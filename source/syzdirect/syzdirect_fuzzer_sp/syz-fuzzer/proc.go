// Copyright 2017 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package main

import (
	"bytes"
	"fmt"
	"math"
	"math/rand"
	"os"

	// "runtime"
	"runtime/debug"
	"strconv"
	"strings"
	"sync"
	"sync/atomic"
	"syscall"
	"time"

	"github.com/google/syzkaller/pkg/cover"
	"github.com/google/syzkaller/pkg/hash"
	"github.com/google/syzkaller/pkg/ipc"
	"github.com/google/syzkaller/pkg/log"
	"github.com/google/syzkaller/pkg/rpctype"
	"github.com/google/syzkaller/pkg/signal"
	"github.com/google/syzkaller/prog"
)

// Proc represents a single fuzzing process (executor).
type Proc struct {
	fuzzer          *Fuzzer
	pid             int
	env             *ipc.Env
	rnd             *rand.Rand
	execOpts        *ipc.ExecOpts
	execOptsCollide *ipc.ExecOpts
	execOptsCover   *ipc.ExecOpts
	execOptsComps   *ipc.ExecOpts
}

func newProc(fuzzer *Fuzzer, pid int) (*Proc, error) {
	env, err := ipc.MakeEnv(fuzzer.config, pid)
	if err != nil {
		return nil, err
	}
	rnd := rand.New(rand.NewSource(time.Now().UnixNano() + int64(pid)*1e12))
	execOptsCollide := *fuzzer.execOpts
	execOptsCollide.Flags &= ^ipc.FlagCollectSignal
	execOptsCover := *fuzzer.execOpts
	execOptsCover.Flags |= ipc.FlagCollectCover
	execOptsComps := *fuzzer.execOpts
	execOptsComps.Flags |= ipc.FlagCollectComps
	proc := &Proc{
		fuzzer:          fuzzer,
		pid:             pid,
		env:             env,
		rnd:             rnd,
		execOpts:        fuzzer.execOpts,
		execOptsCollide: &execOptsCollide,
		execOptsCover:   &execOptsCover,
		execOptsComps:   &execOptsComps,
	}
	return proc, nil
}

func (proc *Proc) loop() {
	generatePeriod := 100
	if proc.fuzzer.config.Flags&ipc.FlagSignal == 0 {
		// If we don't have real coverage signal, generate programs more frequently
		// because fallback signal is weak.
		generatePeriod = 2
	}
	for i := 0; ; i++ {
		item := proc.fuzzer.workQueue.dequeue()
		if item != nil {
			switch item := item.(type) {
			case *WorkTriage:
				proc.triageInput(item)
			case *WorkCandidate:
				item.p.HasTcall(proc.fuzzer.choiceTable)
				proc.execute(proc.execOpts, item.p, item.flags, StatCandidate)
			case *WorkSmash:
				proc.smashInput(item)
			default:
				log.Fatalf("unknown work type: %#v", item)
			}
			continue
		}

		ct := proc.fuzzer.choiceTable
		fuzzerSnapshot := proc.fuzzer.snapshot()
		if len(fuzzerSnapshot.corpus) == 0 || i%generatePeriod == 0 {
			// Generate a new prog.
			p := proc.fuzzer.target.GenerateInGo(proc.rnd, prog.RecommendedCalls, ct)
			log.Logf(1, "#%v: generated", proc.pid)
			proc.executeAndCollide(proc.execOpts, p, ProgNormal, StatGenerate)
		} else {
			// Mutate an existing prog.
			p := fuzzerSnapshot.chooseProgram(proc.rnd, proc.fuzzer.choiceTable).Clone()
			p.Mutate(proc.rnd, prog.RecommendedCalls, ct, fuzzerSnapshot.corpus)
			log.Logf(1, "#%v: mutated", proc.pid)
			proc.executeAndCollide(proc.execOpts, p, ProgNormal, StatFuzz)
		}
	}
}

func (proc *Proc) triageInput(item *WorkTriage) {
	log.Logf(1, "#%v: triaging type=%x", proc.pid, item.flags)

	prio := signalPrio(item.p, &item.info, item.call)
	inputSignal := signal.FromRaw(item.info.Signal, prio)
	newSignal := proc.fuzzer.corpusSignalDiff(inputSignal)
	progDist := item.p.Dist
	callDist := item.info.Dist
	if newSignal.Empty() {
		return
	}
	callName := ".extra"
	logCallName := "extra"
	shouldUpdate := false
	if item.call != -1 {
		callName = item.p.Calls[item.call].Meta.Name
		logCallName = fmt.Sprintf("call #%v %v", item.call, callName)
		if item.p.Calls[item.call] == item.p.Tcall || item.p.Calls[item.call] == item.p.Rcall {
			shouldUpdate = true
		}
	}
	log.Logf(3, "triaging input for %v (new signal=%v)", logCallName, newSignal.Len())
	var inputCover cover.Cover
	const (
		signalRuns       = 3
		minimizeAttempts = 3
	)
	// Compute input coverage and non-flaky signal for minimization.
	notexecuted := 0
	rawCover := []uint32{}
	progHitCounts := make(prog.ProgHitCounts)
	for i := 0; i < signalRuns; i++ {
		info := proc.executeRaw(proc.execOptsCover, item.p, StatTriage)
		if !reexecutionSuccess(info, &item.info, item.call) {
			// The call was not executed or failed.
			notexecuted++
			if notexecuted > signalRuns/2+1 {
				return // if happens too often, give up
			}
			continue
		}
		thisSignal, thisCover, thisDist := getSignalAndCover(item.p, info, item.call)
		if len(rawCover) == 0 && proc.fuzzer.fetchRawCover {
			rawCover = append([]uint32{}, thisCover...)
		}
		newSignal = newSignal.Intersection(thisSignal)
		// Without !minimized check manager starts losing some considerable amount
		// of coverage after each restart. Mechanics of this are not completely clear.
		if newSignal.Empty() && item.flags&ProgMinimized == 0 {
			return
		}
		inputCover.Merge(thisCover)
		if info.MinDist < progDist {
			progDist = info.MinDist
		}
		if thisDist != prog.InvalidDist && thisDist > callDist {
			callDist = thisDist
		}
		for hitIdx, progItem := range info.ProgHitCounts {
			oldItem := progHitCounts[hitIdx]
			oldItem.CallIds = append(progHitCounts[hitIdx].CallIds, progItem.CallIds...)
			progHitCounts[hitIdx] = oldItem
		}
	}
	if item.flags&ProgMinimized == 0 {
		item.p, item.call = prog.Minimize(item.p, item.call, false,
			func(p1 *prog.Prog, call1 int) bool {
				for i := 0; i < minimizeAttempts; i++ {
					info := proc.execute(proc.execOpts, p1, ProgNormal, StatMinimize)
					if !reexecutionSuccess(info, &item.info, call1) {
						// The call was not executed or failed.
						continue
					}
					thisSignal, _, _ := getSignalAndCover(p1, info, call1)
					if newSignal.Intersection(thisSignal).Len() == newSignal.Len() &&
						info.MinDist <= progDist {
						return true
					}
				}
				return false
			})
	}
	if len(progHitCounts) == 0 {
		progHitCounts = nil
	}
	item.p.Dist = progDist
	if progDist != prog.InvalidDist {
		atomic.AddUint64(&proc.fuzzer.extStats[ExtAllDist], uint64(progDist))
		atomic.AddUint64(&proc.fuzzer.extStats[ExtProgCount], 1)
		if shouldUpdate && item.p.Tcall != nil {
			proc.fuzzer.choiceTable.UpdateCallDistance(item.p, callDist)
		}
	}

	data := item.p.Serialize()
	sig := hash.Hash(data)

	tcallId, rcallId := -1, -1
	if shouldUpdate && item.p.Tcall != nil {
		tcallId = item.p.Tcall.Meta.ID
		if item.p.Rcall != nil {
			rcallId = item.p.Rcall.Meta.ID
		}
	}
	feature_id := []string{}
	featureSequence := make([]int, 0, len(item.p.Calls)) // 新增序列存储
	for _, call := range item.p.Calls {
		callId := strconv.Itoa(call.Meta.ID)
		feature_id = append(feature_id, callId)
		featureSequence = append(featureSequence, call.Meta.ID)
	}
	feature := strings.Join(feature_id, ",")
	item.p.Feature = feature
	item.p.FeatureSequence = featureSequence

	// featureDistance := proc.fuzzer.snapshot().featureDistance
	// Seqweight, exists := featureDistance[feature]
	// if !exists {
	// 	// 如果feature不存在，使用一个默认值
	// 	Seqweight = progDist // 或其他合适的默认值
	// }

	log.Logf(2, "added new input for %v to corpus:\n%s", logCallName, data)
	proc.fuzzer.sendInputToManager(rpctype.Input{
		Call:            callName,
		CallID:          item.call,
		Prog:            data,
		Signal:          inputSignal.Serialize(),
		Cover:           inputCover.Serialize(),
		RawCover:        rawCover,
		Dist:            progDist,
		Feature:         feature,
		FeatureSequence: featureSequence,
		TcallId:         tcallId,
		RcallId:         rcallId,
		ProgHitCounts:   progHitCounts,
	})

	proc.fuzzer.addInputToCorpus(item.p, inputSignal, sig)

	if item.flags&ProgSmashed == 0 {
		proc.fuzzer.workQueue.enqueue(&WorkSmash{item.p, item.call})
	}
}

func reexecutionSuccess(info *ipc.ProgInfo, oldInfo *ipc.CallInfo, call int) bool {
	if info == nil || len(info.Calls) == 0 {
		return false
	}
	if call != -1 {
		// Don't minimize calls from successful to unsuccessful.
		// Successful calls are much more valuable.
		if oldInfo.Errno == 0 && info.Calls[call].Errno != 0 {
			return false
		}
		return len(info.Calls[call].Signal) != 0
	}
	return len(info.Extra.Signal) != 0
}

func getSignalAndCover(p *prog.Prog, info *ipc.ProgInfo, call int) (signal.Signal, []uint32, uint32) {
	inf := &info.Extra
	if call != -1 {
		inf = &info.Calls[call]
	}
	return signal.FromRaw(inf.Signal, signalPrio(p, inf, call)), inf.Cover, inf.Dist
}

// 加权LCS计算（带序列长度补偿）
func (p *FeatureProcessor) computeWeightedLCS(a, b []int) uint32 {
	m, n := len(a), len(b)
	dp := make([][]int, m+1)
	for i := range dp {
		dp[i] = make([]int, n+1)
	}

	// 动态规划计算
	for i := 1; i <= m; i++ {
		for j := 1; j <= n; j++ {
			if a[i-1] == b[j-1] {
				dp[i][j] = dp[i-1][j-1] + 1
			} else {
				dp[i][j] = max(dp[i-1][j], dp[i][j-1])
			}
		}
	}
	lcsLength := dp[m][n]
	shorterLen := min(m, n)
	if shorterLen == 0 {
		return 0.0
	}
	return uint32(lcsLength)
}

// // 加权随机选择算法
//
//	func (proc *Proc) weightedRandomSelect(prob []float64, count int) []int {
//		// 采用蓄水池采样算法
//		samples := make([]int, 0, count)
//		for i, p := range prob {
//			if len(samples) < count {
//				samples = append(samples, i)
//			} else {
//				r := rand.Float64()
//				if r < p*float64(count) {
//					samples[rand.Intn(count)] = i
//				}
//			}
//		}
//		return samples
//	}
// type FuzzerSnapshot struct {
// 	corpus          []*prog.Prog
// 	distanceGroup   map[uint32]uint32
// 	distanceFeature map[uint32]map[string]uint32
// 	featureSequence map[string][]int
// }

type FeatureProcessor struct {
	distanceFeature map[uint32]map[string]uint32
	featureSequence map[string][]int
	maxCandidates   int
	rnd             *rand.Rand
	maxDist         uint32
	minDist         uint32
}

// candidate 候选特征结构
type candidate struct {
	dist     uint32
	feature  string
	sequence []int
}

// createTargetSet 创建目标集合
func (p *FeatureProcessor) createTargetSet(seq []int) map[int]struct{} {
	targetSet := make(map[int]struct{}, len(seq))
	for _, v := range seq {
		targetSet[v] = struct{}{}
	}
	return targetSet
}

func (p *FeatureProcessor) calculatefeatureDistances(currentDist uint32) map[string]uint32 {
	featureDistance := make(map[string]uint32)
	for distance, featureMap := range p.distanceFeature {
		if distance == currentDist {
			continue
		}
		for feature := range featureMap {
			if distance < featureDistance[feature] {
				featureDistance[feature] = distance
			}
		}
	}
	return featureDistance
}

// processSingleFeature 处理单个特征
func (p *FeatureProcessor) processSingleFeature(
	feature string,
	dist uint32,
	targetSeq []int,
	targetSet map[int]struct{},
	candidateChan chan<- candidate,
	pool *sync.Pool,
) error {
	canseq := p.featureSequence[feature]
	if len(canseq) < len(targetSeq)/2 || len(canseq) > len(targetSeq)*2 {
		return nil
	}

	// 快速交集计算
	common := 0
	for _, v := range canseq {
		if _, exists := targetSet[v]; exists {
			common++
			if common >= len(targetSeq)/2 {
				c := pool.Get().(*candidate)
				c.dist = dist
				c.feature = feature
				c.sequence = canseq
				select {
				case candidateChan <- *c:
				default:
				}
				pool.Put(c)
				return nil
			}
		}
	}
	return nil
}

func (p *FeatureProcessor) processCandidates(
	featureDistance map[string]uint32,
	targetSeq []int,
	targetSet map[int]struct{},
) ([]candidate, error) {
	candidateChan := make(chan candidate, p.maxCandidates*2)
	var wg sync.WaitGroup

	// 使用对象池复用对象
	candidatePool := sync.Pool{
		New: func() interface{} {
			return &candidate{}
		},
	}

	// 使用普通 goroutine 替代 errgroup
	for feature, dist := range featureDistance {
		wg.Add(1)
		go func(feature string, dist uint32) {
			defer wg.Done()

			canseq := p.featureSequence[feature]
			if len(canseq) < len(targetSeq)/2 || len(canseq) > len(targetSeq)*2 {
				return
			}

			// 快速交集计算
			common := 0
			for _, v := range canseq {
				if _, exists := targetSet[v]; exists {
					common++
					if common >= len(targetSeq)/2 {
						c := candidatePool.Get().(*candidate)
						c.dist = dist
						c.feature = feature
						c.sequence = canseq
						select {
						case candidateChan <- *c:
						default:
						}
						candidatePool.Put(c)
						return
					}
				}
			}
		}(feature, dist)
	}

	// 等待所有goroutine完成
	go func() {
		wg.Wait()
		close(candidateChan)
	}()

	// 收集结果
	candidates := make([]candidate, 0, p.maxCandidates)
	for c := range candidateChan {
		if len(candidates) < p.maxCandidates {
			candidates = append(candidates, c)
		} else {
			// 使用水库抽样
			if p.rnd.Float32() < float32(p.maxCandidates)/float32(len(candidates)+1) {
				replaceIdx := p.rnd.Intn(p.maxCandidates)
				candidates[replaceIdx] = c
			}
		}
	}

	return candidates, nil
}

// calculateFinalWeight 计算最终权重
func (p *FeatureProcessor) calculateFinalWeight(
	candidates []candidate,
	targetSeq []int,
	featureDistance map[string]uint32,
) uint32 {
	var (
		simCount           uint32
		simFeatureDistance uint32
		weightLock         sync.Mutex
	)

	// weights := make([]uint32, len(candidates))
	var lcsWg sync.WaitGroup

	for i := range candidates {
		i := i // 创建副本
		lcsWg.Add(1)
		go func() {
			defer lcsWg.Done()
			cand := candidates[i]
			lcsLen := p.computeWeightedLCS(targetSeq, cand.sequence)
			similarity := (lcsLen/uint32(len(cand.sequence)) +
				lcsLen/uint32(len(targetSeq))) / 2
			weight := featureDistance[cand.feature] / similarity
			// weights[i] = weight

			weightLock.Lock()
			simCount++
			if simFeatureDistance < weight {
				simFeatureDistance = weight
			}
			weightLock.Unlock()
		}()
	}

	lcsWg.Wait()
	// if p.maxDist != p.minDist && simCount > 0 {
	// 	simFeatureDistance = simFeatureDistance / float64(p.maxDist-p.minDist)
	// }

	return simFeatureDistance
}

func NewFeatureProcessor(distanceFeature map[uint32]map[string]uint32, featureSequence map[string][]int, rnd *rand.Rand) *FeatureProcessor {
	return &FeatureProcessor{
		distanceFeature: distanceFeature,
		featureSequence: featureSequence,
		maxCandidates:   len(featureSequence) / 10,
		rnd:             rnd,
	}
}
func (p *FeatureProcessor) ProcessFeatures(item *WorkSmash) uint32 {
	if len(p.featureSequence) <= 100 {
		return 0
	}

	// 1. 计算特征权重
	featureDistance := p.calculatefeatureDistances(item.p.Dist)

	// 2. 获取目标序列
	targetSeq := item.p.FeatureSequence
	targetSet := p.createTargetSet(targetSeq)

	// 3. 并行处理候选特征
	candidates, err := p.processCandidates(featureDistance, targetSeq, targetSet)
	if err != nil {
		return 0
	}
	// 4. 计算最终权重
	return p.calculateFinalWeight(candidates, targetSeq, featureDistance)
}
func (proc *Proc) smashInput(item *WorkSmash) {
	if proc.fuzzer.faultInjectionEnabled && item.call != -1 {
		proc.failCall(item.p, item.call)
	}
	if proc.fuzzer.comparisonTracingEnabled && item.call != -1 {
		proc.executeHintSeed(item.p, item.call)
	}
	maxDist, minDist := proc.fuzzer.readExtremeDist()
	// pull := 1
	// featureCount := proc.fuzzer.distanceFeature[item.p.Dist]
	// var distfeatureMax uint32
	// var sumcount uint32
	var com_count uint32
	var sim_count uint32
	var simFeatureDistance uint32
	var distfeatureMax uint32
	for dist, featureMap := range proc.fuzzer.distanceFeature {
		// distfeatureMax = maxDist - item.p.Dist
		if dist == item.p.Dist {
			continue // 排除相同距离
		}
		if _, exists := featureMap[item.p.Feature]; exists {
			if distfeatureMax < maxDist-dist {
				distfeatureMax = maxDist - dist
			}
			com_count += 1
		}
	}
	// sumcount += com_count
	if com_count == 0 && len(proc.fuzzer.featureSequence) > 100 {
		processor := NewFeatureProcessor(proc.fuzzer.distanceFeature, proc.fuzzer.featureSequence, proc.rnd)
		simFeatureDistance = processor.ProcessFeatures(item)
		// if err != nil {
		//     // continue
		// }
	}
	mutateNum := 100
	if minDist != prog.InvalidDist && item.p.Dist != prog.InvalidDist {
		normalized_d := 0.0
		featureDistance := 0.0
		if maxDist != minDist {
			if com_count > 0 {
				featureDistance = float64(distfeatureMax) / float64(maxDist-minDist)
			} else if sim_count > 0 {
				featureDistance = float64(maxDist-simFeatureDistance) / float64(maxDist-minDist)
			}
			distanceWeight := float64(maxDist-item.p.Dist) / float64(maxDist-minDist)
			normalized_d = (featureDistance + distanceWeight) / 2
		}
		power_factor := math.Pow(16, normalized_d)
		mutateNum = int(power_factor*9.375 + 50.0)
	}
	fuzzerSnapshot := proc.fuzzer.snapshot()
	for i := 0; i < mutateNum; i++ {
		p := item.p.Clone()
		p.Mutate(proc.rnd, prog.RecommendedCalls, proc.fuzzer.choiceTable, fuzzerSnapshot.corpus)
		log.Logf(1, "#%v: smash mutated", proc.pid)
		proc.executeAndCollide(proc.execOpts, p, ProgNormal, StatSmash)
	}
}

func (proc *Proc) failCall(p *prog.Prog, call int) {
	for nth := 1; nth <= 100; nth++ {
		log.Logf(1, "#%v: injecting fault into call %v/%v", proc.pid, call, nth)
		newProg := p.Clone()
		newProg.Calls[call].Props.FailNth = nth
		info := proc.executeRaw(proc.execOpts, newProg, StatFISmash)
		if info != nil && len(info.Calls) > call && info.Calls[call].Flags&ipc.CallFaultInjected == 0 {
			break
		}
	}
}

func (proc *Proc) executeHintSeed(p *prog.Prog, call int) {
	log.Logf(1, "#%v: collecting comparisons", proc.pid)
	// First execute the original program to dump comparisons from KCOV.
	info := proc.execute(proc.execOptsComps, p, ProgNormal, StatSeed)
	if info == nil {
		return
	}

	// Then mutate the initial program for every match between
	// a syscall argument and a comparison operand.
	// Execute each of such mutants to check if it gives new coverage.
	atomic.AddUint64(&proc.fuzzer.extStats[ExtHintCompsCount], 1)
	atomic.AddUint64(&proc.fuzzer.extStats[ExtHintCompsSum], uint64(len(info.Calls[call].Comps)))
	i := 0
	maxNum := 200
	p.MutateWithHints(call, info.Calls[call].Comps, func(p *prog.Prog) {
		if i < maxNum {
			log.Logf(1, "#%v: executing comparison hint", proc.pid)
			proc.execute(proc.execOpts, p, ProgNormal, StatHint)
		} else {
			log.Logf(1, "#%v: ignore executing comparison hint", proc.pid)
		}
		i += 1
	})
}

func (proc *Proc) execute(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) *ipc.ProgInfo {
	info := proc.executeRaw(execOpts, p, stat)
	if info == nil {
		return nil
	}
	p.Dist = info.MinDist
	if p.Dist != prog.InvalidDist && p.Dist > prog.MaxDist {
		log.Fatalf("prog dist %v higher than max dist %v", p.Dist, prog.MaxDist)
		panic("max dist should improve")
	}
	calls, extra := proc.fuzzer.checkNewSignal(p, info)
	for _, callIndex := range calls {
		proc.enqueueCallTriage(p, flags, callIndex, info.Calls[callIndex])
	}
	if extra {
		proc.enqueueCallTriage(p, flags, -1, info.Extra)
	}
	proc.fuzzer.callStatsMu.Lock()
	if p.Tcall != nil {
		proc.fuzzer.callStats[p.Tcall.Meta.Name] += 1
	}
	proc.fuzzer.callStatsMu.Unlock()
	return info
}

func (proc *Proc) enqueueCallTriage(p *prog.Prog, flags ProgTypes, callIndex int, info ipc.CallInfo) {
	// info.Signal points to the output shmem region, detach it before queueing.
	info.Signal = append([]uint32{}, info.Signal...)
	// None of the caller use Cover, so just nil it instead of detaching.
	// Note: triage input uses executeRaw to get coverage.
	info.Cover = nil
	proc.fuzzer.workQueue.enqueue(&WorkTriage{
		p:     p.Clone(),
		call:  callIndex,
		info:  info,
		flags: flags,
	})
}

func (proc *Proc) executeAndCollide(execOpts *ipc.ExecOpts, p *prog.Prog, flags ProgTypes, stat Stat) {
	proc.execute(execOpts, p, flags, stat)

	if proc.execOptsCollide.Flags&ipc.FlagThreaded == 0 {
		// We cannot collide syscalls without being in the threaded mode.
		return
	}
	const collideIterations = 2
	for i := 0; i < collideIterations; i++ {
		proc.executeRaw(proc.execOptsCollide, proc.randomCollide(p), StatCollide)
	}
}

func (proc *Proc) randomCollide(origP *prog.Prog) *prog.Prog {
	// Old-styl collide with a 33% probability.
	if proc.rnd.Intn(3) == 0 {
		p, err := prog.DoubleExecCollide(origP, proc.rnd)
		if err == nil {
			return p
		}
	}
	p := prog.AssignRandomAsync(origP, proc.rnd)
	if proc.rnd.Intn(2) != 0 {
		prog.AssignRandomRerun(p, proc.rnd)
	}
	return p
}

func (proc *Proc) executeRaw(opts *ipc.ExecOpts, p *prog.Prog, stat Stat) *ipc.ProgInfo {
	proc.fuzzer.checkDisabledCalls(p)

	// Limit concurrency window and do leak checking once in a while.
	ticket := proc.fuzzer.gate.Enter()
	defer proc.fuzzer.gate.Leave(ticket)

	proc.logProgram(opts, p)
	for try := 0; ; try++ {
		atomic.AddUint64(&proc.fuzzer.stats[stat], 1)
		output, info, hanged, err := proc.env.Exec(opts, p)
		if err != nil {
			if err == prog.ErrExecBufferTooSmall {
				// It's bad if we systematically fail to serialize programs,
				// but so far we don't have a better handling than ignoring this.
				// This error is observed a lot on the seeded syz_mount_image calls.
				return nil
			}
			if try > 10 {
				log.Fatalf("executor %v failed %v times: %v", proc.pid, try, err)
			}
			log.Logf(4, "fuzzer detected executor failure='%v', retrying #%d", err, try+1)
			debug.FreeOSMemory()
			time.Sleep(time.Second)
			continue
		}
		log.Logf(2, "result hanged=%v: %s", hanged, output)
		proc.fuzzer.handleHitCount(info.ProgHitCounts, p)
		return info
	}
}

func (proc *Proc) logProgram(opts *ipc.ExecOpts, p *prog.Prog) {
	if proc.fuzzer.outputType == OutputNone {
		return
	}

	data := p.Serialize()

	// The following output helps to understand what program crashed kernel.
	// It must not be intermixed.
	switch proc.fuzzer.outputType {
	case OutputStdout:
		now := time.Now()
		proc.fuzzer.logMu.Lock()
		fmt.Printf("%02v:%02v:%02v executing program %v:\n%s\n",
			now.Hour(), now.Minute(), now.Second(),
			proc.pid, data)
		proc.fuzzer.logMu.Unlock()
	case OutputDmesg:
		fd, err := syscall.Open("/dev/kmsg", syscall.O_WRONLY, 0)
		if err == nil {
			buf := new(bytes.Buffer)
			fmt.Fprintf(buf, "syzkaller: executing program %v:\n%s\n",
				proc.pid, data)
			syscall.Write(fd, buf.Bytes())
			syscall.Close(fd)
		}
	case OutputFile:
		f, err := os.Create(fmt.Sprintf("%v-%v.prog", proc.fuzzer.name, proc.pid))
		if err == nil {
			f.Write(data)
			f.Close()
		}
	default:
		log.Fatalf("unknown output type: %v", proc.fuzzer.outputType)
	}
}
