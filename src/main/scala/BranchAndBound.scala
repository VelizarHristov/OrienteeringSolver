package main

import collection.immutable.Queue
import collection.mutable

// TODO: should not crash with small problem sizes (should give the same output as brute force)
object BranchAndBound:
    opaque type BitSet = Long

    object BitSet:
        def apply(): BitSet = 0L
        extension(set: BitSet)
            def add(i: Int): BitSet = set + (1L << i)
            def contains(i: Int) = (set & (1L << i)) != 0
            def safeAdd(i: Int): BitSet = if !contains(i) then add(i) else set
            def -(that: BitSet): BitSet = set - that

    case class State(
        visited: BitSet,
        lastEffLen: Double,
        remaining: Int,
        score: Double,
        maxed: BitSet,
        visitedSeq: List[Int],
        bestBonus: Double,
        bestBonusLen: Int
    ):
        inline def lastOpt = visitedSeq.headOption
        var heuristic: Option[Double] = None

        var mostRemovable: Option[(flatLoss: Double, efficiency: Double, len: Int)] = None
        var mostAddable: Option[(efficiency: Double, maxLen: Int, addableLen: Int)] = None

        // TODO: tighten this by turning mostRemovable and mostAddable into sorted lists and comparing them more thoroughly

        def isInconsistent =
            val failures = for
                (flatLoss, lossPerLen, removableLen) <- mostRemovable
                (gainPerLen, maxLen, addableLen) <- mostAddable
            yield
                if removableLen >= addableLen then
                    val loss = flatLoss + lossPerLen * addableLen
                    val gain = gainPerLen * (addableLen + maxLen * MAX_INTERVAL_BONUS)
                    gain > loss
                else
                    val loss = flatLoss + lossPerLen * removableLen
                    val gain = gainPerLen * removableLen
                    gain > loss
            failures.contains(true)

    def solve(
        intervals: Array[Interval],
        adjBonuses: Array[Array[Double]],
        target: Int,
        MAX_INTERVAL_BONUS: Double,
        LAST_ADJ_MULT: Double
    ) = BranchAndBound(intervals, adjBonuses, target, MAX_INTERVAL_BONUS, LAST_ADJ_MULT).solve()

class BranchAndBound(
    intervals: Array[Interval],
    adjBonuses: Array[Array[Double]],
    target: Int,
    MAX_INTERVAL_BONUS: Double,
    LAST_ADJ_MULT: Double
):
    import BranchAndBound._
    import BranchAndBound.BitSet._

    require(intervals.size < 64, "error: our BitSet can only fit 64 bits")
    var heurCalls = 0
    var debug = false
    def dprintln(s: String) = if debug then println(s)

    val adjBonusForLast = adjBonuses.zipWithIndex.map(
        (arr, i) => arr.sum - arr(i)
    ).sum / (intervals.length * (intervals.length - 1)) * LAST_ADJ_MULT

    val bestForPair = (
        for {
            i <- intervals.indices
            j <- intervals.indices
            adjBonus = if i == j then adjBonusForLast else adjBonuses(i)(j)
            efficiency = (intervals(i).relevance + adjBonus) * (1 + MAX_INTERVAL_BONUS)
        } yield (i, j, efficiency)
    ).toArray.sortBy(-_._3)
    val bestForPairNoAdjBonus = (
        for {
            i <- intervals.indices
            j <- intervals.indices
            if i != j
            efficiency = (intervals(i).relevance + adjBonuses(i)(j)) * (1 + MAX_INTERVAL_BONUS)
        } yield (i, j, efficiency)
    ).toArray.sortBy(-_._3)
    val bestBonuses = adjBonuses.map: arr =>
        arr.indices.map(j => (j, arr(j))).sortBy(-_._2).toArray
    def heuristicCalc(state: State, requiredToPick: List[Int] = List()) =
        var visited = state.visited
        var remaining = state.remaining
        var estScore = state.score
        var usedEdges: BitSet = BitSet()
        var maxLastBonus = Double.MinValue
        requiredToPick.foreach: i =>
            remaining -= intervals(i).from
            val bestBonus = bestBonuses(i).find(x => !visited.contains(x._1))
            val bestBonusValue = bestBonus.map(_._2).getOrElse(0.0)
            val effLen = intervals(i).from * (1 + MAX_INTERVAL_BONUS)
            estScore += effLen * (intervals(i).relevance + bestBonusValue)
            bestBonus.foreach: bonus =>
                usedEdges = usedEdges.safeAdd(bonus._1)
            maxLastBonus = maxLastBonus max (effLen * (adjBonusForLast - bestBonusValue))
        state.lastOpt.foreach: last =>
            val bestBonus = bestBonuses(last).find(x => !visited.contains(x._1))
            val bestBonusForLast = bestBonus.map(_._2).getOrElse(0.0)
            estScore += state.lastEffLen * (bestBonusForLast - adjBonusForLast)
            bestBonus.foreach: bonus =>
                usedEdges = usedEdges.safeAdd(bonus._1)
            if remaining <= state.bestBonusLen then
                maxLastBonus = maxLastBonus max (state.lastEffLen * (adjBonusForLast - bestBonusForLast))
        var skipped = 0
        var usedBestBonusLen = false
        var includedStack = List[(Int, Double)]()
        while (remaining != 0 && skipped < bestForPairNoAdjBonus.length)
            val (i, j, efficiency) = bestForPairNoAdjBonus(skipped)
            if efficiency < state.bestBonus && !usedBestBonusLen then
                val lenToUse = state.bestBonusLen min remaining
                estScore += lenToUse * state.bestBonus
                remaining -= lenToUse
                usedBestBonusLen = true
                includedStack = (lenToUse, state.bestBonus) :: includedStack
            else
                if !visited.contains(i) && !state.visited.contains(j) then
                    val len = if requiredToPick.contains(i) then intervals(i).choiceLen else intervals(i).to
                    val lenToUse = len min remaining
                    estScore += lenToUse * efficiency
                    remaining -= lenToUse
                    visited = visited.add(i)
                    usedEdges = usedEdges.safeAdd(j)
                    // TODO: now requiredToPick is broken!
                    maxLastBonus = maxLastBonus max (lenToUse * (adjBonusForLast - adjBonuses(i)(j)) * (1 + MAX_INTERVAL_BONUS))
                    includedStack = (lenToUse, efficiency) :: includedStack
                skipped += 1
        if includedStack.nonEmpty then
            val remainingNodes = intervals.indices.view.map(i => {
                (i, (intervals(i).relevance + adjBonusForLast) * (1 + MAX_INTERVAL_BONUS), intervals(i).to)
            }).filter(
                (i, eff, _) => !visited.contains(i) && eff > includedStack.head._2
            ).toVector.sortBy(_._3)
            var lenLowerBound = 0
            var lenUpperBound = 0
            var lenIntervalEff = 0.0
            var lostSoFar = 0.0
            var next = 0
            var stop = false
            while (!stop && next < remainingNodes.length)
                val (_, eff, len) = remainingNodes(next)
                while (len > lenUpperBound && !stop)
                    includedStack match
                        case (nodeLen, nodeEff) :: nextStack =>
                            lostSoFar += (lenUpperBound - lenLowerBound) * lenIntervalEff
                            lenLowerBound = lenUpperBound
                            lenUpperBound += nodeLen
                            lenIntervalEff = nodeEff
                            includedStack = nextStack
                        case Nil =>
                            stop = true
                if !stop then
                    val gain = eff * len
                    val loss = lostSoFar + (len - lenLowerBound) * lenIntervalEff
                    maxLastBonus = maxLastBonus max (gain - loss)
                    next += 1
        estScore += maxLastBonus
        (estScore, visited - state.visited, usedEdges)

    def heuristicCalcOld(state: State, requiredToPick: List[Int] = List()) =
        var visited = state.visited
        var remaining = state.remaining
        var estScore = state.score
        var usedEdges = BitSet()
        requiredToPick.foreach: i =>
            remaining -= intervals(i).from
            val bestBonus = bestBonuses(i).find(x => !visited.contains(x._1))
            val bestBonusValue = bestBonus.map(_._2).getOrElse(adjBonusForLast)
            val effLen = intervals(i).from * (1 + MAX_INTERVAL_BONUS)
            estScore += effLen * (intervals(i).relevance + bestBonusValue)
            bestBonus.foreach: bonus =>
                usedEdges = usedEdges.safeAdd(bonus._1)
        state.lastOpt.foreach: last =>
            val bestBonus = bestBonuses(last).find(x => !visited.contains(x._1))
            val bestBonusForLast = bestBonus.map(_._2).getOrElse(adjBonusForLast)
            estScore += state.lastEffLen * (bestBonusForLast - adjBonusForLast)
            bestBonus.foreach: bonus =>
                usedEdges = usedEdges.safeAdd(bonus._1)
        var skipped = 0
        var usedBestBonusLen = false
        while (remaining != 0 && skipped < bestForPair.length)
            val (i, j, efficiency) = bestForPair(skipped)
            if efficiency < state.bestBonus && !usedBestBonusLen then
                val lenToUse = state.bestBonusLen min remaining
                estScore += lenToUse * state.bestBonus
                remaining -= lenToUse
                usedBestBonusLen = true
            else
                if !visited.contains(i) && !state.visited.contains(j) then
                    val len = if requiredToPick.contains(i) then intervals(i).choiceLen else intervals(i).to
                    val lenToUse = len min remaining
                    estScore += lenToUse * efficiency
                    remaining -= lenToUse
                    if (lenToUse == len) // for usedNodes calculation
                        visited = visited.add(i)
                    usedEdges = usedEdges.safeAdd(j)
                skipped += 1
        (estScore, visited - state.visited, usedEdges)

    def heuristic1(state: State) = heuristicCalcOld(state)._1
    def heuristic3(state: State) = heuristicCalc(state)._1

    def heuristic4(state: State) =
        var remaining = state.remaining
        var estScore = state.score
        val toAdd = intervals.indices
            .filterNot(state.visited.contains)
            .map: i =>
                val bonus = bestBonuses(i).find(b =>
                    !state.visited.contains(b._1)
                ).get._2.max(adjBonusForLast) + intervals(i).relevance
                (bonus * (1 + MAX_INTERVAL_BONUS), intervals(i).to, i, bestBonuses(i).find(b =>
                    !state.visited.contains(b._1)
                ).get._1)
        val q = mutable.PriorityQueue(toAdd *)(using (a, b) => a._1.compare(b._1))
        state.lastOpt.foreach: last =>
            val bestBonus = bestBonuses(last).find(x => !state.visited.contains(x._1))
            val bestBonusForLast = bestBonus.map(_._2).getOrElse(adjBonusForLast)
            estScore += state.lastEffLen * (bestBonusForLast - adjBonusForLast)
        var usedBestBonusLen = false
        while (remaining != 0 && q.nonEmpty)
            val (efficiency, len, i, j) = q.head
            if efficiency < state.bestBonus && !usedBestBonusLen then
                val lenToUse = state.bestBonusLen min remaining
                estScore += lenToUse * state.bestBonus
                remaining -= lenToUse
                usedBestBonusLen = true
            else
                val lenToUse = len min remaining
                estScore += lenToUse * efficiency
                remaining -= lenToUse
                q.dequeue()
        estScore

    val HEURISTIC_DEPTH = 7
    def heuristic2(initialState: State) =
        def includeOrExclude(state: State, included: List[Int], depth: Int): Double =
            val (heuristicScore, usedIndices, usedEdges) = heuristicCalcOld(state, included)
            intervals.indices.find(i => usedEdges.contains(i) && !usedIndices.contains(i) && !included.contains(i) && intervals(i).from <= state.remaining) match
                case Some(idx) =>
                    val excludedState = state.copy(visited = state.visited.add(idx))
                    if depth == 0 then
                        val includedScore = heuristicCalcOld(state, idx :: included)._1
                        val excludedScore = heuristicCalcOld(excludedState, included)._1
                        includedScore max excludedScore
                    else
                        val includedScore = includeOrExclude(state, idx :: included, depth - 1)
                        val excludedScore = includeOrExclude(excludedState, included, depth - 1)
                        includedScore max excludedScore
                case None => heuristicScore
        includeOrExclude(initialState, List(), HEURISTIC_DEPTH)

    val bestEffPrecalc = adjBonuses.zipWithIndex.map: (arr, i) =>
        val bonusesForI = arr.indices.map(j => (j, arr(j))) :+ (-1, adjBonusForLast)
        bonusesForI.map((j, bonus) =>
            (j, (intervals(i).relevance + bonus) * (1 + MAX_INTERVAL_BONUS))
        ).sortBy(-_._2).toArray
    // TODO: investigate different behaviour from heuristic2 - it should always return the same output.
    def heuristic2Faster(state: State) =
        // val bestEffPerNode0 = bestEffPrecalc.map: arr =>
        //     arr.filter((j, _) => !state.visited.contains(j))
        val bestEffPerNode = bestEffPrecalc.zipWithIndex.map: (arr, i) =>
            val newArr = arr.filter((j, _) => !state.visited.contains(j))
            if state.lastOpt.contains(i) then
                val lastEl = newArr.find(_._1 == -1).get
                newArr.filter(_._1 != -1) :+ lastEl
            else
                newArr

        val initialNextIndices = Array.fill(intervals.length)(0) // TODO: this used to be 1 to skip the adjBonusForLast presumably
        val notVisited = intervals.indices.filterNot(state.visited.contains)
        val forQueue = notVisited.map: i =>
            val (j, eff) = bestEffPerNode(i).head
            (i, j, eff)
        val initialNext = mutable.PriorityQueue(forQueue *)(using (a, b) => a._3.compare(b._3))
        initialNext.enqueue((-1, -1, state.bestBonus))

        case class HeuristicState(
            nextIndices: Array[Int],
            next: mutable.PriorityQueue[(Int, Int, Double)],
            // TODO: (minor) use BitSet instead of Set[Int]
            edgesInPermaIncluded: Map[Int, Set[Int]],
            included: List[(Int, Int, Double)], // sorted starting from least efficient
            reducedLengths: Map[Int, Int],
            excluded: BitSet,
            remaining: Int,
            estScore: Double,
        ):
            lazy val finalEstScore = next.headOption match
                case Some((i, j, efficiency)) =>
                    val len = reducedLengths.get(i).getOrElse(intervals(i).to)
                    if excluded.contains(j) || remaining > len then
                        throw new IllegalStateException("This should never happen - we have a bug | " + excluded.contains(j))
                    else
                        estScore + efficiency * remaining
                case None => estScore

        var initEdgesInPermaIncluded = (-1 +: notVisited).map(_ -> Set[Int]()).toMap
        var initEstScore = state.score
        // TODO: for some reason, here we have an excess score of `adjBonusForLast` after we remove the last node's score - should be 0.0
        state.lastOpt.foreach: last =>
            // remove MAX_INTERVAL_BONUS from last
            bestEffPerNode(last) = bestEffPerNode(last).map: (i, eff) =>
                (i, eff / (1 + MAX_INTERVAL_BONUS))
            bestEffPerNode(last).headOption.foreach: (toNodeIdx, eff) =>
                initEstScore -= state.lastEffLen * (intervals(last).relevance + adjBonusForLast)
                initEstScore += state.lastEffLen * eff
                initEdgesInPermaIncluded = initEdgesInPermaIncluded.updated(toNodeIdx, Set(last))
        val initialHState = HeuristicState(initialNextIndices, initialNext,
            initEdgesInPermaIncluded, List(), Map(-1 -> state.bestBonusLen), BitSet(),
            state.remaining, initEstScore)

        def fillCapacity(hState: HeuristicState) =
            val nextIndices = hState.nextIndices.clone()
            val next = hState.next.clone()
            var included = hState.included
            var estScore = hState.estScore
            var remaining = hState.remaining
            var stop = false
            while (!stop && next.nonEmpty)
                val nextInQueue@(i, j, efficiency) = next.dequeue()
                if !hState.excluded.contains(i) && !hState.excluded.contains(j) then
                    val len = hState.reducedLengths.get(i).getOrElse(intervals(i).to)
                    if remaining < len then
                        stop = true
                        next.enqueue(nextInQueue)
                    else
                        estScore += len * efficiency
                        remaining -= len
                        included = (i, j, efficiency) :: included
                else if !hState.excluded.contains(i) && i != -1 then
                    val (nextJ, nextEff) = bestEffPerNode(i)(nextIndices(i))
                    next.enqueue((i, nextJ, nextEff))
                // TODO (style): the next line is probably correct, but might be refactor-able
                if !stop && i != -1 && j != -1 && bestEffPerNode(i)(nextIndices(i))._1 == j then
                    nextIndices(i) += 1
            HeuristicState(nextIndices, next, hState.edgesInPermaIncluded,
                included, hState.reducedLengths, hState.excluded, remaining, estScore)
        
        inline def updateAndGetNext(excluded: BitSet, nextIndices: Array[Int], idx: Int) =
            while (excluded.contains(bestEffPerNode(idx)(nextIndices(idx))._1))
                nextIndices(idx) += 1
            bestEffPerNode(idx)(nextIndices(idx))

        val startHState = fillCapacity(initialHState)
        def includeOrExcludeFaster(hState: HeuristicState, depth: Int): Double =
            // (TODO) enhancements that might diverge from the slower version of this heuristic:
            //     TODO: instead of picking an arbitrary edge, pick the one which would worsen estScore the most
            //         TODO (speedup): reuse computation between different edges under consideration
            //         TODO (simplicity): check if doing this lets us get rid of edgesInPermaIncluded
            //     TODO: force-included nodes should be unable to use adjBonusForLast
            //         TODO: it should be impossible to include/exclude everything, because at least one node should be able to use adjBonusForLast
            val includedIndices = hState.included.map(_._1).toSet
            val edgesInIncluded = hState.included.map(_._2).toSet
            val totalIncludedLen = hState.reducedLengths.keys.map(i =>
                if (i == -1)
                    0
                else
                    intervals(i).from
            ).sum
            // TODO (minor performance): the above two statements can be made much faster, but check whether their performances matters anyway
            val nextEdge = intervals.indices.find: i =>
                (edgesInIncluded.contains(i) ||
                    hState.edgesInPermaIncluded.get(i).exists(_.nonEmpty) ||
                    (hState.next.headOption.map(_._2).contains(i) && hState.remaining > 0)
                ) &&
                !includedIndices.contains(i) &&
                !hState.reducedLengths.contains(i) &&
                !hState.excluded.contains(i) &&
                intervals(i).from <= state.remaining - totalIncludedLen
            nextEdge match
                case Some(idx) =>
                    val includedState =
                        val nextIndices = hState.nextIndices.clone()
                        val (nextDst, nextEff) = updateAndGetNext(hState.excluded, nextIndices, idx)
                        val edgesInPermaIncluded = hState.edgesInPermaIncluded
                            .removed(idx)
                            .updatedWith(nextDst)(_.map(_ + idx))
                        val reducedLengths = hState.reducedLengths.updated(idx, intervals(idx).choiceLen)
                        var included = hState.included
                        val next = hState.next.clone()
                        var remaining = hState.remaining - intervals(idx).from
                        var estScore = hState.estScore + intervals(idx).from * nextEff
                        while (remaining < 0)
                            val (idxToRemove, edgeToRemove, eff) = included.head
                            included = included.tail
                            val len = reducedLengths.get(idxToRemove).getOrElse(intervals(idxToRemove).to)
                            estScore -= eff * len
                            remaining += len
                            next.enqueue((idxToRemove, edgeToRemove, eff))

                        val nextState = HeuristicState(nextIndices, next, edgesInPermaIncluded, included,
                            reducedLengths, hState.excluded, remaining, estScore)
                        fillCapacity(nextState)

                    val excludedState =
                        val next = hState.next.clone()
                        val nextIndices = hState.nextIndices.clone()
                        val excluded = hState.excluded.add(idx)
                        var estScore = hState.estScore
                        var edgesInPermaIncluded = hState.edgesInPermaIncluded
                        edgesInPermaIncluded(idx).foreach: i =>
                            val oldEff = bestEffPerNode(i)(nextIndices(i))._2
                            val (newEdge, newEff) = updateAndGetNext(excluded, nextIndices, i)
                            val len = if state.lastOpt.contains(i) then state.lastEffLen else intervals(i).from.toDouble
                            estScore -= len * (oldEff - newEff)
                            edgesInPermaIncluded = edgesInPermaIncluded.updatedWith(newEdge)(_.map(_ + i))
                        edgesInPermaIncluded = edgesInPermaIncluded.removed(idx)
                        var remaining = hState.remaining
                        hState.included.foreach: (i, j, eff) =>
                            val len = hState.reducedLengths.get(i).getOrElse(intervals(i).to)
                            remaining += len
                            estScore -= len * eff
                            next.enqueue((i, j, eff))
                        val updState = HeuristicState(nextIndices, next, edgesInPermaIncluded,
                            List(), hState.reducedLengths, excluded, remaining, estScore)
                        fillCapacity(updState)

                    if depth == 0 then
                        includedState.finalEstScore max excludedState.finalEstScore
                    else
                        val includedScore = includeOrExcludeFaster(includedState, depth - 1)
                        val excludedScore = includeOrExcludeFaster(excludedState, depth - 1)
                        includedScore max excludedScore
                case None => hState.finalEstScore
        includeOrExcludeFaster(startHState, HEURISTIC_DEPTH)

    // TODO: try having a constraint on each `j` (edge-destination) appearing only once, rather than potentially giving adj bonus to multiple; or compromise variant: spanning tree/arborescence, if that's at all possible
    // TODO: try having only one adjBonusForLast
    inline def whichHeuristic(state: State) = heuristic2(state)
    // inline def whichHeuristic = heuristic1
    inline def heuristic(state: State) = state.heuristic.getOrElse({
        heurCalls += 1
        val h = whichHeuristic(state)
        // val h2 = heuristic2(state)
        // val h2f = heuristic2Faster(state)
        // if ((h2 - h2f).abs > 0.00001) {
        //     println("ARG START")
        //     println((h2, h2f))
        //     println(state)
        //     println()
        //     System.exit(0)
        // }
        state.heuristic = Some(h)
        h
    })

    def solve() =
        heurCalls = 0
        val startState = State(BitSet(), -1, target, 0.0, BitSet(), List[Int](), 0.0, 0)
        val fringe = mutable.PriorityQueue(startState)(
            using (a, b) => heuristic(a).compare(heuristic(b))
        )
        val bestVisited = mutable.Map[(BitSet, Int, Double, Int), Double]().withDefaultValue(Double.MinValue)
        var bestScore = Double.MinValue
        var bestSolution: Option[State] = None
        while (fringe.nonEmpty && heuristic(fringe.head) > bestScore)
            if heurCalls % 2000 == 0 then
                println((fringe.size, fringe.head.score, bestScore))
            val state@State(visited, lastEffLen, remaining, score, maxed, visitedSeq, bestBonus, bestBonusLen) = fringe.dequeue()
            if remaining < bestBonusLen then
                val finalScore = score + bestBonus * remaining
                if finalScore > bestScore then
                    bestScore = finalScore
                    bestSolution = Some(state)
            val nextStates = for
                nextIdx <- intervals.indices
                // TODO: incorrect - sometimes prunes a state leading to the optimal state
                if !state.isInconsistent
                if !visited.contains(nextIdx)
                next@Interval(from, to, relevance) = intervals(nextIdx)
                takeMax <- Seq(false, true)
                nextRemaining = remaining - (if takeMax then to else from)
                if nextRemaining >= 0
                effectiveLength = if takeMax then next.toWithBonus else from.toDouble
                adjBonus = state.lastOpt.map(last => adjBonuses(last)(nextIdx)).getOrElse(0.0)
                nextScore = score + effectiveLength * (relevance + adjBonusForLast) + lastEffLen * (adjBonus - adjBonusForLast)
                mapKey = (visited, nextIdx, effectiveLength, nextRemaining) // TODO: (style) when we make State a case class, this should be from a method instead
                if bestVisited(mapKey) < nextScore
                _ = bestVisited.update(mapKey, nextScore)
                nextVisited = visited.add(nextIdx)
                nextVisitedSeq = nextIdx :: visitedSeq
                nextMaxed = if takeMax then maxed.add(nextIdx) else maxed
                (newBestBonus, newBestBonusLen) =
                    var best = bestBonus
                    var len = bestBonusLen
                    if !takeMax && relevance > best then
                        best = relevance
                        len = next.choiceLen
                        // TODO: should instead be `relevance + adjBonusForLast`, but then we also need to keep track in case the adj bonus gets replaced with a smaller one - if it becomes less than `best` then we will need to revert to the previous `best`
                    state.lastOpt.foreach: last =>
                        if lastEffLen == intervals(last).from then
                            val lastBonus = intervals(last).relevance + adjBonus
                            if lastBonus > best then
                                best = lastBonus
                                len = intervals(last).choiceLen
                    (best, len)
                nextState = State(nextVisited, effectiveLength, nextRemaining, nextScore, nextMaxed, nextVisitedSeq, newBestBonus, newBestBonusLen)
                _ =
                    // TODO (style): should these be a part of the case class if we're copying them around like this
                    nextState.mostRemovable = state.mostRemovable
                    nextState.mostAddable = state.mostAddable
                    state.lastOpt.foreach: last =>
                        val (worstFlatLoss, worstEfficiency, worstLen) = nextState.mostRemovable.getOrElse((Double.MinValue, Double.MaxValue, 0))
                        inline def approxBadness(flat: Double, eff: Double, len: Int) = flat - eff * len / 2
                        val badness = approxBadness(worstFlatLoss, worstEfficiency, worstLen)
                        val efficiency = intervals(last).relevance + adjBonuses(last)(nextIdx)
                        if lastEffLen == intervals(last).from then
                            val (bestEfficiency, _, _) = nextState.mostAddable.getOrElse((0.0, 0, 0))
                            if efficiency > bestEfficiency then
                                nextState.mostAddable = Some((efficiency, intervals(last).from, intervals(last).choiceLen))
                            visitedSeq.headOption.foreach: beforeLast =>
                                val beforeLastLen = if maxed.contains(beforeLast) then intervals(beforeLast).toWithBonus else intervals(beforeLast).from.toDouble
                                // this "loss" might be a negative number, making it a gain
                                val flatLoss = beforeLastLen * (adjBonuses(beforeLast)(last) - adjBonuses(beforeLast)(nextIdx))
                                if approxBadness(flatLoss, efficiency, intervals(last).from) > badness then
                                    nextState.mostRemovable = Some((flatLoss, efficiency, intervals(last).from))
                        else
                            val flatLoss = MAX_INTERVAL_BONUS * intervals(last).to * efficiency
                            if approxBadness(flatLoss, efficiency, intervals(last).choiceLen) > badness then
                                nextState.mostRemovable = Some((flatLoss, efficiency, intervals(last).choiceLen))
                if heuristic(nextState) > bestScore
            yield nextState
            fringe ++= nextStates
        val state@State(visited, lastEffLen, remaining, score, maxed, visitedSeq, bestBonus, bestBonusLen) = bestSolution.get
        println(s"heurCalls = $heurCalls | score = ${bestScore / FPS} | len = ${visitedSeq.length}")
        // println(s"$target | ${state.visitedSeq}")
        /*
        println("double check: " + ({
            var score = 0
            visitedSeq.indices.map(i => {
                val idx = visitedSeq(i)
                val adjBonus = if (i == 0) adjBonusForLast else adjBonuses(idx)(visitedSeq(i - 1))
                val effLen = if (maxed.contains(idx)) intervals(idx).toWithBonus else intervals(idx).from.toDouble
                (adjBonus + intervals(idx).relevance) * effLen
            }).sum + remaining * bestBonus
        } / 120).toString)
        */
        println("lengths: " + {
            visitedSeq.indices.map(i => {
                val idx = visitedSeq(i)
                val len = if (maxed.contains(idx)) intervals(idx).to else intervals(idx).from
                (idx, len)
            })
        } + " | " + remaining)
        (state.visitedSeq, bestScore / FPS)
