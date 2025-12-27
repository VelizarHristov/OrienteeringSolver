package main

import collection.mutable

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
        bestBonusLen: Int,
        mostRemovable: Option[(flatLoss: Double, efficiency: Double, len: Int)] = None,
        mostAddable: Option[(efficiency: Double, maxLen: Int, addableLen: Int)] = None
    ):
        inline def lastOpt = visitedSeq.headOption
        var heuristic: Option[Double] = None

        // TODO: tighten this by turning mostRemovable and mostAddable into sorted lists (heaps) and comparing them more thoroughly

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
    val bestBonuses = adjBonuses.map: arr =>
        arr.indices.map(j => (j, arr(j))).sortBy(-_._2).toArray

    def heuristicCalc(state: State, requiredToPick: List[Int] = List()) =
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

    def heuristicFast(state: State) = heuristicCalc(state)._1

    val MAX_HEURISTIC_DEPTH = 5
    def heuristicInclExcl(initialState: State) =
        def includeOrExclude(state: State, included: List[Int], depth: Int): Double =
            val (heuristicScore, usedIndices, usedEdges) = heuristicCalc(state, included)
            intervals.indices.find(i => usedEdges.contains(i) && !usedIndices.contains(i) && !included.contains(i) && intervals(i).from <= state.remaining) match
                case Some(idx) =>
                    val excludedState = state.copy(visited = state.visited.add(idx))
                    if depth == 0 then
                        val includedScore = heuristicCalc(state, idx :: included)._1
                        val excludedScore = heuristicCalc(excludedState, included)._1
                        includedScore max excludedScore
                    else
                        val includedScore = includeOrExclude(state, idx :: included, depth - 1)
                        val excludedScore = includeOrExclude(excludedState, included, depth - 1)
                        includedScore max excludedScore
                case None => heuristicScore
        val depthToUse = 1 max (MAX_HEURISTIC_DEPTH - initialState.visitedSeq.size)
        includeOrExclude(initialState, List(), depthToUse)

    inline def whichHeuristic(state: State) = heuristicInclExcl(state)
    inline def heuristic(state: State) = state.heuristic.getOrElse({
        heurCalls += 1
        val h = whichHeuristic(state)
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
            if heurCalls % 25000 == 0 then
                println((fringe.size, fringe.head.score, bestScore))
            val state@State(visited, lastEffLen, remaining, score, maxed, visitedSeq, bestBonus,
                bestBonusLen, mostRemovable, mostAddable) = fringe.dequeue()
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
                mapKey = (visited, nextIdx, effectiveLength, nextRemaining)
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
                (mostRm, mostAdd) =
                    var mostRm = mostRemovable
                    var mostAdd = mostAddable
                    state.lastOpt.foreach: last =>
                        val (worstFlatLoss, worstEfficiency, worstLen) = mostRm.getOrElse((Double.MinValue, Double.MaxValue, 0))
                        inline def approxBadness(flat: Double, eff: Double, len: Int) = flat - eff * len / 2
                        val badness = approxBadness(worstFlatLoss, worstEfficiency, worstLen)
                        val efficiency = intervals(last).relevance + adjBonuses(last)(nextIdx)
                        if lastEffLen == intervals(last).from then
                            val (bestEfficiency, _, _) = mostAdd.getOrElse((0.0, 0, 0))
                            if efficiency > bestEfficiency then
                                mostAdd = Some((efficiency, intervals(last).from, intervals(last).choiceLen))
                            visitedSeq.headOption.foreach: beforeLast =>
                                val beforeLastLen = if maxed.contains(beforeLast) then intervals(beforeLast).toWithBonus else intervals(beforeLast).from.toDouble
                                // this "loss" might be a negative number, making it a gain
                                val flatLoss = beforeLastLen * (adjBonuses(beforeLast)(last) - adjBonuses(beforeLast)(nextIdx))
                                if approxBadness(flatLoss, efficiency, intervals(last).from) > badness then
                                    mostRm = Some((flatLoss, efficiency, intervals(last).from))
                        else
                            val flatLoss = MAX_INTERVAL_BONUS * intervals(last).to * efficiency
                            if approxBadness(flatLoss, efficiency, intervals(last).choiceLen) > badness then
                                mostRm = Some((flatLoss, efficiency, intervals(last).choiceLen))
                    (mostRm, mostAdd)
                nextState = State(nextVisited, effectiveLength, nextRemaining, nextScore, nextMaxed,
                    nextVisitedSeq, newBestBonus, newBestBonusLen, mostRm, mostAdd)
                if heuristic(nextState) > bestScore
            yield nextState
            fringe ++= nextStates
        val state@State(visited, lastEffLen, remaining, score, maxed, visitedSeq, bestBonus, bestBonusLen, _, _) = bestSolution.get
        println(s"heurCalls = $heurCalls | score = ${bestScore / FPS} | len = ${visitedSeq.length}")
        println("lengths: " + {
            visitedSeq.indices.map(i => {
                val idx = visitedSeq(i)
                val len = if (maxed.contains(idx)) intervals(idx).to else intervals(idx).from
                (idx, len)
            })
        } + " | " + remaining)
        (state.visitedSeq, bestScore / FPS)
