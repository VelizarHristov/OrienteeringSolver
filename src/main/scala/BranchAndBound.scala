package main

import collection.immutable.Queue
import collection.mutable

// TODO: should not crash with small problem sizes (should give the same output as brute force)
object BranchAndBound:
    opaque type BitSet = Long

    object BitSet:
        def apply() = 0L
        
    extension(set: BitSet)
        def add(i: Int) = set + (1L << i)
        def contains(i: Int) = (set & (1L << i)) != 0
        def safeAdd(i: Int) = if !contains(i) then add(i) else set

    def solveBranchAndBound(
        intervals: Array[Interval],
        adjBonuses: Array[Array[Double]],
        target: Int,
        MAX_INTERVAL_BONUS: Double,
        LAST_ADJ_MULT: Double,
        useZeroHeuristic: Boolean = false
    ) =
        require(intervals.size < 64, "error: we are using a Long for BitSet")
        var heurCalls = 0
        var debug = false
        def dprintln(s: String) = if debug then println(s)

        val adjBonusForLast = adjBonuses.zipWithIndex.map(
            (arr, i) => arr.sum - arr(i)
        ).sum / (intervals.length * (intervals.length - 1)) * LAST_ADJ_MULT
        if useZeroHeuristic then
            val lsSolution = Seq(0, 7, 8, 1, 4, 5, 6, 9)
            val lsLengths = Seq(475, 1038, 388, 917, 506, 546, 1140, 532)
            println(lsSolution.map(i => intervals(i)))
            println(lsSolution.zip(lsLengths).forall((i, len) => intervals(i).from <= len && intervals(i).to >= len))
            println(lsLengths.sum)
            println(target)
            val items = lsSolution.indices.map(i => {
                val idx1 = lsSolution(i)
                val adjBonus = if (i == (lsSolution.length - 1)) adjBonusForLast else adjBonuses(idx1)(lsSolution(i + 1))
                val maxIntervalBonus = if (lsLengths(i) == intervals(idx1).to) (1 + MAX_INTERVAL_BONUS) else 1
                (intervals(idx1).relevance + adjBonus) * lsLengths(i) * maxIntervalBonus
            })
            println(items.sum)
            println(items.sum / 120)

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
            var usedEdges = BitSet()
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
        def heuristic2(state: State) =
            def includeOrExclude(state: State, included: List[Int], depth: Int): Double =
                val (heuristicScore, usedIndices, usedEdges) = heuristicCalcOld(state, included)
                intervals.indices.find(i => usedEdges.contains(i) && !usedIndices.contains(i) && !included.contains(i) && intervals(i).from <= state.remaining) match
                    case Some(idx) =>
                        val excludedState = state.copy(visited = state.visited.add(idx))
                        if depth == 0 then
                            val excludedScore = heuristicCalcOld(excludedState, included)._1
                            val includedScore = heuristicCalcOld(state, idx :: included)._1
                            excludedScore max includedScore
                        else
                            val excludedScore = includeOrExclude(excludedState, included, depth - 1)
                            val includedScore = includeOrExclude(state, idx :: included, depth - 1)
                            excludedScore max includedScore
                    case None => heuristicScore
            includeOrExclude(state, List(), HEURISTIC_DEPTH)

        val bestEffPrecalc = adjBonuses.zipWithIndex.map: (arr, i) =>
            val bonusesForI = arr.indices.map(j => (j, arr(j))) :+ (-1, adjBonusForLast)
            bonusesForI.map((j, bonus) =>
                (j, (intervals(i).relevance + bonus) * (1 + MAX_INTERVAL_BONUS))
            ).sortBy(-_._2).toArray
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
            val initialNextIndices = Array.fill(intervals.length)(1)
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
            state.lastOpt.foreach: last =>
                bestEffPerNode(last).headOption.foreach: (toNodeIdx, eff) =>
                    // adjust because bestEffPerNode always gives a MAX_INTERVAL_BONUS and the includes relevance
                    initEstScore -= state.lastEffLen * (intervals(last).relevance + adjBonusForLast)
                    val updatedEffLen = state.lastEffLen / (1 + MAX_INTERVAL_BONUS)
                    initEstScore += updatedEffLen * eff
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
            // val h1 = startHState.finalEstScore
            // val h2 = heuristicCalcOld(state)._1
            // if ((h1 - h2).abs > 0.00001) {
            //     println("\n\n\n\n\nEND!!!\n\n\n\n\n")
            //     println("state = " + state)
            //     println("start score = " + state.score)
            //     println("target = " + target)
            //     println("remaining = " + state.remaining)
            //     println(bestEffPerNode(state.lastOpt.get).headOption)
            //     debug = true
            //     heuristicCalcOld(state)
            //     println((h1, h2, startHState))
            //     intervals.foreach(println)
            //     System.exit(0)
            // }

            println("start")
            def includeOrExcludeFaster(hState: HeuristicState, depth: Int): Double =
                // (TODO) enhancements that might diverge from the slower version of this heuristic:
                //     TODO: instead of picking an arbitrary edge, pick the one which would worsen estScore the most
                //         TODO (speedup): reuse computation between different edges under consideration
                //         TODO (simplicity): check if doing this lets us get rid of edgesInPermaIncluded
                //     TODO: force-included nodes should be unable to use adjBonusForLast
                // TODO (unsure if in the above category or mandatory to fix): it should be impossible to include/exclude everything, because at least one node should be able to use adjBonusForLast
                val includedIndices = hState.included.map(_._1).toSet
                val edgesInIncluded = hState.included.map(_._2).toSet
                val totalIncludedLen = hState.reducedLengths.keys.map(i =>
                    if (i == -1)
                        0
                    else
                        intervals(i).from
                ).sum
                println(hState.next)
                println(hState.included)
                println(hState)
                println("--------")
                // TODO ponder: whether it's ok if `next` ever contains something with a better efficiency than included.head - because: 1) this sometimes happens, and 2) I think it's not ok
                if (hState.next.headOption.exists(item => item._3 > hState.included.headOption.map(_._3).getOrElse(Double.MaxValue))) {
                    println(hState.next)
                    println(hState.included)
                    println(hState)
                    System.exit(0)
                }
                // TODO (minor performance): the above two statements can be made much faster, but check whether they matter anyway
                val nextEdge = intervals.indices.find: i =>
                    (edgesInIncluded.contains(i) || hState.edgesInPermaIncluded.get(i).exists(_.nonEmpty)) &&
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
                                estScore -= intervals(i).from * (oldEff - newEff)
                                edgesInPermaIncluded = edgesInPermaIncluded.updatedWith(newEdge)(_.map(_ + i))
                            edgesInPermaIncluded = edgesInPermaIncluded.removed(idx)
                            var remaining = hState.remaining
                            val (toRemove, newIncluded) = hState.included.partition(_._2 == idx)
                            toRemove.foreach: (i, _, eff) =>
                                val len = hState.reducedLengths.get(i).getOrElse(intervals(i).to)
                                remaining += len
                                estScore -= len * eff
                                val (newEdge, newEff) = updateAndGetNext(excluded, nextIndices, i)
                                next.enqueue((i, newEdge, newEff))
                            val included = newIncluded
                            val updState = HeuristicState(nextIndices, next, edgesInPermaIncluded,
                                included, hState.reducedLengths, excluded, remaining, estScore)
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
        inline def whichHeuristic(state: State) = if useZeroHeuristic then 10000000.0 else heuristic2(state)
        // inline def whichHeuristic = heuristic1
        inline def heuristic(state: State) = state.heuristic.getOrElse({
            heurCalls += 1
            val h = whichHeuristic(state)
            // val h1 = heuristic1(state)
            // val h4 = heuristic4(state)
            // if ((h4 - h1).abs > 0.000001) {
            //     println((h1, h4))
            //     println(state)
            //     System.exit(0)
            // }
            state.heuristic = Some(h)
            h
        })

        inline def displayHeuristics(s: State) =
            val heuristics = Seq(heuristic1, heuristic2, heuristic2Faster)
            println(heuristics.map(_(s)).mkString(" | "))

        val startState = State(BitSet(), -1, target, 0.0, BitSet(), List[Int](), 0.0, 0)
        val fringe = mutable.PriorityQueue(startState)(
            using (a, b) => heuristic(a).compare(heuristic(b))
        )
        val bestVisited = mutable.Map[(BitSet, Int, Double, Int), Double]().withDefaultValue(Double.MinValue)
        var bestScore = Double.MinValue
        var bestSolution: Option[State] = None
        while (fringe.nonEmpty && heuristic(fringe.head) > bestScore)
            if heurCalls % 1000 == 0 then
                displayHeuristics(fringe.head)
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
