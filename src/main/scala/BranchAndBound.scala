package main

import collection.immutable.Queue
import collection.mutable

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
            // println("h1")
            // println(estScore)
            while (remaining != 0 && skipped < bestForPair.length)
                val (i, j, efficiency) = bestForPair(skipped)
                // println("test: " + (visited.contains(37), visited))
                if efficiency < state.bestBonus && !usedBestBonusLen then
                    val lenToUse = state.bestBonusLen min remaining
                    estScore += lenToUse * state.bestBonus
                    remaining -= lenToUse
                    usedBestBonusLen = true
                    // println(("best", estScore))
                else
                    // println("observing " + (i, j, efficiency, visited.contains(i), state.visited.contains(j)))
                    if !visited.contains(i) && !state.visited.contains(j) then
                        val len = if requiredToPick.contains(i) then intervals(i).choiceLen else intervals(i).to
                        val lenToUse = len min remaining
                        estScore += lenToUse * efficiency
                        remaining -= lenToUse
                        visited = visited.add(i)
                        usedEdges = usedEdges.safeAdd(j)
                        // println((i, j, efficiency, lenToUse, estScore))
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
                val (heuristicScore, usedIdx, usedEdges) = heuristicCalc(state, included)
                intervals.indices.find(i => usedEdges.contains(i) && !usedIdx.contains(i) && !included.contains(i) && intervals(i).from <= state.remaining) match
                    case Some(idx) =>
                        val excludedState = state.copy(visited = state.visited.add(idx))
                        if depth == 0 then
                            val excludedScore = heuristicCalc(excludedState, included)._1
                            val includedScore = heuristicCalc(state, idx :: included)._1
                            excludedScore max includedScore
                        else
                            val excludedScore = includeOrExclude(excludedState, included, depth - 1)
                            val includedScore = includeOrExclude(state, idx :: included, depth - 1)
                            excludedScore max includedScore
                    case None => heuristicScore
            includeOrExclude(state, List(), HEURISTIC_DEPTH)

        def heuristic2Faster(state: State) =
            // TODO: (style) rename the next two variables
            val bestForPair2 =
                val builder = mutable.ArrayBuilder.make[(Int, Int, Double)]
                var idx = 0
                var prevEff = Double.MaxValue
                bestForPair.indices.foreach: idx =>
                    val x@(i, j, eff) = bestForPair(idx)
                    if !state.visited.contains(i) && !state.visited.contains(j) then
                        if prevEff > state.bestBonus && state.bestBonus > eff then
                            builder += ((-1, -1, state.bestBonus))
                        builder += x
                        prevEff = eff
                builder.result()
            val bestBonuses2 = bestBonuses.zipWithIndex.map((arr, i) => arr
                .view
                .filter((j, _) => !state.visited.contains(j))
                .map((j, bonus) => (j, (intervals(i).relevance + bonus) * (1 + MAX_INTERVAL_BONUS)))
                .toArray
            )

            case class HeuristicState(
                addedNodes: Map[Int, Queue[(Int, Double)]],
                permaIncluded: Vector[(Double, Int, Array[(Int, Double)])],
                edgesInNodes: Map[Int, Set[Int]],
                edgesInPermaIncluded: Map[Int, Set[Int]],
                included: List[(Int, Int, Double)],
                reducedLengths: Map[Int, Int],
                excluded: BitSet,
                remaining: Int,
                estScore: Double,
                skipped: Int
            ):
                lazy val finalEstScore =
                    if skipped < bestForPair2.length && remaining > 0 then
                        val (i, j, efficiency) = bestForPair2(skipped)
                        val len = reducedLengths.get(i).getOrElse(intervals(i).to)
                        if addedNodes.contains(i) || excluded.contains(j) || remaining > len then
                            throw new IllegalStateException("This should never happen - we have a bug")
                        else
                            estScore + efficiency * remaining
                    else
                        estScore

            var permaIncluded = Vector[(Double, Int, Array[(Int, Double)])]()
            var edgesInPermaIncluded = Map[Int, Set[Int]]()
            var estScore = state.score
            state.lastOpt.foreach: last =>
                val arr = bestBonuses2(last)
                arr.headOption.foreach: (toNodeIdx, eff) =>
                    // adjust because bestBonuses2 always gives a MAX_INTERVAL_BONUS and the includes relevance
                    estScore -= state.lastEffLen * (intervals(last).relevance + adjBonusForLast)
                    val updatedEffLen = state.lastEffLen / (1 + MAX_INTERVAL_BONUS)
                    estScore += updatedEffLen * eff
                    permaIncluded = (updatedEffLen, 0, arr) +: permaIncluded
                    edgesInPermaIncluded = edgesInPermaIncluded.updated(toNodeIdx, Set(0))
            val initialHState = HeuristicState(Map(), permaIncluded, Map(), edgesInPermaIncluded, List(),
                Map(-1 -> state.bestBonusLen), BitSet(), state.remaining, estScore, 0)

            def fillCapacity(hState: HeuristicState) =
                var addedNodes = hState.addedNodes
                var edgesInNodes = hState.edgesInNodes
                var included = hState.included
                var estScore = hState.estScore
                var remaining = hState.remaining
                var skipped = hState.skipped
                var stop = false
                while (!stop && remaining > 0 && skipped < bestForPair2.length)
                    val (i, j, efficiency) = bestForPair2(skipped)
                    if !addedNodes.contains(i) && !hState.excluded.contains(j) then
                        val len = hState.reducedLengths.get(i).getOrElse(intervals(i).to)
                        if remaining < len then
                            stop = true
                        else
                            estScore += len * efficiency
                            remaining -= len
                            if i != -1 then
                                included = (i, j, efficiency) :: included
                                if i != j then // not real edges (more like edge CASES, duh!)
                                    addedNodes = addedNodes.updated(i, Queue())
                                    edgesInNodes = edgesInNodes.updatedWith(j)(s =>
                                        Some(s.getOrElse(Set()) + i)
                                    )
                    else
                        addedNodes = addedNodes.updatedWith(i)(
                            _.map(_.enqueue((j, efficiency)))
                        )
                    if !stop then
                        skipped += 1
                HeuristicState(addedNodes, hState.permaIncluded, edgesInNodes,
                    hState.edgesInPermaIncluded, included, hState.reducedLengths, hState.excluded,
                    remaining, estScore, skipped)
            val startHState = fillCapacity(initialHState)
            val h1 = startHState.finalEstScore
            val h2 = heuristicCalc(state)._1
            if ((h1 - h2).abs > 0.00001) {
                println("\n\n\n\n\nEND!!!\n\n\n\n\n")
                debug = true
                heuristicCalc(state)
                println((h1, h2, startHState))
                println(bestForPair2.toList)
                System.exit(0)
            }

            def includeOrExcludeFaster(hState: HeuristicState, depth: Int): Double =
                // TODO: instead of picking an arbitrary edge, pick the one which would worsen estScore the most
                val nextEdge = hState.edgesInNodes.keys.headOption.orElse(hState.edgesInPermaIncluded.keys.headOption)
                nextEdge match
                    case Some(idx) =>
                        val includedState =
                            var idxInArr = 0
                            val arr = bestBonuses2(idx)
                            while (hState.excluded.contains(arr(idxInArr)._1))
                                idxInArr += 1
                            var addedNodes = hState.addedNodes
                            val permaIncluded = hState.permaIncluded :+ (intervals(idx).from.toDouble, idxInArr, arr)
                            val edgesInNodes = hState.edgesInNodes.removed(idx)
                            val edgesInPermaIncluded = hState.edgesInPermaIncluded.removed(idx)
                            var included = hState.included
                            val reducedLengths = hState.reducedLengths.updated(idx, intervals(idx).choiceLen)
                            var remaining = hState.remaining - intervals(idx).from
                            var estScore = hState.estScore + intervals(idx).from * arr(idxInArr)._2
                            var skipped = hState.skipped
                            while (remaining < 0)
                                val removed@(idxToRemove, edgeToRemove, eff) = included.head
                                addedNodes = addedNodes.removed(idxToRemove)
                                included = included.tail
                                // TODO: rewinding this much is potentially slow, do we need to redesign the heuristic?
                                while (bestForPair2(skipped) != removed)
                                    skipped -= 1
                                val len = reducedLengths.get(idxToRemove).getOrElse(intervals(idxToRemove).to)
                                estScore -= eff * len
                                remaining += len
                            HeuristicState(addedNodes, permaIncluded, edgesInNodes, edgesInPermaIncluded,
                                included, reducedLengths, hState.excluded, remaining, estScore, skipped)
                        val excludedState =
                            val excluded = hState.excluded.add(idx)
                            var estScore = hState.estScore
                            var edgesInPermaIncluded = hState.edgesInPermaIncluded
                            hState.edgesInPermaIncluded.get(idx).foreach: indices =>
                                indices.foreach: i =>
                                    val (len, idxInArr, arr) = permaIncluded(i)
                                    var newIdx = idxInArr + 1
                                    while (excluded.contains(arr(newIdx)._1))
                                        newIdx += 1
                                    val (newNext, newEff) = arr(newIdx)
                                    estScore -= len * (arr(idxInArr)._2 - newEff)
                                    permaIncluded = permaIncluded.updated(i, (len, newIdx, arr))
                                    edgesInPermaIncluded = edgesInPermaIncluded.updatedWith(newNext)(s => {
                                        s match
                                            case Some(set) => Some(set + i)
                                            case None => Some(Set(i))
                                    })
                            edgesInPermaIncluded = edgesInPermaIncluded.removed(idx)
                            var addedNodes = hState.addedNodes
                            var included = hState.included
                            var remaining = hState.remaining
                            var skipped = hState.skipped
                            var edgesInNodes = hState.edgesInNodes
                            hState.edgesInNodes.get(idx).foreach: indices =>
                                indices.foreach: i =>
                                    var queue = addedNodes(i)
                                    var stop = false
                                    while (!stop)
                                        queue.dequeueOption match
                                            case Some(((edge, newEff), nextQueue)) =>
                                                queue = nextQueue
                                                if !excluded.contains(edge) then
                                                    val len = hState.reducedLengths.get(i).getOrElse(intervals(i).to)
                                                    // estScore -= len * (??? - newEff)
                                                    intervals(i)
                                                    stop = true
                                                    // TODO: handle this case
                                            case None =>
                                                stop = true
                                                // TODO: handle this case
                                    addedNodes = addedNodes.updated(i, queue)
                                    // TODO: also update edgesInNodes to add the new edge
                            edgesInNodes = edgesInNodes.removed(idx)
                            HeuristicState(addedNodes, permaIncluded, edgesInNodes, edgesInPermaIncluded,
                                included, hState.reducedLengths, excluded, remaining, estScore, skipped)
                        if depth == 0 then
                            includedState.finalEstScore max excludedState.finalEstScore
                        else
                            val includedScore = includeOrExcludeFaster(includedState, depth - 1)
                            val excludedScore = includeOrExcludeFaster(excludedState, depth - 1)
                            includedScore max excludedScore
                    case None =>
                        hState.finalEstScore
            includeOrExcludeFaster(startHState, HEURISTIC_DEPTH)

        /*
        def heuristic2Faster2(state: State) =
            val bestBonuses2 = bestBonuses.zipWithIndex.map((arr, i) => arr
                .view
                .filter((j, _) => !state.visited.contains(j))
                .map((j, bonus) => (j, (intervals(i).relevance + bonus) * (1 + MAX_INTERVAL_BONUS)))
                .toArray
            )
            val nextIndices = Array.fill(intervals.length)(0)
            val forQueue = intervals.indices.filterNot(state.visited.contains).map(i =>
                val (j, eff) = bestBonuses2(i).head
                (i, j, eff)
            )
            val next = mutable.PriorityQueue(forQueue *)(using (a, b) => a._3.compare(b._3))
            // TODO: add the one-off bonus to `next`

            case class HeuristicState(
                nextIndices: Array[Int],
                next: mutable.PriorityQueue[(Int, Int, Double)],
                addedNodes: Map[Int, Queue[(Int, Double)]], // TODO: delete
                permaIncluded: Vector[(Double, Int, Array[(Int, Double)])], // TODO: no need to have another reference to the array - the array is already in `bestBonuses2`, the idx in already in `nextIndices`
                edgesInNodes: Map[Int, Set[Int]],
                edgesInPermaIncluded: Map[Int, Set[Int]],
                included: List[(Int, Int, Double)],
                reducedLengths: Map[Int, Int],
                excluded: BitSet,
                remaining: Int,
                estScore: Double,
            ):
                lazy val finalEstScore = next.headOption match
                    case Some((i, j, efficiency)) =>
                        val len = reducedLengths.get(i).getOrElse(intervals(i).to)
                        if addedNodes.contains(i) || excluded.contains(j) || remaining > len then
                            throw new IllegalStateException("This should never happen - we have a bug")
                        else
                            estScore + efficiency * remaining
                    case None => estScore

            var permaIncluded = Vector[(Double, Int, Array[(Int, Double)])]()
            var edgesInPermaIncluded = Map[Int, Set[Int]]()
            var estScore = state.score
            state.lastOpt.foreach: last =>
                val arr = bestBonuses2(last)
                arr.headOption.foreach: (toNodeIdx, eff) =>
                    // adjust because bestBonuses2 always gives a MAX_INTERVAL_BONUS and the includes relevance
                    estScore -= state.lastEffLen * (intervals(last).relevance + adjBonusForLast)
                    val updatedEffLen = state.lastEffLen / (1 + MAX_INTERVAL_BONUS)
                    estScore += updatedEffLen * eff
                    permaIncluded = (updatedEffLen, 0, arr) +: permaIncluded
                    edgesInPermaIncluded = edgesInPermaIncluded.updated(toNodeIdx, Set(0))
            val initialHState = HeuristicState(nextIndices, next, Map(), permaIncluded, Map(), edgesInPermaIncluded, List(),
                Map(-1 -> state.bestBonusLen), BitSet(), state.remaining, estScore)

            def fillCapacity(hState: HeuristicState) =
                var addedNodes = hState.addedNodes
                var edgesInNodes = hState.edgesInNodes
                var included = hState.included
                var estScore = hState.estScore
                var remaining = hState.remaining
                var stop = false
                while (!stop && remaining > 0 && hState.next.nonEmpty)
                    val (i, j, efficiency) = hState.next.dequeue()
                    if !addedNodes.contains(i) && !hState.excluded.contains(j) then
                        val len = hState.reducedLengths.get(i).getOrElse(intervals(i).to)
                        if remaining < len then
                            stop = true
                        else
                            estScore += len * efficiency
                            remaining -= len
                            if i != -1 then
                                included = (i, j, efficiency) :: included
                                if i != j then // not real edges (more like edge CASES, duh!)
                                    edgesInNodes = edgesInNodes.updatedWith(j)(s =>
                                        Some(s.getOrElse(Set()) + i)
                                    )
                    if !stop then
                        skipped += 1
                HeuristicState(addedNodes, hState.permaIncluded, edgesInNodes,
                    hState.edgesInPermaIncluded, included, hState.reducedLengths, hState.excluded,
                    remaining, estScore)
            val startHState = fillCapacity(initialHState)
            val h1 = startHState.finalEstScore
            val h2 = heuristicCalc(state)._1
            if ((h1 - h2).abs > 0.00001) {
                println("\n\n\n\n\nEND!!!\n\n\n\n\n")
                debug = true
                heuristicCalc(state)
                println((h1, h2, startHState))
                System.exit(0)
            }

            def includeOrExcludeFaster(hState: HeuristicState, depth: Int): Double =
                // TODO: instead of picking an arbitrary edge, pick the one which would worsen estScore the most
                val nextEdge = hState.edgesInNodes.keys.headOption.orElse(hState.edgesInPermaIncluded.keys.headOption)
                nextEdge match
                    case Some(idx) =>
                        val includedState =
                            var idxInArr = 0
                            val arr = bestBonuses2(idx)
                            while (hState.excluded.contains(arr(idxInArr)._1))
                                idxInArr += 1
                            var addedNodes = hState.addedNodes
                            val permaIncluded = hState.permaIncluded :+ (intervals(idx).from.toDouble, idxInArr, arr)
                            val edgesInNodes = hState.edgesInNodes.removed(idx)
                            val edgesInPermaIncluded = hState.edgesInPermaIncluded.removed(idx)
                            var included = hState.included
                            val reducedLengths = hState.reducedLengths.updated(idx, intervals(idx).choiceLen)
                            var remaining = hState.remaining - intervals(idx).from
                            var estScore = hState.estScore + intervals(idx).from * arr(idxInArr)._2
                            while (remaining < 0)
                                val removed@(idxToRemove, edgeToRemove, eff) = included.head
                                addedNodes = addedNodes.removed(idxToRemove)
                                included = included.tail
                                val len = reducedLengths.get(idxToRemove).getOrElse(intervals(idxToRemove).to)
                                estScore -= eff * len
                                remaining += len
                            HeuristicState(addedNodes, permaIncluded, edgesInNodes, edgesInPermaIncluded,
                                included, reducedLengths, hState.excluded, remaining, estScore)
                        val excludedState =
                            val excluded = hState.excluded.add(idx)
                            var estScore = hState.estScore
                            var edgesInPermaIncluded = hState.edgesInPermaIncluded
                            hState.edgesInPermaIncluded.get(idx).foreach: indices =>
                                indices.foreach: i =>
                                    val (len, idxInArr, arr) = permaIncluded(i)
                                    var newIdx = idxInArr + 1
                                    while (excluded.contains(arr(newIdx)._1))
                                        newIdx += 1
                                    val (newNext, newEff) = arr(newIdx)
                                    estScore -= len * (arr(idxInArr)._2 - newEff)
                                    permaIncluded = permaIncluded.updated(i, (len, newIdx, arr))
                                    edgesInPermaIncluded = edgesInPermaIncluded.updatedWith(newNext)(s => {
                                        s match
                                            case Some(set) => Some(set + i)
                                            case None => Some(Set(i))
                                    })
                            edgesInPermaIncluded = edgesInPermaIncluded.removed(idx)
                            var addedNodes = hState.addedNodes
                            var included = hState.included
                            var remaining = hState.remaining
                            var edgesInNodes = hState.edgesInNodes
                            hState.edgesInNodes.get(idx).foreach: indices =>
                                indices.foreach: i =>
                                    var queue = addedNodes(i)
                                    var stop = false
                                    while (!stop)
                                        queue.dequeueOption match
                                            case Some(((edge, newEff), nextQueue)) =>
                                                queue = nextQueue
                                                if !excluded.contains(edge) then
                                                    val len = hState.reducedLengths.get(i).getOrElse(intervals(i).to)
                                                    // estScore -= len * (??? - newEff)
                                                    intervals(i)
                                                    stop = true
                                                    // TODO: handle this case
                                            case None =>
                                                stop = true
                                                // TODO: handle this case
                                    addedNodes = addedNodes.updated(i, queue)
                                    // TODO: also update edgesInNodes to add the new edge
                            edgesInNodes = edgesInNodes.removed(idx)
                            HeuristicState(addedNodes, permaIncluded, edgesInNodes, edgesInPermaIncluded,
                                included, hState.reducedLengths, excluded, remaining, estScore)
                        if depth == 0 then
                            includedState.finalEstScore max excludedState.finalEstScore
                        else
                            val includedScore = includeOrExcludeFaster(includedState, depth - 1)
                            val excludedScore = includeOrExcludeFaster(excludedState, depth - 1)
                            includedScore max excludedScore
                    case None =>
                        hState.finalEstScore
            includeOrExcludeFaster(startHState, HEURISTIC_DEPTH)
        */

        // TODO: try having a constraint on each `j` (edge-destination) appearing only once, rather than potentially giving adj bonus to multiple; or compromise variant: spanning tree/arborescence, if that's at all possible
        // TODO: try having only one adjBonusForLast
        inline def whichHeuristic(state: State) = if useZeroHeuristic then 10000000.0 else heuristic1(state)
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
            val heuristics = Seq(heuristic1, heuristic2)
            println(heuristics.map(_(s)).mkString(" | "))

        val startState = State(BitSet(), -1, target, 0.0, BitSet(), List[Int](), 0.0, 0)
        val fringe = mutable.PriorityQueue(startState)(
            using (a, b) => heuristic(a).compare(heuristic(b))
        )
        val bestVisited = mutable.Map[(BitSet, Int, Double, Int), Double]().withDefaultValue(Double.MinValue)
        var bestScore = Double.MinValue
        var bestSolution: Option[State] = None
        while (fringe.nonEmpty && heuristic(fringe.head) > bestScore)
            // if heurCalls % 200000 == 0 then
            //     displayHeuristics(fringe.head)
            //     println((fringe.size, fringe.head.score, bestScore))
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
        // println(s"heurCalls = $heurCalls | score = ${bestScore / FPS} | len = ${visitedSeq.length}")
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
