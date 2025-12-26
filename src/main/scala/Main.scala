package main

import collection.mutable
import util.Random

var MAX_INTERVAL_BONUS = 0.03
// a rough approximate of the average adj bonus of the optimal trip, divided by the average of all adj bonuses
var LAST_ADJ_MULT = 1.2
val FPS = 120
// how important adj bonus is relative to relevance - max relevance is 1.0
var MAX_ADJ_BONUS = 0.5

var kToUse = 4
var useSlowerLengthsFunc = false

case class Interval(from: Int, to: Int, relevance: Double):
    val choiceLen = to - from
    // effective length, only for calculating score
    val toWithBonus = to * (1 + MAX_INTERVAL_BONUS)

// TODO: could speed up by storing curLen and score in allStates (but I don't think it will help that much)
def solveBruteForce(intervals: Array[Interval], adjBonuses: Array[Array[Double]], target: Int) =
    val adjBonusForLast =
        if intervals.length == 1 then
            0.0
        else
            adjBonuses.zipWithIndex.map(
                (arr, i) => arr.sum - arr(i)
            ).sum / (intervals.length * (intervals.length - 1)) * LAST_ADJ_MULT

    var allStates = Vector((List[Boolean](), List[Int]()))
    var bestScore = Double.MinValue
    var bestState = allStates.head
    var paddedNode = -1
    var lengths = List[Int]()
    while (allStates.nonEmpty)
        allStates = allStates.flatMap: (maxed, visited) =>
            val curLen = maxed.zip(visited).map((isMaxed, idx) => {
                if (isMaxed) intervals(idx).to else intervals(idx).from
            }).sum
            val remainingLen = target - curLen
            val score = visited.indices.map(i => {
                val id = visited(i)
                val effLen = if maxed(i) then intervals(id).toWithBonus else intervals(id).from.toDouble
                val adjBonus = if i == 0 then adjBonusForLast else adjBonuses(id)(visited(i - 1))
                effLen * (adjBonus + intervals(id).relevance)
            }).sum

            // deal with all states that terminate here
            for
                (max, idx) <- maxed.zip(visited)
                if !max
                if intervals(idx).choiceLen >= remainingLen
                nodeEfficiency =
                    val adjBonus =
                        if idx == visited.head then
                            adjBonusForLast
                        else
                            val nextNode = visited.reverse.dropWhile(_ != idx)(1)
                            adjBonuses(idx)(nextNode)
                    adjBonus + intervals(idx).relevance
                newScore = score + remainingLen * nodeEfficiency
                if newScore > bestScore
            do
                bestState = (maxed, visited)
                bestScore = newScore
                paddedNode = idx
                lengths = visited.zip(maxed).map: (id, isMaxed) =>
                    if isMaxed then
                        intervals(id).to
                    else if id == paddedNode then
                        intervals(id).from + remainingLen
                    else
                        intervals(id).from

            // generate all follow-up states
            for
                idx <- intervals.indices.filterNot(visited.contains)
                max <- Seq(true, false)
                lenToAdd = if (max) intervals(idx).to else intervals(idx).from
                if remainingLen >= lenToAdd
            yield (max :: maxed, idx :: visited)
    if paddedNode == -1 then
        None
    else
        // val visited = bestState._2
        // val score = lengths.indices.map(i => {
        //     val id = visited(i)
        //     val effLen = if lengths(i) == intervals(id).to then intervals(id).toWithBonus else lengths(i).toDouble
        //     val adjBonus = if i == 0 then adjBonusForLast else adjBonuses(id)(visited(i - 1))
        //     effLen * (adjBonus + intervals(id).relevance)
        // }).sum
        // println(lengths.indices.map(i => {
        //     val id = visited(i)
        //     val effLen = if lengths(i) == intervals(id).to then intervals(id).toWithBonus else lengths(i).toDouble
        //     val adjBonus = if i == 0 then adjBonusForLast else adjBonuses(id)(visited(i - 1))
        //     println((effLen, adjBonus, intervals(id).relevance))
        //     effLen * (adjBonus + intervals(id).relevance)
        // }))
        // println("score should be = " + score)
        // println("lengths.reverse = " + lengths.reverse)
        // println("visited.reverse = " + visited.reverse)
        // println("adjBonusForLast = " + adjBonusForLast)
        // paddedNode could also be outputted
        Some((bestState, bestScore, lengths))

def findFeasible(intervals: List[Interval], target: Int, slack: Int = 0): Option[List[Int]] =
    if slack > target then
        Some(List())
    else
        intervals match
            case Interval(from, to, _) :: nextIntervals =>
                val newTarget = target - from
                val newSlack = slack + (to - from)
                lazy val nextSolution = findFeasible(nextIntervals, target, slack)
                val solution = if newTarget < 0 then
                    nextSolution
                else
                    findFeasible(nextIntervals, newTarget, newSlack).map(-1 :: _).orElse(nextSolution)
                solution.map(_.map(_ + 1))
            case Nil => None

// TODO ideas to improve:
//     1. restart with different orders of intervals (then we must make sure that findFeasible won't crash),
//     2. explore the neighbourhoods in a shuffled order,
//     3. try making 2-combos of two different possible changes, even if the first makes it worse, with the second it should be better overall
def solveLocalSearch(intervals: Array[Interval], adjBonuses: Array[Array[Double]], target: Int) =
    val adjBonusForLast = adjBonuses.zipWithIndex.map(
        (arr, i) => arr.sum - arr(i)
    ).sum / (intervals.length * (intervals.length - 1)) * LAST_ADJ_MULT

    // Find an initial feasible solution - not necessarily efficient, but should be good enough especially with our data
    val intervalsByWidth = intervals.zipWithIndex.sortBy(-_._1.choiceLen)
    val intervalIdxMapping = intervalsByWidth.map(_._2)
    val initialSolutionShuffled = findFeasible(intervalsByWidth.map(_._1).toList, target).get
    var curSolution = initialSolutionShuffled.map(intervalIdxMapping.apply)

    def efficiencies(solution: Seq[Int]) = solution.indices.map: i =>
        val adjBonus = if i == (solution.length - 1) then adjBonusForLast else adjBonuses(solution(i))(solution(i + 1))
        intervals(solution(i)).relevance + adjBonus

    def getBestLengths(solution: Seq[Int], thisTarget: Int = target) =
        val bestEffs = efficiencies(solution).zipWithIndex.sortBy(-_._1)
        var spareLength = thisTarget - solution.map(i => intervals(i).from).sum
        var i = 0
        // taken at greater than `from`
        val extendedIntervals = mutable.ArrayBuffer[Int]()
        while (spareLength > 0 && i < bestEffs.length)
            val idx = solution(bestEffs(i)._2)
            spareLength -= intervals(idx).choiceLen
            extendedIntervals += idx
            i += 1
        val maxes = extendedIntervals.dropRight(1).toSet

        if spareLength > 0 then
            List.fill(solution.length)(0)
        else
            solution.map: i =>
                if maxes.contains(i) then
                    intervals(i).to
                else if extendedIntervals.lastOption.contains(i) then
                    intervals(i).to + spareLength // spareLength is a negative number
                else
                    intervals(i).from

    def solutionScore(solution: Seq[Int], lengths: Seq[Int]) =
        val effs = efficiencies(solution)
        solution.indices.map(i => {
            val maxBonus = if lengths(i) == intervals(solution(i)).to then (1 + MAX_INTERVAL_BONUS) else 1
            effs(i) * maxBonus * lengths(i)
        }).sum
    val simpleScoreMemo = mutable.Map[(Seq[Int]), Double]()
    def simpleScore(solution: Seq[Int]) = simpleScoreMemo.get(solution) match
        case Some(res) => res
        case None =>
            val res = if solution.map(i => intervals(i).from).sum > target then
                0
            else
                val lengths = if useSlowerLengthsFunc then getBestLengths2(solution) else getBestLengths(solution)
                solutionScore(solution, lengths)
            simpleScoreMemo(solution) = res
            res

    // TODO: rename (note - this is a slower version that sometimes finds a better score)
    def getBestLengths2(solution: Seq[Int]) =
        val bestEffs = efficiencies(solution).zipWithIndex.sortBy(-_._1)
        var spareLength = target - solution.map(i => intervals(i).from).sum
        var i = 0
        val bestLengths = mutable.ArrayBuffer[Int]()
        while (spareLength > 0 && i < bestEffs.length)
            val idx = solution(bestEffs(i)._2)
            spareLength -= intervals(idx).choiceLen
            bestLengths += idx
            i += 1
        val bestLengthsSet = bestLengths.toSet
        val notInBestLengths = solution.filterNot(bestLengthsSet.contains)
        val best = getBestLengths(solution)
        val bestScore = solutionScore(solution, best)
        if notInBestLengths.isEmpty then
            best
        else
            val (bestAltScore2, bestAlt2) =
                val res = for
                    idx1 <- notInBestLengths
                    idx2 <- notInBestLengths
                    if idx2 > idx1
                yield
                    val newTarget = target - intervals(idx1).choiceLen - intervals(idx2).choiceLen
                    val i1 = solution.indexOf(idx1)
                    val i2 = solution.indexOf(idx2)
                    val lengths = getBestLengths(
                        solution, newTarget
                    ).updated(i1, intervals(idx1).to).updated(i2, intervals(idx2).to)
                    if lengths.sum > target then
                        ((-10.0, Seq()))
                    else
                        (solutionScore(solution, lengths), lengths)
                res.maxByOption(_._1).getOrElse((-10.0, Seq()))

            val (bestAltScore, bestAlt) = notInBestLengths.map(idx => {
                val newTarget = target - intervals(idx).choiceLen
                val i = solution.indexOf(idx)
                val lengths = getBestLengths(
                    solution, newTarget
                ).updated(i, intervals(idx).to)
                if lengths.sum > target then
                    ((-10.0, Seq()))
                else
                    (solutionScore(solution, lengths), lengths)
            }).maxBy(_._1)
            val theBest = Seq(bestScore, bestAltScore, bestAltScore2).max
            if theBest == bestScore then
                best
            else if theBest == bestAltScore then
                bestAlt
            else
                bestAlt2

    def tryAdding(solution: List[Int]) =
        val initialScore = simpleScore(solution)
        val used = solution.toSet
        val pair = intervals.indices.filterNot(used).view.map(i => {
            val jToReplace = solution.indices.find: j =>
                val newSolution = (solution.take(j) :+ i) ++ solution.drop(j)
                val totalMinLen = newSolution.map(i => intervals(i).from).sum
                totalMinLen <= target && simpleScore(newSolution) > initialScore
            jToReplace.map(j => (i, j))
        }).find(_.isDefined).flatten
        pair.map: (i, j) =>
            (solution.take(j) :+ i) ++ solution.drop(j)

    def tryRemoving(solution: List[Int]) =
        val initialScore = simpleScore(solution)
        val jToReplace = solution.indices.find: j =>
            val newSolution = solution.take(j) ++ solution.drop(j + 1)
            simpleScore(newSolution) > initialScore
        jToReplace.map: j =>
            solution.take(j) ++ solution.drop(j + 1)

    def tryReversing(solution: List[Int]) =
        val initialScore = simpleScore(solution)
        val allPossibilities = for
            from <- 0 until solution.size - 1
            to <- from + 1 until solution.size
            newSolution = solution.take(from) ++ solution.drop(from).take(to - from + 1).reverse ++ solution.drop(to + 1)
            if simpleScore(newSolution) > initialScore
        yield newSolution
        allPossibilities.headOption

    def kReplace(k: Int)(solution: List[Int]) =
        val initialScore = simpleScore(solution)
        val remaining = intervals.indices.filterNot(solution.contains).toList
        // (k choose n) possibilities
        def removedIndices(k: Int, ls: List[Int], skipped: Int = 0): Iterator[List[Int]] =
            if k == 0 then
                Iterator(List())
            else
                (0 until ls.size - skipped - k + 1).iterator.flatMap: i =>
                    removedIndices(k - 1, ls, skipped + i + 1)
                        .map((i + skipped) +: _)
        val allPossibilities = for
            indices <- removedIndices(k, solution)
            toAdd <- removedIndices(k, remaining)
            permutation <- toAdd.permutations
            newSolution = indices.indices.foldLeft(solution)((curSolution, idx) =>
                curSolution.updated(indices(idx), remaining(permutation(idx)))
            )
            if simpleScore(newSolution) > initialScore
        yield newSolution
        allPossibilities.nextOption

    def kSwap(k: Int)(solution: List[Int]) =
        val initialScore = simpleScore(solution)
        // (k choose n) possibilities
        def removedIndices(k: Int, skipped: Int = 0): Iterator[List[Int]] =
            if k == 0 then
                Iterator(List())
            else
                (0 until solution.size - skipped - k + 1).iterator.flatMap: i =>
                    removedIndices(k - 1, skipped + i + 1)
                        .map((i + skipped) +: _)
        val allPossibilities = for
            indices <- removedIndices(k)
            permutation <- indices.permutations
            newSolution = indices.indices.foldLeft(solution)((curSolution, idx) =>
                curSolution.updated(indices(idx), solution(permutation(idx)))
            )
            if simpleScore(newSolution) > initialScore
        yield newSolution
        allPossibilities.nextOption

    def kOpt(k: Int)(solution: List[Int]) =
        val initialScore = simpleScore(solution)
        def partitions(k: Int, skipped: Int = 0): Iterator[List[List[Int]]] =
            if k == 0 then
                Iterator(List(solution.drop(skipped)))
            else
                (1 to solution.size - skipped - k + 1).iterator.flatMap: i =>
                    partitions(k - 1, skipped + i)
                        .map(solution.drop(skipped).take(i) +: _)

        val allPossibilities = for
            intervals <- partitions(k)
            permutation <- intervals.permutations
            if simpleScore(permutation.flatten) > initialScore
        yield permutation.flatten
        allPossibilities.nextOption

    val funcs = Seq(
        tryRemoving -> "tryRemoving",
        kOpt(2) -> s"kOpt(${2})",
        kReplace(1) -> s"kReplace(1)",
        tryAdding -> "tryAdding",
        tryReversing -> "tryReversing",
        kOpt(kToUse) -> s"kOpt(${kToUse})",
        kSwap(kToUse) -> s"kSwap(${kToUse})",
        kReplace(kToUse - 2) -> s"kReplace(${kToUse - 2})",
    ).view
    // val funcsInJsCode = Seq(
    //     kOpt(3) -> "kOpt(3)",
    //     kReplace(1) -> "kReplace(1)",
    //     tryAdding -> "tryAdding"
    // ).view
    var halt = false
    while (!halt)
        funcs.flatMap((f, name) => {
            f(curSolution).map(sol => (sol, name))
        }).headOption match
            case Some((newSolution, fName)) =>
                curSolution = newSolution
                // println(newSolution)
                // println(s"${simpleScore(curSolution) / FPS} <- $fName")
            case None =>
                halt = true

    println(s"Solution stats: $curSolution | ${getBestLengths(curSolution)} | ${getBestLengths2(curSolution)} | ${curSolution.map(intervals.apply)} | $target | $adjBonusForLast")
    val finalScore = simpleScore(curSolution) / FPS
    (curSolution, finalScore)

def calcProblemSize(intervals: Array[Interval], target: Int) =
    val maxSolutionLen = intervals.map(_.from).sorted.scanLeft(0)(_ + _).tail.takeWhile(_ <= target).length - 1
    (intervals.length to intervals.length - maxSolutionLen by -1).map(x => BigInt(x * 2)).product

def canSolveBruteForce(intervals: Array[Interval], target: Int) =
    calcProblemSize(intervals, target) < 500_000

def solveHeuristic(intervals: Array[Interval], adjBonuses: Array[Array[Double]], target: Int) =
    val maxSolutionLen = intervals.map(_.from).sorted.scanLeft(0)(_ + _).tail.takeWhile(_ <= target).length - 1
    val possibleChoices = intervals.length * 2
    val problemSize = (possibleChoices until (possibleChoices - maxSolutionLen * 2) by -2).map(BigInt(_)).product
    if problemSize < 500_000 then
        solveBruteForce(intervals, adjBonuses, target)
    else
        solveLocalSearch(intervals, adjBonuses, target)

// TODO: (style) simplify by specifying "from" and "to" or "width", and multiplying random.nextDouble by each width
val random = Random(1000000)
def generateIntervals(n: Int, maxWidth: Double) =
    val maxFrom = 5
    val minFrom = 2

    (1 to n).map(_ => {
        val from = minFrom + random.nextInt(maxFrom - minFrom) + random.nextDouble
        val width = maxWidth * random.nextDouble
        val to = from + from * width
        val relevance = random.nextDouble
        Interval((from * FPS).round.toInt, (to * FPS).round.toInt, relevance)
    }).toArray

val minTarget = 5
def solveWith(n: Int, targetFraction: Double, maxWidth: Double) =
    // val target = ((minTarget + random.nextInt(maxTarget - minTarget) + random.nextDouble()) * FPS).round.toInt
    val intervals = generateIntervals(n, maxWidth)
    val target = (intervals.map(_.to).sum * targetFraction).round.toInt
    val adjBonuses = (1 to n).map(i =>
        (1 to n).map(j =>
            if i == j then
                -1.0
            else
                (random.nextDouble * 2 - 1) * MAX_ADJ_BONUS
        ).toArray
    ).toArray

    if canSolveBruteForce(intervals, target) then
        val t0 = System.nanoTime()
        solveBruteForce(intervals, adjBonuses, target) match
            case Some(((_, ls), score, _)) =>
                println(s"brute force found: $ls | ${score / FPS} in ${(System.nanoTime() - t0) / 1_000_000}ms")
            case None =>
                println(s"brute force found no valid answers in ${(System.nanoTime() - t0) / 1_000_000}ms")
    else
        println("too large for brute force")

    var theBnbRes = Double.MaxValue
    val t1 = System.nanoTime()
    // try
        val (bnbSolution, bnbRes) = BranchAndBound.solve(intervals, adjBonuses, target, MAX_INTERVAL_BONUS, LAST_ADJ_MULT)
        theBnbRes = bnbRes
        println(s"$bnbRes (len = ${bnbSolution.length}) - branch and bound - solved for ${(System.nanoTime() - t1) / 1_000_000}ms")
    // catch
    //     case _ => println("B&B - Exception occurred")
    for
        slowerFuncs <- Seq(false, true)
        if !canSolveBruteForce(intervals, target) // TODO (style, PLEASE): wrong place for an if statement
        k <- Seq(3, 4, 5)
        if n > k
    do
        kToUse = k
        useSlowerLengthsFunc = slowerFuncs
        val t = System.nanoTime()
        val (solution, res) = solveLocalSearch(intervals, adjBonuses, target)
        println(s"$res (len = ${solution.length}) - local search (k = $kToUse | slowerFuncs = $useSlowerLengthsFunc) - solved for ${(System.nanoTime() - t) / 1_000_000.0}ms")
        if res - theBnbRes > 0.001 && solution.length > 1 then
            println("Trying again")
            val r = BranchAndBound.solveBranchAndBound(intervals, adjBonuses, target, MAX_INTERVAL_BONUS, LAST_ADJ_MULT, true)
            println(r)
            System.exit(0)

@main def run(): Unit =
    solveWith(
        n = 16,
        targetFraction = 0.5,
        maxWidth = 0.5
    )
    System.exit(0)

    for
        maxWidth <- Seq(1.0, 0.8, 0.6, 0.3, 0.1)
        // n <- Seq(1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12)
        n <- Seq(18)
        targetFraction <- Seq(0.1, 0.2, 0.4, 0.6, 0.8, 0.9)
    do
        val intervals = generateIntervals(n, maxWidth)
        val target = (intervals.map(_.to).sum * targetFraction).round.toInt
        val adjBonuses = (1 to n).map(i =>
            (1 to n).map(j =>
                if i == j then
                    -1.0
                else
                    (random.nextDouble * 2 - 1) * MAX_ADJ_BONUS
            ).toArray
        ).toArray
        val t = System.nanoTime()
        val (solution, score) = solveLocalSearch(intervals, adjBonuses, target)
        val msTaken = (System.nanoTime() - t) / 1_000_000.0
        val intervalsAsJS = "[" + intervals.map(i => s"{from: ${i.from}, to: ${i.to}, score: ${i.relevance}, choiceLen: ${i.choiceLen}}").mkString(",") + "]"
        val adjBonusesAsJS = "[" + adjBonuses.map(arr => "[" + arr.mkString(",") + "]").mkString(",") + "]"
        println(s"debugSolve($intervalsAsJS, $adjBonusesAsJS, $target, $score, \"${solution.mkString(",")}\", $msTaken)")
    System.exit(0)

    for
        maxIntervalBonus <- Seq(0.03, 0.01, 0.08)
        lastAdjMult <- Seq(1.2)
        maxAdjBonus <- Seq(0.5, 0.2, 1.1)
        maxWidth <- Seq(1.0, 0.6, 0.3, 0.1)
        n <- Seq(1, 2, 3, 4, 5, 5, 6, 7, 8, 9, 10, 11, 12, 10, 10)//, 15, 20, 25)
        targetFraction <- Seq(0.1, 0.2, 0.4, 0.6, 0.8)
        if targetFraction * n <= 12

        // maxIntervalBonus <- Seq(0.03, 0.01, 0.08)
        // lastAdjMult <- Seq(1.2, 1.1, 1.3)
        // maxAdjBonus <- Seq(0.65, 0.2, 1.2)
        // maxWidth <- Seq(1.0, 0.6, 0.3, 0.1, 0.05)
        // n <- Seq(5, 10, 15, 15, 20, 25, 30, 35)
        // targetFraction <- Seq(0.1, 0.2, 0.4, 0.4, 0.6, 0.8, 0.9)
    do
        println(s"solving with: maxIntervalBonus = $maxIntervalBonus | lastAdjMult = $lastAdjMult | maxAdjBonus = $maxAdjBonus | maxWidth = $maxWidth | n = $n | targetFraction = $targetFraction")
        MAX_INTERVAL_BONUS = maxIntervalBonus
        LAST_ADJ_MULT = lastAdjMult
        MAX_ADJ_BONUS = maxAdjBonus
        solveWith(
            n = n,
            targetFraction = targetFraction,
            maxWidth = maxWidth
        )
