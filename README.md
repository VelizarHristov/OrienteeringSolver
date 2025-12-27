Solves a problem similar to the "orienteering problem with variable profits".

There are two serious solvers: local search (faster but suboptimal) and branch and bound (optimal but less scalable). There is also brute force.

There's a JS version - main.js - which only performs local search. It was hand written for a friend.

# Problem statement
Input - `n` intervals, `n` x `n` adjBonuses, target.
- Each interval is of the form of [5, 20, 0.77] - min (int), max (int), relevance (number from 0.0 to 1.0)
- Each adjBonus is a number from -1.0 to 1.0
- `target` is an integer

Each interval can be taken as any value from min to max - for example if it is [5, 20, 0.77] then we can take 15 from it.

A valid solution takes a subset of intervals at values whose sum equals exactly `target`.

In an optimal solution, their order matters too. The objective is to maximize the sum of the scores of our selected intervals - its selected value is multiplied by its "relevance".

The relevance is defined as follows: the interval's relevance + its adjBonus.

The adjBonus is based on the current interval and the one following it. For example, if we have intervals [i, j, k] then the adjBonus for i = adjBonuses[i][j].

For our last interval, we define the adjBonus differently. We attempt to approximate the average adjBonus we'd normally get, thus we average the elements in adjBonuses (excluding the diagonal elements: adjBonuses[i][i] for all `i`), and then we multiply it by the constant LAST_ADJ_MULT, which can be configured. This is the adjBonus for our last element only. The idea is to keep LAST_ADJ_MULT above 1.0 because our algorithm will likely end up pairing our intervals so that they have better than average adj bonuses, and we want the last element to be comparable to the other ones. We do not want the last element to be less important, and to be a "dump element" where the worst interval gets put.

Finally, any intervals that we take at a full length are multiplied by (1 + MAX_INTERVAL_BONUS). MAX_INTERVAL_BONUS is a constant that we can freely modify. The goal here is to force the program to prefer fewer intervals with less truncating. (!) MAX_INTERVAL_BONUS should be non-negative, otherwise the program might not work.

Note that for all of our intervals but one, we will always choose either the min or max length, even if MAX_INTERVAL_BONUS is 0. This is because if we have at least two intervals at length between the min and max, then we should always reduce the length of the interval with a lower relevance to increase the length of an interval with a higher relevance, until we have only one left. This observation makes our search-space manageable.

# Parameters
This program has a few parameters that can be freely modified, which might make it give better results under some circumstances.
- MAX_INTERVAL_BONUS - how important entire intervals are. Causes the program to prefer solutions with fewer maxed intervals rather than more min-ed intervals.
- LAST_ADJ_MULT - how important the last node is, relative to the average node. Probably not worth messing with this, unless the average is negative. See text above for technical details.
- FPS - this should be determined by the resolution of your data. It determines how large integers to use.
- (Local search) kToUse - higher numbers make local search exponentially slower, but more accurate, with heavy diminishing returns.
- (Local search) useSlowerLengthsFunc - setting it to `true` makes local search slower, but more accurate.
- (Branch and bound) whichHeuristic - there are two options: heuristicInclExcl and heuristicFast. The first heuristic is slower but tighter.
- (Branch and bound) depthToUse - that is only for heuristicInclExcl - slows down exponentially (should be 2x per increment), but makes it more accurate. Currently it uses lower numbers the deeper in the search tree it gets. Higher values do not tend to do great.

# Data
The algorithms are assuming data where the intervals are wide (note: with sufficiently narrow intervals we might need exponential compute because it turns into the subset sum problem; however, I do not expect data where that is non trivial).

In Main.scala there is code that generates highly customizable synthetic data. That was used to test the algorithms and to improve them.

# Algorithms
## Local search
### Performance & solution quality
Compared with k=3 and k=4 and slowerFuncs at both settings - both of these settings did not seem to matter much. Scores were compared to the Branch & bound score, when the problem could be solved with Branch & bound.

- 150ms, 95.57% of optimal score with n = 14, k = 6
- 200ms, 95.56% of optimal score with n = 19, k = 10
- 450ms, 99.24% of optimal score with n = 22, k = 11
- 350ms, 94.50% of optimal score with n = 30, k = 10
- 850ms, 99.05% of optimal score with n = 16, k = 15
- 3000ms, unknown score with n = 32, k = 17
- 34.5s, unknown score with n = 36, k = 24

Of course, local search provides on lower bound to the quality of the solution. And in my experience, this implementation often provides suboptimal solutions, differing significantly but not too much below the optimal. 10-20% worse score in rare cases.
### Ideas for improvement
- Check out the TODO comment in its source code
- Try making a single step into an invalid state, and then the optimal step outside of it
- Try considering fewer moves, we are trying way too many options before we restart
- Explore a wider variety of moves

## Branch & bound
### Performance
Brute-force performance is `O(n! / k! * 2^k)`, and branch & bound sometimes feels like it scales similarly, even if less harshly. It would struggle when the optimal solution (`k`) is of size of 12 or more, and a larger `n` exacerbates that.

Some benchmarks with synthetic data, not necessarily representative because it varies plenty:
- 784ms with n = 14, k = 6
- 10.0s with n = 19, k = 10
- 51.6s with n = 22, k = 11
- 107.8s with n = 30, k = 10
- 102.1s with n = 16, k = 15

### Bugs
- Does not always provide the optimal solution, sometimes goes slightly suboptimal. There are two TODO comments in its source code that point out the bug responsible for this.
- Crashes if there is no solution.
### Ideas for improvement
- It is possible to improve its branch pruning by expanding its worst and best elements to be entire list and then looking for subsets of them to exchange, instead of only looking at the best & worst. Probably would not help much, though.
- Could be less generous with the MAX_INTERVAL_BONUS and the last adj multiplier in its heuristics, if those are high for your data.
- Can be parallelized.
### Failed attempt for O(n^2 * 2^n) approach
For the TSP (travelling salesman problem), there is the Held-Karp algorithm which is O(n^2 * 2^n), and it was possible to even implement this branching in the branch & bound algorithm (in my aTSP repo). So it makes sense to attempt something similar here.

Unfortunately, I could not find a solution. Things are much more complicated here, even if I removed the MAX_INTERVAL_BONUS and the adj bonus for the last element.

Recall that Held-Karp requires building up from subproblems whose number is O(2^n * n). That is, for given all possible ending nodes, and all possible subsets of the other nodes of size `k`, we can find the same for the size `k + 1` by trying all possible nodes to insert at the end of each, and the big saving comes from the fact that if solution 1 ended with `a` and had `b` in its subset, while solution 2 ended with `b` and contained `a` in the subset, and we try appending `c` to both, then we only need to take the one with the better score, the other sub-solution will never be useful for anything.

Here's an example which shows why it cannot be that simple: consider such a subproblem, with remaining length of 300. So far we have nodes a,b,c,d such that their differences between min and max are respectively 150,75,76,400 but d has very low relevance so we do not want to consider it for giving it extra score. It is possible to rearrange a,b,c so that a receives more at the expense of b and c, but that is only worth it if we put 150 extra points into a, and none into b or c. If we have 151 leftover points then we are better off putting then into b and c, but if we have 150 leftover points then we are better off putting them into a. But we do not yet know which one of the two will happen because that depends on the remaining nodes, and on how much remaining points they will leave us with. So we actually do not know which permutation of a,b,c is the best yet, we'd need to keep track of multiple permutations. If we kept track of which node is min and which is max then that's a factor of 2^n - if we have 8 nodes so far, we'd need to keep track of 2^8 possibilities - which is a lot.

Generally what often happens is that we cannot rule out subproblems because either a min/max combination, or a permutation, can be better or worse depending on whether we can get the exact sum to get the MAX_INTERVAL_BONUS, and checking for sums is 2^k operations.

Even if we removed MAX_INTERVAL_BONUS, it still seemed hard enough that I have given up on it - then we can keep all nodes at `min`, and assume that we will distribute the remaining by first pouring the max possible amount into the best relevance node that it still available, until we run out of nodes or points. But in that situation we still have to keep track of multiple options for converting score (aka `remaining`) into points (aka objective function value). At that point, I decided that branch & bound will do decent enough pruning without trying to get an asymptotically efficient algorithm.
