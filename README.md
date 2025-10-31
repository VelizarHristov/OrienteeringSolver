Solves a problem similar to the "orienteering problem with variable profits".

I implement it in Scala because I like it a lot more than JS, then I translate it to JS since I have a friend who uses that.

Repo needs some cleanup right now.

Upcoming (later than 5th January 2026):
- better summary of what this repo does (solver for NP-hard problem)
- exact problem definition (roughly: we have `n` intervals, each with `from`, `to`, `score`; each interval we either do not take at all, or we pay somewhere from its `from` value to its `to` value; the sum of what we must pay must exactly equal a given number; we also have an `n` x `n` input which says, if interval `i` is before interval `j`, then its score is increased by the number in it; we multiply the final score by how much we took from the interval, and we must maximize this sum; if we took from the interval exactly `to`, then there is a percentage bonus on the entire interval's score; the last interval does not have a next node, so we calculate a specific number which adjusts its score; `from`, `to`, and the target length are integers; `score` is from 0.0 to 1.0; the entries in the matrix are from -1.0 to 1.0, but they are all multiplied by a constant in order to weight its importance relative to the score.)
- explanation of my branch & bound algorithm, and especially some things that were tried for it but failed (I still need to try a new heuristic, after I do I'll delete all of the failed heuristics); also one of its branch pruning techniques can be improved
- general cleanup, most of it is very minor refactoring, but some would ensure correctness in some corner cases, especially in branch & bound
