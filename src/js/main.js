// PARAMS - these can be tweaked

// bonus for the entire score if we are using an interval at its max length
const MAX_INTERVAL_BONUS = 0.03;
// how important adj bonus is relative to score - max score is 1.0
const MAX_ADJ_BONUS = 0.5;

// (not very worth tweaking - maybe try 1.1-1.6, but probably don't bother)
// a rough approximate of the average adj bonus of the optimal trip, divided by the average of all adj bonuses
const LAST_ADJ_MULT = 1.2;

// takes approximately 1ms per 1000
const MAX_BRUTEFORCE_SIZE = 500_000;

// used in local search - more is exponentially slower, but gives a better score
const K = 3;

function* permutations(arr) {
  if (arr.length <= 1) {
    yield arr;
  } else {
    for (let i = 0; i < arr.length; i++) {
      const rest = [...arr.slice(0, i), ...arr.slice(i + 1)];
      for (const perm of permutations(rest))
        yield [arr[i], ...perm];
    }
  }
}

// k = the size of the longest possible set of intervals that fits
// output is n!/k! * 2^k
function calcProblemSize(intervals, target) {
  const sorted = [...intervals].sort((a, b) => a.from - b.from);
  const maxPossible = intervals.map(i => i.to).reduce((a, b) => a + b);
  if (sorted[0].from > target || maxPossible < target) {
    return -1;
  }
  let maxSolutionLen = 0;
  while (target >= 0 && maxSolutionLen < sorted.length) {
    target -= sorted[maxSolutionLen].from;
    maxSolutionLen++;
  }
  // remove the last step - target should be >= 0
  if (target < 0)
    maxSolutionLen--;

  let problemSize = 1;
  for (let i = intervals.length; i > intervals.length - maxSolutionLen; i--)
    problemSize *= i * 2; // `i` choices, each at min or max

  return problemSize;
}

function getAdjBonusForLast(intervals, adjBonuses) {
  let adjBonusForLast = 0;
  if (intervals.length !== 1) {
    for (let i = 0; i < intervals.length; i++)
      for (let j = 0; j < intervals.length; j++)
        if (i != j)
          adjBonusForLast += adjBonuses[i][j];
    adjBonusForLast = (adjBonusForLast / (intervals.length * (intervals.length - 1))) * LAST_ADJ_MULT;
  }
  return adjBonusForLast;
}

function solveBruteForce(intervals, adjBonuses, target) {
  const adjBonusForLast = getAdjBonusForLast(intervals, adjBonuses);

  let allStates = [[]];
  let bestScore = -Number.MAX_VALUE;
  let bestState = {};
  while (allStates.length > 0) {
    const nextStates = [];
    for (let state of allStates) {
      let curLen = 0;
      let score = 0;
      for (let i = 0; i < state.length; i++) {
        const {id, isMaxed} = state[i];
        const effLen = isMaxed ? intervals[id].to * (1 + MAX_INTERVAL_BONUS) : intervals[id].from;
        const adjBonus = i == state.length - 1 ? adjBonusForLast : adjBonuses[id][state[i + 1].id];

        curLen += isMaxed ? intervals[id].to : intervals[id].from;
        score += effLen * (adjBonus + intervals[id].score);
      }
      const remainingLen = target - curLen;

      // handle all states that can terminate here
      for (let i = 0; i < state.length; i++) {
        const {id, isMaxed} = state[i];
        if (isMaxed || intervals[id].choiceLen < remainingLen)
          continue;
        const adjBonus = i == state.length - 1 ? adjBonusForLast : adjBonuses[id][state[i + 1].id];
        const efficiency = adjBonus + intervals[id].score;
        const newScore = score + remainingLen * efficiency;

        if (newScore > bestScore) {
          bestState = state.map(st => {
            let length;
            if (st.isMaxed)
              length = intervals[st.id].to;
            else
              length = intervals[st.id].from;
            if (st.id === id)
              length += remainingLen;
            return {...st, length}
          });
          bestScore = newScore;
        }
      }

      // generate all follow-up states
      const used = new Set(state.map(s => s.id));
      for (let idx = 0; idx < intervals.length; idx++)
        if (!used.has(idx))
          for (let max of [true, false])
            if (remainingLen >= (max ? intervals[idx].to : intervals[idx].from))
              nextStates.push([...state, {id: idx, isMaxed: max}]);
    }
    allStates = nextStates;
  }

  if (bestScore === -Number.MAX_VALUE)
    return null;
  else
    return {
      score: bestScore,
      state: bestState
    };
}

// Finds any feasible solution, ignoring any score, prefers returning intervals in sorted order.
// Theoretically O(2^n), - can be very slow if the intervals are very narrow (subset sum problem);
//   with our wide intervals it should be very fast.
function findFeasible(intervals, target, slack = 0) {
  if (slack > target)
    return [];
  if (intervals.length === 0)
    return null;
  
  const [{ from, choiceLen }, ...nextIntervals] = intervals;
  const newTarget = target - from;
  const newSlack = slack + choiceLen;
  
  let solution;
  if (newTarget < 0) {
    solution = findFeasible(nextIntervals, target, slack);
  } else {
    const withCurrent = findFeasible(nextIntervals, newTarget, newSlack);
    if (withCurrent !== null)
      solution = [-1, ...withCurrent];
    else
      solution = findFeasible(nextIntervals, target, slack);
  }
  
  if (solution === null)
    return null;
  else
    return solution.map(x => x + 1);
}

function solveLocalSearch(intervals, adjBonuses, target) {
  const adjBonusForLast = getAdjBonusForLast(intervals, adjBonuses);
  const intervalsByWidth = intervals.map((item, idx) => [item, idx])
    .sort((a, b) => b[0].choiceLen - a[0].choiceLen);
  const intervalIdxMapping = intervalsByWidth.map(item => item[1]);
  const initialSolutionShuffled = findFeasible(intervalsByWidth.map(item => item[0]), target);
  if (initialSolutionShuffled === null)
    return null;
  let curSolution = initialSolutionShuffled.map(idx => intervalIdxMapping[idx]);

  function efficiencies(solution) {
    return solution.map((_, i) => {
      const adjBonus = i === (solution.length - 1) ? adjBonusForLast : adjBonuses[solution[i]][solution[i + 1]];
      return intervals[solution[i]].score + adjBonus;
    });
  }

  function getBestLengths(solution, thisTarget = target) {
    const bestEffs = efficiencies(solution).map((item, idx) => [item, idx]).sort((a, b) => b[0] - a[0]);
    let spareLength = thisTarget - solution.map(i => intervals[i].from).reduce((a, b) => a + b);
    let i = 0;
    // taken at greater than `from`
    const extendedIntervals = [];
    while (spareLength > 0 && i < bestEffs.length) {
      const idx = solution[bestEffs[i][1]];
      spareLength -= intervals[idx].choiceLen;
      extendedIntervals.push(idx);
      i += 1;
    }
    const maxes = new Set(extendedIntervals.slice(0, -1));

    if (spareLength > 0) {
      // unsolvable
      return solution.map(_ => 0);
    } else {
      return solution.map(i => {
        if (maxes.has(i))
          return intervals[i].to;
        else if (extendedIntervals.at(-1) === i)
          return intervals[i].to + spareLength; // spareLength is a negative number
        else
          return intervals[i].from;
      });
    }
  }

  // TODO: also port getBestLengths2 (which is slower but better)
  //   and add a top-level constant that switches between them

  function solutionScore(solution, lengths) {
    const effs = efficiencies(solution);
    let sum = 0;
    for (let i = 0; i < solution.length; i++) {
      const maxBonus = lengths[i] === intervals[solution[i]].to ? (1 + MAX_INTERVAL_BONUS) : 1;
      sum += effs[i] * maxBonus * lengths[i];
    }
    return sum;
  }

  const simpleScoreMemo = {};
  function simpleScore(solution) {
    if (simpleScoreMemo[solution] !== undefined) {
      return simpleScoreMemo[solution];
    } else {
      let res = 0;
      const minIntervalLen = solution.map(i => intervals[i].from).reduce((a, b) => a + b);
      if (minIntervalLen <= target) {
        const lengths = getBestLengths(solution);
        res = solutionScore(solution, lengths);
      }
      simpleScoreMemo[solution] = res;
      return res;
    }
  }

  const kOpt = (k) => (solution) => {
    const initialScore = simpleScore(solution);

    function* partitions(k, skipped = 0) {
      if (k === 0)
        yield [solution.slice(skipped)];
      else
        for (let i = 1; i <= solution.length - skipped - k + 1; i++)
          for (const rest of partitions(k - 1, skipped + i))
            yield [solution.slice(skipped, skipped + i), ...rest];
    }

    for (const intervals of partitions(k))
      for (const permutation of permutations(intervals))
        if (simpleScore(permutation.flat()) > initialScore)
          return permutation.flat();


    return null;
  };

  const tryReplacing = (solution) => {
    const initialScore = simpleScore(solution);

    const remaining = [...intervals.keys()].filter(i => !solution.includes(i));
    for (let toAdd of remaining) {
      for (let toRemove = 0; toRemove < solution.length; toRemove++) {
        const newSolution = [...solution];
        newSolution[toRemove] = toAdd;
        if (simpleScore(newSolution) > initialScore)
          return newSolution;
      }
    }

    return null;
  }

  const tryAdding = (solution) => {
    const initialScore = simpleScore(solution);

    const remaining = [...intervals.keys()].filter(i => !solution.includes(i));
    for (let toAdd of remaining) {
      for (let toSkip = 0; toSkip <= solution.length; toSkip++) {
        const newSolution = solution.slice(0, toSkip).concat([toAdd]).concat(solution.slice(toSkip));
        if (simpleScore(newSolution) > initialScore)
          return newSolution;
      }
    }

    return null;
  }

  const funcs = [kOpt(K), tryReplacing, tryAdding];
  let halt = false;
  while(!halt) {
    halt = true;
    for (let func of funcs) {
      const res = func(curSolution);
      if (res !== null) {
        curSolution = res;
        halt = false;
        break;
      }
    }
  }

  return {
    score: simpleScore(curSolution) / 120,
    state: curSolution
  };
}

function solve(intervals, adjBonuses, target) {
  const sz = calcProblemSize(intervals, target);
  if (sz == -1) {
    return "Error: unsolvable (trivially)";
  } else if (sz < MAX_BRUTEFORCE_SIZE) {
    const res = solveBruteForce(intervals, adjBonuses, target);
    if (res === null)
      return "Error: unsolvable";
  } else {
    const res = findFeasible(intervals, target);
    if (res === null)
      return "Error: unsolvable";
    // TODO: transform the output to return intervals with a selected length for each
    return res;
  }
}

const FRAMING_CATEGORIES = {
  EXTREME_CLOSE_UP: 'ECU',
  CLOSE_UP: 'CU',
  MEDIUM_CLOSE_UP: 'MCU',
  MEDIUM_SHOT: 'MS',
  MEDIUM_LONG_SHOT: 'MLS',
  LONG_SHOT: 'LS',
  WIDE_SHOT: 'WS',
  UNKNOWN: 'UNK',
  EXTREME_LONG_SHOT: 'ELS'
};
const lettersToFraming = Object.fromEntries(Object.entries(FRAMING_CATEGORIES).map(([k, v]) => [v, k]));

const FRAMING_TRANSITION_REWARD = {
  EXTREME_CLOSE_UP: {
    EXTREME_CLOSE_UP: 0.6,
    CLOSE_UP: 0.8,
    MEDIUM_CLOSE_UP: 0.5,
    MEDIUM_SHOT: 0.1,
    MEDIUM_LONG_SHOT: -0.2,
    LONG_SHOT: -0.5,
    WIDE_SHOT: -0.7,
    EXTREME_LONG_SHOT: -0.9,
    UNKNOWN: 0.0,
  },
  CLOSE_UP: {
    EXTREME_CLOSE_UP: 0.7,
    CLOSE_UP: 0.6,
    MEDIUM_CLOSE_UP: 0.8,
    MEDIUM_SHOT: 0.4,
    MEDIUM_LONG_SHOT: 0.1,
    LONG_SHOT: -0.3,
    WIDE_SHOT: -0.6,
    EXTREME_LONG_SHOT: -0.8,
    UNKNOWN: 0.0,
  },
  MEDIUM_CLOSE_UP: {
    EXTREME_CLOSE_UP: 0.3,
    CLOSE_UP: 0.7,
    MEDIUM_CLOSE_UP: 0.6,
    MEDIUM_SHOT: 0.8,
    MEDIUM_LONG_SHOT: 0.4,
    LONG_SHOT: 0.0,
    WIDE_SHOT: -0.4,
    EXTREME_LONG_SHOT: -0.6,
    UNKNOWN: 0.0,
  },
  MEDIUM_SHOT: {
    EXTREME_CLOSE_UP: -0.2,
    CLOSE_UP: 0.3,
    MEDIUM_CLOSE_UP: 0.7,
    MEDIUM_SHOT: 0.6,
    MEDIUM_LONG_SHOT: 0.7,
    LONG_SHOT: 0.3,
    WIDE_SHOT: 0.0,
    EXTREME_LONG_SHOT: -0.4,
    UNKNOWN: 0.0,
  },
  MEDIUM_LONG_SHOT: {
    EXTREME_CLOSE_UP: -0.4,
    CLOSE_UP: -0.1,
    MEDIUM_CLOSE_UP: 0.4,
    MEDIUM_SHOT: 0.7,
    MEDIUM_LONG_SHOT: 0.6,
    LONG_SHOT: 0.8,
    WIDE_SHOT: 0.5,
    EXTREME_LONG_SHOT: 0.0,
    UNKNOWN: 0.0,
  },
  LONG_SHOT: {
    EXTREME_CLOSE_UP: -0.6,
    CLOSE_UP: -0.3,
    MEDIUM_CLOSE_UP: 0.0,
    MEDIUM_SHOT: 0.5,
    MEDIUM_LONG_SHOT: 0.8,
    LONG_SHOT: 0.6,
    WIDE_SHOT: 0.7,
    EXTREME_LONG_SHOT: 0.3,
    UNKNOWN: 0.0,
  },
  WIDE_SHOT: {
    EXTREME_CLOSE_UP: -0.8,
    CLOSE_UP: -0.5,
    MEDIUM_CLOSE_UP: -0.2,
    MEDIUM_SHOT: 0.3,
    MEDIUM_LONG_SHOT: 0.6,
    LONG_SHOT: 0.8,
    WIDE_SHOT: 0.5,
    EXTREME_LONG_SHOT: 0.7,
    UNKNOWN: 0.0,
  },
  EXTREME_LONG_SHOT: {
    EXTREME_CLOSE_UP: -1.0,
    CLOSE_UP: -0.7,
    MEDIUM_CLOSE_UP: -0.5,
    MEDIUM_SHOT: -0.2,
    MEDIUM_LONG_SHOT: 0.2,
    LONG_SHOT: 0.6,
    WIDE_SHOT: 0.8,
    EXTREME_LONG_SHOT: 0.7,
    UNKNOWN: 0.0,
  },
  UNKNOWN: {
    EXTREME_CLOSE_UP: 0.0,
    CLOSE_UP: 0.0,
    MEDIUM_CLOSE_UP: 0.0,
    MEDIUM_SHOT: 0.0,
    MEDIUM_LONG_SHOT: 0.0,
    LONG_SHOT: 0.0,
    WIDE_SHOT: 0.0,
    EXTREME_LONG_SHOT: 0.0,
    UNKNOWN: 0.0,
  },
};

function solveWrapper(durations, desiredDuration) {
  const intervals = durations.map(duration => {
    const [from, to] = duration.bounds;
    return {
      from,
      to,
      choiceLen: to - from,
      score: duration.alternative.score
    };
  });

  const adjBonuses = durations.map(duration =>
    durations.map(duration2 =>
      FRAMING_TRANSITION_REWARD[
        lettersToFraming[duration.alternative.framing ?? "UNK"]][
        lettersToFraming[duration2.alternative.framing ?? "UNK"]]
    )
  );

  return solve(intervals, adjBonuses, desiredDuration);
}

function debugSolve(intervals, adjBonuses, target, scalaScore, scalaSolution, scalaMs) {
  const startTime = performance.now();
  let solveRes = {state: "N/A", score: "N/A"};
  solveRes = solveLocalSearch(intervals, adjBonuses, target);
  // if (sz < 30_000_000)
  //   solveRes = solveBruteForce(intervals, adjBonuses, target);
  const timeTaken = performance.now() - startTime;
  console.log(`solution Scala: ${scalaSolution} | JS: ${JSON.stringify(solveRes.state)}`);
  console.log(`solution score Scala: ${scalaScore} | JS: ${solveRes.score}`);
  console.log(`time taken Scala: ${scalaMs}ms | JS: ${timeTaken}ms`);
}
