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

function solveBruteForce(intervals, adjBonuses, target) {
  let adjBonusForLast = 0;
  if (intervals.length !== 1) {
    for (let i = 0; i < intervals.length; i++)
      for (let j = 0; j < intervals.length; j++)
        if (i != j)
          adjBonusForLast += adjBonuses[i][j];
    adjBonusForLast = (adjBonusForLast / (intervals.length * (intervals.length - 1))) * LAST_ADJ_MULT;
  }

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
    return "Error: unsolvable";
  else
    return {
      score: bestScore,
      state: bestState
    };
}

function solve(intervals, adjBonuses, target) {
  const sz = calcProblemSize(intervals, target);
  if (sz == -1) {
    return "Error: unsolvable (trivially)";
  } else if (sz < MAX_BRUTEFORCE_SIZE) {
    return solveBruteForce(intervals, adjBonuses, target);
  } else {
    // TODO: solve with a faster method
    return "Error: problem too large - TODO: solve with a faster method";
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

  const lettersToFraming = Object.fromEntries(Object.entries(FRAMING_CATEGORIES).map(([k, v]) => [v, k]));
  const adjBonuses = durations.map(duration =>
    durations.map(duration2 =>
      FRAMING_TRANSITION_REWARD[
        lettersToFraming[duration.alternative.framing ?? "UNK"]][
        lettersToFraming[duration2.alternative.framing ?? "UNK"]]
    )
  );

  solve(intervals, adjBonuses, desiredDuration);
}

function debugSolve(intervals, adjBonuses, target, scalaProblemSize, scalaScore, scalaSolution, scalaMs) {
  const sz = calcProblemSize(intervals, target);
  console.log(`problemSize Scala: ${scalaProblemSize} | JS: ${sz}`);
  const startTime = performance.now();
  let solveRes = {state: "N/A", score: "N/A"};
  if (sz < 30_000_000)
    solveRes = solveBruteForce(intervals, adjBonuses, target);
  const timeTaken = performance.now() - startTime;
  console.log(`solution Scala: ${scalaSolution} | JS: ${JSON.stringify(solveRes.state)}`);
  console.log(`solution score Scala: ${scalaScore} | JS: ${solveRes.score}`);
  console.log(`time taken Scala: ${scalaMs}ms | JS: ${timeTaken}ms`);
}
