var manager = "manager";
var player = "hail_mary_persistent";

var role = "robot";
var rules = [];
var startclock = 10;
var playclock = 10;

var library = [];
var roles = [];
var state = [];

//==============================================================================
// Persistent-tree minimax search with exploration/exploitation selection
//==============================================================================

var root = null;
var rootSignature = "";
var deadline = 0;

var maxExpansionsPerMove = 2500;
var safetyMs = 800;
var selectionC = 18.0;

var expansions = 0;
var reusedRoot = false;
var transpositionTable = {};
var ttHits = 0;
var ttStores = 0;
var historyScore = {};

var sampleMaxDepth = 30;
var sampleMaxLegal = 1;
var samplePlayouts = 0;
var sampleStateCount = 0;
var sampleTerminalCount = 0;
var sampleTerminalRewardSum = 0;
var sampleAvgTerminalReward = 50;
var sampleTerminalRate = 0;
var sampleFeatureCount = 0;
var sampleRewardSum = 0;
var sampleRewardSqSum = 0;
var sampleMobilitySum = 0;
var sampleMobilitySqSum = 0;
var rewardHeuristicWeight = 0.35;
var payoffStability = 0.35;
var controlStability = 0.65;

function ping() {
  return "ready";
}

function start(r, rs, sc, pc) {
  role = r;
  rules = rs.slice(1);
  startclock = numberize(sc);
  playclock = numberize(pc);
  library = definemorerules([], rs.slice(1));
  roles = findroles(library);
  state = findinits(library);
  transpositionTable = {};
  ttHits = 0;
  ttStores = 0;
  historyScore = {};

  root = makeNode(state, null, null);
  rootSignature = stateKey(state);
  buildSamplingModel();

  console.log(
    "[persistent_tree] start role=" +
      role +
      " playclock=" +
      playclock +
      " samples=" +
      samplePlayouts +
      " avgReward=" +
      sampleAvgTerminalReward +
      " rewardWeight=" +
      rewardHeuristicWeight +
      " expansionsCap=" +
      maxExpansionsPerMove
  );
  return "ready";
}

function play(move) {
  if (move !== nil) {
    state = simulate(move, state, library);
  }

  if (findcontrol(state, library) !== role) {
    return false;
  }

  syncRootToState(state);
  if (!root) {
    root = makeNode(state, null, null);
    rootSignature = stateKey(state);
  }

  var actions = findlegals(state, library);
  if (actions.length === 0) {
    return false;
  }
  if (actions.length === 1) {
    return actions[0];
  }

  var immediateWin = findImmediateWinningAction(actions, state);
  if (immediateWin !== null) {
    console.log("[persistent_tree] taking immediate win " + grind(immediateWin));
    return immediateWin;
  }

  return playPersistentMinimax(role);
}

function stop(move) {
  return false;
}

function abort() {
  return false;
}

function playPersistentMinimax(role) {
  deadline = Date.now() + Math.max(100, playclock * 1000 - safetyMs);
  expansions = 0;
  reusedRoot = true;

  while (expansions < maxExpansionsPerMove && Date.now() <= deadline) {
    if (root.solved) {
      break;
    }
    var leaf = selectNodeForExpansion(root);
    if (!leaf) {
      break;
    }
    expandSingleAction(leaf, role);
    expansions = expansions + 1;
  }

  var bestAction = bestActionFromRoot(root);
  if (bestAction === null) {
    var fallback = findlegals(state, library);
    bestAction = fallback.length > 0 ? fallback[0] : false;
  }

  console.log(
    "[persistent_tree] expansions=" +
      expansions +
      " rootVisits=" +
      root.visits +
      " rootValue=" +
      root.value +
      " rootChildren=" +
      root.children.length +
      " ttSize=" +
      Object.keys(transpositionTable).length +
      " ttHits=" +
      ttHits +
      " bestAction=" +
      grind(bestAction)
  );
  return bestAction;
}

function findImmediateWinningAction(actions, currentState) {
  for (var i = 0; i < actions.length; i++) {
    var nextState = simulate(actions[i], currentState, library);
    if (findterminalp(nextState, library)) {
      var reward = findreward(role, nextState, library) * 1;
      if (reward === 100) {
        return actions[i];
      }
    }
  }
  return null;
}

function selectNodeForExpansion(start) {
  var node = start;
  while (true) {
    if (!node.expanded) {
      initializeExpansion(node);
    }
    if (node.solved) {
      return null;
    }
    if (node.terminal) {
      return node;
    }
    if (node.unexpandedActions.length > 0) {
      return node;
    }
    if (node.children.length === 0) {
      return node;
    }
    node = chooseChildByTreePolicy(node);
    if (!node) {
      return null;
    }
  }
}

function expandSingleAction(node, role) {
  if (node.terminal) {
    backupMinimax(node, role);
    return;
  }

  if (!node.expanded) {
    initializeExpansion(node);
  }

  if (node.unexpandedActions.length === 0) {
    backupMinimax(node, role);
    return;
  }

  var action = node.unexpandedActions.pop();
  var nextState = simulate(action, node.state, library);
  var child = makeNode(nextState, node, action);
  node.children.push(child);

  initializeExpansion(child);
  updateHistoryScore(node, action, child);
  backupMinimax(child, role);
}

function initializeExpansion(node) {
  if (node.expanded) {
    return;
  }
  node.expanded = true;
  node.terminal = findterminalp(node.state, library);
  node.actor = findcontrol(node.state, library);

  if (node.terminal) {
    node.value = terminalOrHeuristic(role, node.state);
    node.solved = true;
    node.solvedValue = node.value;
    node.unexpandedActions = [];
    storeTransposition(node);
    return;
  }

  var actions = shuffle(findlegals(node.state, library).slice(0));
  // History heuristic: pop() takes the last action, so sort weakest to strongest.
  actions.sort(function(a, b) {
    return historyValue(a) - historyValue(b);
  });
  node.unexpandedActions = actions;

  if (actions.length === 0) {
    node.value = terminalOrHeuristic(role, node.state);
  } else {
    node.value = heuristicEval(role, node.state);
  }
  storeTransposition(node);
}

function chooseChildByTreePolicy(node) {
  var best = null;
  var bestScore = -1000000;
  var parentVisits = Math.max(1, node.visits);

  for (var i = 0; i < node.children.length; i++) {
    var child = node.children[i];
    if (child.solved) {
      continue;
    }
    if (child.visits === 0) {
      return child;
    }
    var averageUtility = child.utility / child.visits;
    var exploitation =
      node.actor === role ? averageUtility : 100 - averageUtility;
    var score =
      exploitation +
      selectionC * Math.sqrt(Math.log(parentVisits) / child.visits);

    if (score > bestScore) {
      bestScore = score;
      best = child;
    }
  }
  return best;
}

function backupMinimax(node, role) {
  var current = node;
  while (current !== null) {
    current.visits = current.visits + 1;

    if (current.terminal) {
      current.value = terminalOrHeuristic(role, current.state);
    } else if (current.children.length > 0) {
      current.value = minimaxChildValue(current);
    } else {
      current.value = heuristicEval(role, current.state);
    }

    updateSolvedStatus(current);
    if (current.solved) {
      current.value = current.solvedValue;
    }
    current.utility = current.utility + current.value;
    storeTransposition(current);
    current = current.parent;
  }
}

function updateSolvedStatus(node) {
  if (node.terminal) {
    node.solved = true;
    node.solvedValue = terminalOrHeuristic(role, node.state);
    return;
  }

  if (node.children.length === 0) {
    node.solved = false;
    node.solvedValue = null;
    return;
  }

  var i = 0;
  var allChildrenSolved = true;
  var allChildrenWin100 = true;
  var anyChildWin100 = false;
  var allChildrenLoss0 = true;
  var anyChildLoss0 = false;

  for (i = 0; i < node.children.length; i++) {
    var child = node.children[i];
    if (!child.solved) {
      allChildrenSolved = false;
      allChildrenWin100 = false;
      allChildrenLoss0 = false;
      continue;
    }
    if (child.solvedValue === 100) {
      anyChildWin100 = true;
    } else {
      allChildrenWin100 = false;
    }
    if (child.solvedValue === 0) {
      anyChildLoss0 = true;
    } else {
      allChildrenLoss0 = false;
    }
  }

  // Early proofs:
  // - At MAX nodes (our turn), one solved 100 child proves a forced win.
  // - At MIN nodes (opponent turn), one solved 0 child proves they can force our loss.
  if (node.actor === role && anyChildWin100) {
    node.solved = true;
    node.solvedValue = 100;
    return;
  }
  if (node.actor !== role && anyChildLoss0) {
    node.solved = true;
    node.solvedValue = 0;
    return;
  }

  // If there are still unexpanded actions, outcomes not covered by current
  // children remain unknown and we cannot mark this node solved (except terminal
  // and the early forced-outcome proofs above).
  if (node.unexpandedActions.length > 0) {
    node.solved = false;
    node.solvedValue = null;
    return;
  }

  // With full expansion, solved minimax value is exact when all children solved.
  if (allChildrenSolved) {
    node.solved = true;
    node.solvedValue = minimaxChildValue(node);
    return;
  }

  // Strong opponent/all-branch proofs require all solved children.
  if (node.actor === role && allChildrenLoss0) {
    node.solved = true;
    node.solvedValue = 0;
    return;
  }
  if (node.actor !== role && allChildrenWin100) {
    node.solved = true;
    node.solvedValue = 100;
    return;
  }

  node.solved = false;
  node.solvedValue = null;
}

function minimaxChildValue(node) {
  var best = node.actor === role ? 0 : 100;
  for (var i = 0; i < node.children.length; i++) {
    var value = node.children[i].value;
    if (node.actor === role) {
      if (value > best) {
        best = value;
      }
    } else {
      if (value < best) {
        best = value;
      }
    }
  }
  return best;
}

function bestActionFromRoot(root) {
  if (!root || root.children.length === 0) {
    return null;
  }

  // If we have a proven forced win from root, always take it.
  for (var j = 0; j < root.children.length; j++) {
    var forced = root.children[j];
    if (forced.solved && forced.solvedValue === 100) {
      return forced.actionFromParent;
    }
  }

  var bestChild = null;
  var bestValue = -1;
  for (var i = 0; i < root.children.length; i++) {
    var child = root.children[i];
    if (child.value > bestValue) {
      bestValue = child.value;
      bestChild = child;
    }
  }
  return bestChild ? bestChild.actionFromParent : null;
}

function syncRootToState(currentState) {
  var key = stateKey(currentState);
  if (root && rootSignature === key) {
    return;
  }

  if (root && root.children.length > 0) {
    for (var i = 0; i < root.children.length; i++) {
      var child = root.children[i];
      if (child.key === key) {
        root = child;
        root.parent = null;
        root.actionFromParent = null;
        rootSignature = key;
        return;
      }
    }
  }

  // Could not match an existing subtree after the observed transition; reset.
  root = makeNode(currentState, null, null);
  rootSignature = key;
  reusedRoot = false;
}

function makeNode(st, parent, actionFromParent) {
  var node = {
    state: st,
    key: stateKey(st),
    parent: parent,
    actionFromParent: actionFromParent,
    actor: null,
    terminal: false,
    expanded: false,
    visits: 0,
    utility: 0,
    value: 50,
    solved: false,
    solvedValue: null,
    children: [],
    unexpandedActions: []
  };
  hydrateFromTransposition(node);
  return node;
}

function hydrateFromTransposition(node) {
  var cached = transpositionTable[node.key];
  if (!cached) {
    return;
  }
  ttHits = ttHits + 1;
  node.visits = cached.visits;
  node.utility = cached.utility;
  node.value = cached.value;
  node.solved = cached.solved;
  node.solvedValue = cached.solvedValue;
  node.terminal = cached.terminal;
}

function storeTransposition(node) {
  transpositionTable[node.key] = {
    visits: node.visits,
    utility: node.utility,
    value: node.value,
    solved: node.solved,
    solvedValue: node.solvedValue,
    terminal: node.terminal
  };
  ttStores = ttStores + 1;
}

function buildSamplingModel() {
  var samplingDeadline = Date.now() + Math.max(100, startclock * 1000 - 1200);
  sampleMaxLegal = 1;
  samplePlayouts = 0;
  sampleStateCount = 0;
  sampleTerminalCount = 0;
  sampleTerminalRewardSum = 0;
  sampleAvgTerminalReward = 50;
  sampleTerminalRate = 0;
  sampleFeatureCount = 0;
  sampleRewardSum = 0;
  sampleRewardSqSum = 0;
  sampleMobilitySum = 0;
  sampleMobilitySqSum = 0;
  rewardHeuristicWeight = 0.35;

  while (Date.now() < samplingDeadline) {
    runRandomSamplePlayout();
  }

  if (sampleTerminalCount > 0) {
    sampleAvgTerminalReward = Math.round(
      sampleTerminalRewardSum / sampleTerminalCount
    );
  }
  if (sampleStateCount > 0) {
    sampleTerminalRate = sampleTerminalCount / sampleStateCount;
  }
  estimateRewardSignalWeight();
}

function runRandomSamplePlayout() {
  var sampleState = findinits(library);

  for (var depth = 0; depth < sampleMaxDepth; depth++) {
    sampleStateCount = sampleStateCount + 1;

    if (findterminalp(sampleState, library)) {
      sampleTerminalCount = sampleTerminalCount + 1;
      sampleTerminalRewardSum =
        sampleTerminalRewardSum + findreward(role, sampleState, library) * 1;
      samplePlayouts = samplePlayouts + 1;
      return;
    }

    var actions = findlegals(sampleState, library);
    if (actions.length > sampleMaxLegal) {
      sampleMaxLegal = actions.length;
    }
    recordSampleFeatures(sampleState, actions.length);
    if (actions.length === 0) {
      samplePlayouts = samplePlayouts + 1;
      return;
    }

    var action = actions[Math.floor(Math.random() * actions.length)];
    sampleState = simulate(action, sampleState, library);
  }

  samplePlayouts = samplePlayouts + 1;
}

function recordSampleFeatures(sampleState, legalCount) {
  var reward = findreward(role, sampleState, library) * 1;
  sampleFeatureCount = sampleFeatureCount + 1;
  sampleRewardSum = sampleRewardSum + reward;
  sampleRewardSqSum = sampleRewardSqSum + reward * reward;
  sampleMobilitySum = sampleMobilitySum + legalCount;
  sampleMobilitySqSum = sampleMobilitySqSum + legalCount * legalCount;
}

function estimateRewardSignalWeight() {
  if (sampleFeatureCount <= 1) {
    rewardHeuristicWeight = 0.35;
    return;
  }

  var rewardMean = sampleRewardSum / sampleFeatureCount;
  var rewardVariance =
    sampleRewardSqSum / sampleFeatureCount - rewardMean * rewardMean;
  var mobilityMean = sampleMobilitySum / sampleFeatureCount;
  var mobilityVariance =
    sampleMobilitySqSum / sampleFeatureCount - mobilityMean * mobilityMean;

  var rewardSignal = Math.sqrt(Math.max(0, rewardVariance)) / 100;
  var mobilitySignal =
    Math.sqrt(Math.max(0, mobilityVariance)) / Math.max(1, sampleMaxLegal);
  var signalRatio = rewardSignal / (rewardSignal + mobilitySignal + 0.001);

  // Keep some generic heuristic influence, but trust reward heavily when it
  // varies meaningfully across sampled states.
  rewardHeuristicWeight = clampUnit(0.2 + 0.75 * signalRatio);
}

function updateHistoryScore(parent, action, child) {
  var key = actionKey(action);
  var delta = 0;

  if (parent.actor === role) {
    delta = child.value - 50;
  } else {
    delta = 50 - child.value;
  }

  // Boost proven tactical outcomes to prioritize them quickly in future searches.
  if (child.solved && child.solvedValue === 100) {
    delta = delta + (parent.actor === role ? 25 : -25);
  } else if (child.solved && child.solvedValue === 0) {
    delta = delta + (parent.actor === role ? -25 : 25);
  }

  historyScore[key] = historyValue(action) + delta;
}

function historyValue(action) {
  var key = actionKey(action);
  var value = historyScore[key];
  if (typeof value === "number") {
    return value;
  }
  return 0;
}

function actionKey(action) {
  return grind(action);
}

function terminalOrHeuristic(role, state) {
  if (findterminalp(state, library)) {
    return findreward(role, state, library) * 1;
  }
  return heuristicEval(role, state);
}

function heuristicEval(role, state) {
  var active = findcontrol(state, library);
  var legalMoves = findlegals(state, library).length;
  var mobilityRatio = Math.min(1, legalMoves / Math.max(1, sampleMaxLegal));

  var rawReward = findreward(role, state, library) * 1;
  var payoff = rawReward;
  if (payoff === 0 && sampleTerminalCount > 0 && rewardHeuristicWeight < 0.5) {
    payoff = Math.round(0.4 * payoff + 0.6 * sampleAvgTerminalReward);
  }

  var control = active === role ? mobilityRatio : -mobilityRatio;
  var terminalLikelihood = clampUnit(
    sampleTerminalRate + (1 - mobilityRatio) * 0.25
  );

  var value =
    terminalLikelihood * payoff +
    (1 - terminalLikelihood) *
      ((50 + 50 * control) * controlStability + payoffStability * payoff);

  return clampScore(
    Math.round(rewardHeuristicWeight * rawReward + (1 - rewardHeuristicWeight) * value)
  );
}

function clampScore(v) {
  if (v < 0) {
    return 0;
  }
  if (v > 100) {
    return 100;
  }
  return v;
}

function clampUnit(v) {
  if (v < 0) {
    return 0;
  }
  if (v > 1) {
    return 1;
  }
  return v;
}

function stateKey(st) {
  return JSON.stringify(st);
}

function shuffle(array) {
  for (var i = array.length - 1; i > 0; i--) {
    var j = Math.floor(Math.random() * (i + 1));
    var temp = array[i];
    array[i] = array[j];
    array[j] = temp;
  }
  return array;
}

//==============================================================================
// End of player code
//==============================================================================
