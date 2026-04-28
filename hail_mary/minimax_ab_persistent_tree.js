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

  root = makeNode(state, null, null);
  rootSignature = stateKey(state);

  console.log(
    "[persistent_tree] start role=" +
      role +
      " playclock=" +
      playclock +
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

  var selected = playPersistentMinimax(role);
  return selected;
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
      " bestAction=" +
      grind(bestAction)
  );
  return bestAction;
}

function selectNodeForExpansion(start) {
  var node = start;
  while (true) {
    if (!node.expanded) {
      initializeExpansion(node);
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
    return;
  }

  var actions = shuffle(findlegals(node.state, library).slice(0));
  node.unexpandedActions = actions;

  if (actions.length === 0) {
    node.value = terminalOrHeuristic(role, node.state);
  } else {
    node.value = heuristicEval(role, node.state);
  }
}

function chooseChildByTreePolicy(node) {
  var best = null;
  var bestScore = -1000000;
  var parentVisits = Math.max(1, node.visits);

  for (var i = 0; i < node.children.length; i++) {
    var child = node.children[i];
    if (child.visits === 0) {
      return child;
    }
    var score =
      child.utility / child.visits +
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

  // If there are still unexpanded actions, outcomes not covered by current
  // children remain unknown and we cannot mark this node solved (except terminal).
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
      if (stateKey(child.state) === key) {
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
  return {
    state: st,
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
}

function terminalOrHeuristic(role, state) {
  if (findterminalp(state, library)) {
    return findreward(role, state, library) * 1;
  }
  return heuristicEval(role, state);
}

function heuristicEval(role, state) {
  var reward = findreward(role, state, library) * 1;
  var active = findcontrol(state, library);
  var legalMoves = findlegals(state, library).length;
  var scaledMobility = Math.min(100, legalMoves * 10);
  var mobility = active === role ? scaledMobility : 100 - scaledMobility;
  return clampScore(Math.round(0.7 * reward + 0.3 * mobility));
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
