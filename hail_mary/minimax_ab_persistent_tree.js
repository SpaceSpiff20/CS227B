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
    current.utility = current.utility + current.value;
    current = current.parent;
  }
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
