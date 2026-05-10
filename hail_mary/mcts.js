var manager = "manager";
var player = "hail_mary_mcts";

var role = "robot";
var rules = [];
var startclock = 10;
var playclock = 10;

var library = [];
var roles = [];
var state = [];
var tree = null;
var safetyMs = 1000;
var pendingMove = null;

//==============================================================================

function ping() { return "ready"; }

function start(r, rs, sc, pc) {
  role = r;
  rules = rs.slice(1);
  startclock = numberize(sc);
  playclock = numberize(pc);
  library = definemorerules([], rs.slice(1));
  roles = findroles(library);
  state = findinits(library);
  tree = makenode(state, null);
  pendingMove = null;
  console.log("[mcts] start role=" + role + " startclock=" + startclock + " playclock=" + playclock);
  return "ready";
}

function play(move) {
  syncstate(move);
  if (findcontrol(state, library) !== role) { return false; }
  var returnDeadline = Date.now() + Math.max(100, playclock * 1000 - safetyMs);
  var searchDeadline = Math.max(Date.now(), returnDeadline - 200);
  var primeBudgetMs = Math.max(75, Math.floor((playclock * 1000 - safetyMs) * 0.15));
  var primeDeadline = Math.min(searchDeadline, Date.now() + primeBudgetMs);
  primeroot(tree, primeDeadline);
  var iterations = 0;
  while (Date.now() < searchDeadline && !tree.solved) {
    iterate(tree, searchDeadline);
    iterations++;
  }
  var result = selectaction(tree, returnDeadline);
  console.log("[mcts] iterations=" + iterations + " move=" + grind(result.action) + " score=" + result.score);
  pendingMove = result.action;
  return result.action;
}

function syncstate(move) {
  if (pendingMove !== null) {
    var previousPending = pendingMove;
    advancetree(previousPending);
    pendingMove = null;
    if (move !== nil && equalp(move, previousPending)) { return; }
  }
  if (move !== nil) {
    advancetree(move);
  }
}

function advancetree(move) {
  tree = subtree(move, tree);
  state = tree.state;
}

function stop(move) { return false; }
function abort() { return false; }

//==============================================================================
// Node
//==============================================================================

// C is the UCB exploration constant. Scores are 0-100, so C=70 gives roughly
// equal weight to exploitation and exploration early in search.
var C = 70;

function makenode(state, parent) {
  return {
    state: state,
    parent: parent,
    actions: null,   // null means not yet expanded
    children: [],
    visits: 0,
    score: 0,
    mover: findcontrol(state, library),
    solved: false,
    solvedValue: null,
    tacticalKnown: false,
    isImmediateWin: false,
    allowsImmediateLoss: false
  };
}

//==============================================================================
// One MCTS iteration: selection -> expansion -> simulation -> backpropagation
//==============================================================================

function timeup(deadline) {
  return deadline !== undefined && Date.now() >= deadline;
}

function iterate(root, deadline) {
  if (timeup(deadline)) { return; }
  var node = select(root, deadline);
  if (node === null || timeup(deadline)) { return; }
  var reward = rollout(node.state, deadline);
  if (timeup(deadline)) { return; }
  backpropagate(node, reward);
}

//==============================================================================
// Selection: descend using UCT, stopping at a not-fully-expanded node,
// then expand one new child and return it for simulation.
//==============================================================================

function select(node, deadline) {
  while (true) {
    if (timeup(deadline)) { return null; }
    if (findterminalp(node.state, library)) {
      node.solved = true;
      node.solvedValue = parseInt(findreward(role, node.state, library));
      updatesolvedup(node.parent);
      return node;
    }
    if (node.actions === null) {
      node.actions = findlegals(node.state, library);
    }
    // If there are unexpanded actions, expand the next one and return it
    if (node.children.length < node.actions.length) {
      return expand(node);
    }
    if (allchildrensolved(node)) {
      updatesolvedup(node);
      return null;
    }
    // Fully expanded and non-terminal — descend via UCB
    if (node.children.length === 0) { return node; }
    node = bestchild(node);
  }
}

function allchildrensolved(node) {
  if (node.children.length === 0) { return false; }
  for (var i = 0; i < node.children.length; i++) {
    if (!node.children[i].solved) { return false; }
  }
  return true;
}

function bestchild(node) {
  var ourTurn = isourturn(node);
  var best = null;
  var bestval = ourTurn ? -Infinity : Infinity;
  var hasNonLosing = false;
  var hasNonWinning = false;

  for (var i = 0; i < node.children.length; i++) {
    if (!(node.children[i].solved && node.children[i].solvedValue === 0)) {
      hasNonLosing = true;
    }
    if (!(node.children[i].solved && node.children[i].solvedValue === 100)) {
      hasNonWinning = true;
    }
  }

  for (var j = 0; j < node.children.length; j++) {
    var child = node.children[j];

    if (ourTurn && child.solved && child.solvedValue === 100) { return child; }
    if (!ourTurn && child.solved && child.solvedValue === 0) { return child; }
    if (ourTurn && hasNonLosing && child.solved && child.solvedValue === 0) { continue; }
    if (!ourTurn && hasNonWinning && child.solved && child.solvedValue === 100) { continue; }

    var val = selectionvalue(child, node.visits, ourTurn);
    if (
      (ourTurn && val > bestval) ||
      (!ourTurn && val < bestval)
    ) {
      best = child;
      bestval = val;
    }
  }
  return best || node.children[0];
}

function isourturn(node) {
  return findcontrol(node.state, library) === role;
}

function childaverage(node) {
  if (node.solved) { return node.solvedValue; }
  return node.visits > 0 ? node.score / node.visits : 50;
}

function selectionvalue(node, parentVisits, maximizing) {
  if (node.visits === 0) { return maximizing ? Infinity : -Infinity; }
  if (node.solved) { return node.solvedValue; }
  var exploit = node.score / node.visits;
  var explore = C * Math.sqrt(Math.log(Math.max(2, parentVisits)) / node.visits);
  return maximizing ? exploit + explore : exploit - explore;
}

function ucb(node, parentVisits) {
  if (node.visits === 0) { return Infinity; }
  var exploit = node.score / node.visits;
  return exploit + C * Math.sqrt(Math.log(parentVisits) / node.visits);
}

//==============================================================================
// Expansion: add exactly one new child (the next unvisited action)
//==============================================================================

function expand(node) {
  var move = node.actions[node.children.length];
  var newstate = simulate(move, node.state, library);
  var child = makenode(newstate, node);
  node.children.push(child);
  return child;
}

//==============================================================================
// Simulation: random rollout to terminal, return our reward
//==============================================================================

// Iterative to avoid stack overflow on long games.
function rollout(startstate, deadline) {
  var state = startstate;
  while (!findterminalp(state, library)) {
    if (timeup(deadline)) { return 50; }
    var actions = findlegals(state, library);
    if (actions.length === 0) { return 0; }
    state = simulate(actions[Math.floor(Math.random() * actions.length)], state, library);
  }
  return findreward(role, state, library) * 1;
}

//==============================================================================
// Backpropagation: walk parent pointers updating visits and score
//==============================================================================

function backpropagate(node, reward) {
  while (node !== null) {
    node.visits = node.visits + 1;
    node.score = node.score + reward;
    node = node.parent;
  }
}

function solvedvalue(node) {
  if (findterminalp(node.state, library)) {
    return parseInt(findreward(role, node.state, library));
  }

  if (node.actions === null) { return null; }
  if (node.children.length < node.actions.length || node.children.length === 0) { return null; }

  for (var i = 0; i < node.children.length; i++) {
    if (!node.children[i].solved) { return null; }
  }

  var control = findcontrol(node.state, library);
  var value = control === role ? 0 : 100;
  for (var j = 0; j < node.children.length; j++) {
    var childValue = node.children[j].solvedValue;
    if (control === role) {
      if (childValue > value) { value = childValue; }
    } else {
      if (childValue < value) { value = childValue; }
    }
  }
  return value;
}

function updatesolvedup(node) {
  while (node !== null) {
    var value = solvedvalue(node);
    if (value === null) {
      node.solved = false;
      node.solvedValue = null;
    } else {
      node.solved = true;
      node.solvedValue = value;
    }
    node = node.parent;
  }
}

//==============================================================================
// Action selection: evaluate all legal root moves with tactical guards
//==============================================================================

function ensurechildat(node, index, deadline) {
  if (node.actions === null) { node.actions = findlegals(node.state, library); }
  while (node.children.length <= index && node.children.length < node.actions.length) {
    if (timeup(deadline)) { break; }
    expand(node);
  }
  return node.children[index] || null;
}

function scoreunvisited(node, deadline) {
  if (node === null || node.visits > 0 || timeup(deadline)) { return false; }
  var reward = rollout(node.state, deadline);
  if (timeup(deadline)) { return false; }
  backpropagate(node, reward);
  return true;
}

function analyzetactical(child, deadline) {
  if (child.tacticalKnown || timeup(deadline)) { return; }

  child.isImmediateWin = false;
  child.allowsImmediateLoss = false;

  if (findterminalp(child.state, library)) {
    var terminalReward = parseInt(findreward(role, child.state, library));
    child.solved = true;
    child.solvedValue = terminalReward;
    child.isImmediateWin = terminalReward === 100;
    child.tacticalKnown = true;
    return;
  }

  if (findcontrol(child.state, library) !== role) {
    if (child.actions === null) { child.actions = findlegals(child.state, library); }
    for (var j = 0; j < child.actions.length; j++) {
      if (timeup(deadline)) { return; }
      var newstate = simulate(child.actions[j], child.state, library);
      if (findterminalp(newstate, library) && parseInt(findreward(role, newstate, library)) === 0) {
        child.allowsImmediateLoss = true;
        break;
      }
    }
  }

  child.tacticalKnown = true;
}

function primeroot(node, deadline) {
  if (timeup(deadline)) { return; }
  if (node.actions === null) { node.actions = findlegals(node.state, library); }

  // every root action gets a child and evidence before
  // any action is allowed to consume time going deeper.
  for (var i = 0; i < node.actions.length; i++) {
    if (timeup(deadline)) { return; }
    var child = ensurechildat(node, i, deadline);
    if (child === null) { return; }
    analyzetactical(child, deadline);
    scoreunvisited(child, deadline);
  }

  // Second pass: expand opponent replies round-robin so early root moves do
  // not get a deeper subtree just because they appear first in legal order.
  var replyIndex = 0;
  while (!timeup(deadline)) {
    var expandedAny = false;
    for (var rootIndex = 0; rootIndex < node.children.length; rootIndex++) {
      if (timeup(deadline)) { return; }
      var rootChild = node.children[rootIndex];
      if (rootChild.solved) { continue; }
      if (findcontrol(rootChild.state, library) === role) { continue; }
      if (rootChild.actions === null) { rootChild.actions = findlegals(rootChild.state, library); }
      if (replyIndex >= rootChild.actions.length) { continue; }

      var reply = ensurechildat(rootChild, replyIndex, deadline);
      if (reply === null) { continue; }
      expandedAny = true;
      analyzetactical(reply, deadline);
      scoreunvisited(reply, deadline);
    }
    if (!expandedAny) {
      return;
    }
    replyIndex++;
  }
}

function prefercandidate(score, bestScore) {
  return score > bestScore;
}

function breakordertie(score, bestScore, candidateIndex, bestIndex) {
  return score === bestScore && bestIndex !== -1 && candidateIndex > bestIndex;
}

function candidatebeats(score, bestScore, candidateIndex, bestIndex) {
  return prefercandidate(score, bestScore) || breakordertie(score, bestScore, candidateIndex, bestIndex);
}

function fallbackchild(node, action) {
  return makenode(simulate(action, node.state, library), null);
}

function pessimisticvalue(node) {
  if (node.solved) { return node.solvedValue; }
  if (node.allowsImmediateLoss) { return 0; }

  var value = childaverage(node);
  if (findcontrol(node.state, library) !== role && node.children.length > 0) {
    value = 100;
    for (var i = 0; i < node.children.length; i++) {
      var replyValue = childaverage(node.children[i]);
      if (replyValue < value) { value = replyValue; }
    }

    // If not every opponent reply has been expanded, keep the node's own
    // rollout value in the estimate rather than pretending the reply set is
    // complete.
    if (node.actions !== null && node.children.length < node.actions.length) {
      var ownAverage = childaverage(node);
      if (ownAverage < value) { value = ownAverage; }
    }
  }

  return value;
}

function selectaction(node, deadline) {
  if (node.actions === null) { node.actions = findlegals(node.state, library); }
  if (node.actions.length === 0) { return { action: false, child: node, score: 0 }; }
  if (node.children.length === 0) {
    var first = ensurechildat(node, 0, deadline);
    if (first !== null && !first.tacticalKnown) { analyzetactical(first, deadline); }
  }

  var bestSafe = null;
  var bestSafeScore = -Infinity;
  var bestSafeIndex = -1;

  var bestAny = null;
  var bestAnyScore = -Infinity;
  var bestAnyIndex = -1;

  for (var i = 0; i < node.children.length; i++) {
    var child = node.children[i];

    if (child.solved && child.solvedValue === 100) {
      return { action: node.actions[i], child: child, score: 100 };
    }
    if (child.isImmediateWin) {
      return { action: node.actions[i], child: child, score: 100 };
    }

    var moveValue = pessimisticvalue(child);
    var losingNow = child.allowsImmediateLoss || (child.solved && child.solvedValue === 0) || moveValue === 0;

    if (candidatebeats(moveValue, bestAnyScore, i, bestAnyIndex)) {
      bestAny = { action: node.actions[i], child: child, score: moveValue };
      bestAnyScore = moveValue;
      bestAnyIndex = i;
    }

    if (!losingNow) {
      if (candidatebeats(moveValue, bestSafeScore, i, bestSafeIndex)) {
        bestSafe = { action: node.actions[i], child: child, score: moveValue };
        bestSafeScore = moveValue;
        bestSafeIndex = i;
      }
    }
  }

  var picked = bestSafe || bestAny;
  if (picked === null) {
    var fallbackAction = node.actions[0];
    var fallbackNode = node.children.length > 0 ? node.children[0] : ensurechildat(node, 0, deadline);
    if (fallbackNode === null) { fallbackNode = fallbackchild(node, fallbackAction); }
    picked = { action: fallbackAction, child: fallbackNode, score: 0 };
  }

  return {
    action: picked.action,
    child: picked.child,
    score: Math.round(Math.max(picked.score, 0))
  };
}

//==============================================================================
// Tree reuse: advance root to the subtree matching the move played
//==============================================================================

function subtree(move, node) {
  if (node.actions === null) { node.actions = findlegals(node.state, library); }
  // Only search expanded children — node.children[i] is only valid for i < children.length
  for (var i = 0; i < node.children.length; i++) {
    if (equalp(move, node.actions[i])) {
      var child = node.children[i];
      child.parent = null;
      return child;
    }
  }
  // Move not found among expanded children — start fresh from the resulting state
  var newstate = simulate(move, node.state, library);
  return makenode(newstate, null);
}

//==============================================================================
// End of player code
//==============================================================================
