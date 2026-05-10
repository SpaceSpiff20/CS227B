var manager = "manager";
var player = "hail_mary_mcts_metagaming";

var role = "robot";
var rules = [];
var originalRules = [];
var startclock = 10;
var playclock = 10;

var library = [];
var roles = [];
var state = [];
var tree = null;
var safetyMs = 1000;
var pendingMove = null;

var ENABLE_RULE_OPTIMIZATION = true;
var metagameAnalysis = null;
var optimizationSummary = null;
var runtimePolicy = defaultruntimepolicy();

//==============================================================================

function ping() { return "ready"; }

function start(r, rs, sc, pc) {
  role = r;
  originalRules = rs.slice(1);
  startclock = numberize(sc);
  playclock = numberize(pc);
  pendingMove = null;

  var startDeadline = Date.now() + Math.max(0, startclock * 1000 - safetyMs);
  var analysisDeadline = Date.now() + metagamebudget(startDeadline);
  var metagame = runmetagaming(originalRules, role, analysisDeadline);

  rules = metagame.optimizedRules;
  metagameAnalysis = metagame.analysis;
  optimizationSummary = metagame.optimizationSummary;
  runtimePolicy = configurepolicy(metagameAnalysis);
  C = runtimePolicy.explorationConstant;

  library = definemorerules([], rules);
  roles = findroles(library);
  state = findinits(library);
  tree = makenode(state, null);

  var headstartIterations = headstart(tree, startDeadline);
  console.log(
    "[mcts_metagaming] start role=" + role +
    " roles=" + roles.length +
    " startclock=" + startclock +
    " playclock=" + playclock +
    " policy=" + runtimePolicy.searchMode + "/" + runtimePolicy.selectionMode +
    " optimized=" + optimizationSummary.reorderedRules +
    " samples=" + metagameAnalysis.samples +
    " headstart=" + headstartIterations
  );
  return "ready";
}

function play(move) {
  syncstate(move);
  if (findcontrol(state, library) !== role) {
    if (runtimePolicy.searchDuringOpponentTurn) {
      var opponentDeadline = Date.now() + Math.max(25, Math.floor(playclock * 1000 * 0.20));
      headstart(tree, opponentDeadline);
    }
    return false;
  }
  var returnDeadline = Date.now() + Math.max(100, playclock * 1000 - safetyMs);
  var searchDeadline = Math.max(Date.now(), returnDeadline - 200);
  var primeBudgetMs = Math.max(75, Math.floor((playclock * 1000 - safetyMs) * runtimePolicy.primeFraction));
  var primeDeadline = Math.min(searchDeadline, Date.now() + primeBudgetMs);
  primeroot(tree, primeDeadline);
  var iterations = 0;
  while (Date.now() < searchDeadline && !tree.solved) {
    iterate(tree, searchDeadline);
    iterations++;
  }
  var result = selectaction(tree, returnDeadline);
  console.log(
    "[mcts_metagaming] iterations=" + iterations +
    " move=" + grind(result.action) +
    " score=" + result.score +
    " C=" + C
  );
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
// Metagaming
//==============================================================================

function metagamebudget(deadline) {
  var remaining = Math.max(0, deadline - Date.now());
  if (remaining <= 250) { return 0; }
  return Math.min(2500, Math.floor(remaining * 0.35));
}

function runmetagaming(rawRules, playerRole, deadline) {
  var optimized = rawRules;
  var summary = emptyoptimizationsummary();

  if (ENABLE_RULE_OPTIMIZATION && Date.now() < deadline) {
    var fixed = fixrules(rawRules);
    optimized = fixed.rules;
    summary = fixed.summary;
  }

  var analysis = analyzegameuntil(optimized, playerRole, deadline);
  return {
    optimizedRules: optimized,
    analysis: analysis,
    optimizationSummary: summary
  };
}

function headstart(root, deadline) {
  if (root === null || timeup(deadline)) { return 0; }
  var primeBudget = Math.max(25, Math.floor((deadline - Date.now()) * runtimePolicy.primeFraction));
  var primeDeadline = Math.min(deadline, Date.now() + primeBudget);
  primeroot(root, primeDeadline);
  var iterations = 0;
  while (!timeup(deadline) && !root.solved) {
    iterate(root, deadline);
    iterations++;
  }
  return iterations;
}

function analyzegameuntil(candidateRules, playerRole, deadline) {
  var analysis = defaultanalysis();
  var tempLibrary;
  var tempRoles;
  var tempState;

  try {
    tempLibrary = definemorerules([], candidateRules);
    tempRoles = findroles(tempLibrary);
    tempState = findinits(tempLibrary);
  } catch (err) {
    analysis.recommendedSearch = "mcts";
    analysis.selectionMode = "balanced";
    analysis.opponentModel = "minimax";
    return analysis;
  }

  analysis.numRoles = tempRoles.length;
  analysis.hasIntermediateRewards = detectsintermediaterewards(playerRole, tempState, tempLibrary);

  var totals = {
    samples: 0,
    depth: 0,
    branching: 0,
    branchPoints: 0,
    expansionMs: 0,
    expansions: 0,
    rewards: 0,
    intermediateRewards: analysis.hasIntermediateRewards
  };

  while (Date.now() < deadline) {
    var sample = randomplayoutstats(playerRole, tempState, tempLibrary, deadline);
    if (sample === null) { break; }
    totals.samples++;
    totals.depth += sample.depth;
    totals.branching += sample.branching;
    totals.branchPoints += sample.branchPoints;
    totals.expansionMs += sample.expansionMs;
    totals.expansions += sample.expansions;
    totals.rewards += sample.reward;
    if (sample.intermediateReward) { totals.intermediateRewards = true; }
  }

  if (totals.samples > 0) {
    analysis.samples = totals.samples;
    analysis.estimatedDepth = Math.round(totals.depth / totals.samples);
    analysis.estimatedBranchingFactor = totals.branchPoints > 0 ? totals.branching / totals.branchPoints : 1;
    analysis.expansionCostMs = totals.expansions > 0 ? totals.expansionMs / totals.expansions : 0;
    analysis.averageReward = totals.rewards / totals.samples;
    analysis.hasIntermediateRewards = totals.intermediateRewards;
  } else {
    analysis.estimatedBranchingFactor = safelegalcount(tempState, tempLibrary);
  }

  return choosepolicy(analysis);
}

function defaultanalysis() {
  return {
    numRoles: 0,
    samples: 0,
    estimatedBranchingFactor: 1,
    estimatedDepth: 0,
    expansionCostMs: 0,
    averageReward: 50,
    hasIntermediateRewards: false,
    recommendedSearch: "mcts",
    selectionMode: "balanced",
    evaluationFeatures: ["mobility", "depth_charge"],
    opponentModel: "minimax"
  };
}

function detectsintermediaterewards(playerRole, startState, gameLibrary) {
  try {
    if (!findterminalp(startState, gameLibrary)) {
      var reward = numberize(findreward(playerRole, startState, gameLibrary));
      return !isNaN(reward) && reward > 0 && reward < 100;
    }
  } catch (err) {
    return false;
  }
  return false;
}

function randomplayoutstats(playerRole, startState, gameLibrary, deadline) {
  var current = startState;
  var depth = 0;
  var branching = 0;
  var branchPoints = 0;
  var expansionMs = 0;
  var expansions = 0;
  var sawIntermediateReward = false;
  var maxDepth = 200;

  while (!findterminalp(current, gameLibrary) && depth < maxDepth) {
    if (timeup(deadline)) { return null; }

    var reward = numberize(findreward(playerRole, current, gameLibrary));
    if (!isNaN(reward) && reward > 0 && reward < 100) {
      sawIntermediateReward = true;
    }

    var t0 = Date.now();
    var actions = findlegals(current, gameLibrary);
    expansionMs += Date.now() - t0;
    expansions++;
    branching += actions.length;
    branchPoints++;

    if (actions.length === 0) { break; }
    var action = actions[Math.floor(Math.random() * actions.length)];
    var t1 = Date.now();
    current = simulate(action, current, gameLibrary);
    expansionMs += Date.now() - t1;
    expansions++;
    depth++;
  }

  var finalReward = 50;
  try {
    finalReward = numberize(findreward(playerRole, current, gameLibrary));
    if (isNaN(finalReward)) { finalReward = 50; }
  } catch (err) {
    finalReward = 50;
  }

  return {
    depth: depth,
    branching: branching,
    branchPoints: branchPoints,
    expansionMs: expansionMs,
    expansions: expansions,
    reward: finalReward,
    intermediateReward: sawIntermediateReward
  };
}

function safelegalcount(position, gameLibrary) {
  try {
    return findlegals(position, gameLibrary).length;
  } catch (err) {
    return 1;
  }
}

function choosepolicy(analysis) {
  var highBranching = analysis.estimatedBranchingFactor > 25;
  var expensiveExpansion = analysis.expansionCostMs > 15;
  var singlePlayer = analysis.numRoles <= 1;

  analysis.recommendedSearch = highBranching || expensiveExpansion ? "mcts_broad" : "mcts_deep";
  analysis.selectionMode = highBranching ? "explore" : "exploit";
  analysis.evaluationFeatures = analysis.hasIntermediateRewards ?
    ["state_value", "mobility", "depth_charge"] :
    ["mobility", "depth_charge"];
  analysis.opponentModel = singlePlayer ? "none" : "minimax";
  return analysis;
}

function defaultruntimepolicy() {
  return {
    searchMode: "mcts",
    selectionMode: "balanced",
    explorationConstant: 70,
    primeFraction: 0.15,
    rolloutMaxDepth: 200,
    useIntermediateRewards: false,
    opponentModel: "minimax",
    searchDuringOpponentTurn: true
  };
}

function configurepolicy(analysis) {
  var policy = defaultruntimepolicy();
  policy.searchMode = analysis.recommendedSearch;
  policy.selectionMode = analysis.selectionMode;
  policy.useIntermediateRewards = analysis.hasIntermediateRewards;
  policy.opponentModel = analysis.opponentModel;

  if (analysis.selectionMode === "explore") {
    policy.explorationConstant = 90;
    policy.primeFraction = 0.25;
  } else if (analysis.selectionMode === "exploit") {
    policy.explorationConstant = 45;
    policy.primeFraction = 0.12;
  }

  if (analysis.expansionCostMs > 15) {
    policy.rolloutMaxDepth = 80;
    policy.primeFraction = Math.max(policy.primeFraction, 0.25);
  } else if (analysis.estimatedDepth > 120) {
    policy.rolloutMaxDepth = 120;
  }

  if (analysis.opponentModel === "none") {
    policy.searchDuringOpponentTurn = false;
  }

  return policy;
}

//==============================================================================
// Local rule optimization: conservative subgoal ordering
//==============================================================================

function emptyoptimizationsummary() {
  return {
    totalRules: 0,
    reorderedRules: 0,
    reorderedConjunctions: 0
  };
}

function fixrules(sourceRules) {
  var summary = emptyoptimizationsummary();
  var optimized = [];
  var stats = relationstats(sourceRules);

  for (var i = 0; i < sourceRules.length; i++) {
    var optimizedRule = optimizestatement(sourceRules[i], stats, summary);
    optimized.push(optimizedRule);
  }

  return { rules: optimized, summary: summary };
}

function optimizestatement(statement, stats, summary) {
  if (symbolp(statement)) { return statement; }
  if (statement[0] === "rule") {
    summary.totalRules++;
    var body = statement.slice(2);
    var ordered = ordersubgoals(body, stats);
    if (!sameorder(body, ordered)) { summary.reorderedRules++; }
    return [statement[0], statement[1]].concat(ordered);
  }
  if (statement[0] === "handler") {
    var condition = optimizeexpression(statement[1], stats, summary);
    var effect = optimizeexpression(statement[2], stats, summary);
    return [statement[0], condition, effect];
  }
  return optimizeexpression(statement, stats, summary);
}

function optimizeexpression(expression, stats, summary) {
  if (symbolp(expression)) { return expression; }
  if (expression[0] === "and") {
    var original = expression.slice(1);
    var ordered = ordersubgoals(original, stats);
    if (!sameorder(original, ordered)) { summary.reorderedConjunctions++; }
    return ["and"].concat(ordered);
  }
  if (expression[0] === "transition") {
    var optimizedCondition = optimizeexpression(expression[1], stats, summary);
    return [expression[0], optimizedCondition, expression[2]];
  }
  if (expression[0] === "not") {
    return [expression[0], optimizeexpression(expression[1], stats, summary)];
  }

  var copy = [expression[0]];
  for (var i = 1; i < expression.length; i++) {
    copy.push(optimizeexpression(expression[i], stats, summary));
  }
  return copy;
}

function ordersubgoals(body, stats) {
  var remaining = body.slice();
  var ordered = [];
  var bound = [];

  while (remaining.length > 0) {
    var index = bestreadyindex(remaining, bound, stats);
    if (index < 0) { index = bestgeneratorindex(remaining, bound, stats); }
    if (index < 0) { index = 0; }

    var chosen = remaining.splice(index, 1)[0];
    ordered.push(chosen);
    bound = unionvars(bound, variablesboundby(chosen));
  }

  return ordered;
}

function bestreadyindex(goals, bound, stats) {
  var best = -1;
  var bestScore = Infinity;
  for (var i = 0; i < goals.length; i++) {
    if (!readygoalp(goals[i], bound)) { continue; }
    var score = goalcost(goals[i], stats);
    if (score < bestScore) {
      best = i;
      bestScore = score;
    }
  }
  return best;
}

function bestgeneratorindex(goals, bound, stats) {
  var best = -1;
  var bestScore = Infinity;
  for (var i = 0; i < goals.length; i++) {
    if (!positiverelationp(goals[i])) { continue; }
    var score = generatorcost(goals[i], bound, stats);
    if (score < bestScore) {
      best = i;
      bestScore = score;
    }
  }
  return best;
}

function readygoalp(goal, bound) {
  var goalVars = metavars(goal);
  if (positiverelationp(goal)) {
    return allbound(goalVars, bound);
  }
  return allbound(goalVars, bound);
}

function variablesboundby(goal) {
  if (positiverelationp(goal)) { return metavars(goal); }
  return [];
}

function positiverelationp(goal) {
  if (symbolp(goal)) { return !varp(goal); }
  if (goal.length === 0) { return false; }
  var op = goal[0];
  if (
    op === "not" ||
    op === "and" ||
    op === "or" ||
    op === "same" ||
    op === "distinct" ||
    op === "plus" ||
    op === "minus" ||
    op === "leq" ||
    op === "evaluate" ||
    op === "countofall" ||
    op === "setofall" ||
    op === "exists" ||
    op === "member" ||
    op === "matches" ||
    op === "submatches"
  ) {
    return false;
  }
  return true;
}

function goalcost(goal, stats) {
  if (symbolp(goal)) { return relationcost(goal, stats); }
  if (goal[0] === "same" || goal[0] === "distinct") { return 0; }
  if (goal[0] === "plus" || goal[0] === "minus" || goal[0] === "leq" || goal[0] === "evaluate") { return 1; }
  if (goal[0] === "not") { return 10; }
  if (positiverelationp(goal)) { return relationcost(goal[0], stats); }
  return 100;
}

function generatorcost(goal, bound, stats) {
  var goalVars = metavars(goal);
  var unbound = 0;
  for (var i = 0; i < goalVars.length; i++) {
    if (!find(goalVars[i], bound)) { unbound++; }
  }
  return goalcost(goal, stats) + unbound * 100;
}

function relationcost(name, stats) {
  if (stats[name] === undefined) { return 50; }
  return stats[name];
}

function relationstats(sourceRules) {
  var stats = {};
  for (var i = 0; i < sourceRules.length; i++) {
    var head = getstatementhead(sourceRules[i]);
    if (head === null) { continue; }
    var op = symbolp(head) ? head : head[0];
    if (stats[op] === undefined) { stats[op] = 0; }
    stats[op]++;
  }
  return stats;
}

function getstatementhead(statement) {
  if (symbolp(statement)) { return statement; }
  if (statement[0] === "rule" || statement[0] === "handler") { return statement[1]; }
  return statement;
}

function metavars(expression) {
  var found = [];
  metavarsexp(expression, found);
  return found;
}

function metavarsexp(expression, found) {
  if (varp(expression)) {
    if (!find(expression, found)) { found.push(expression); }
    return found;
  }
  if (symbolp(expression)) { return found; }
  for (var i = 0; i < expression.length; i++) {
    metavarsexp(expression[i], found);
  }
  return found;
}

function unionvars(left, right) {
  var result = left.slice();
  for (var i = 0; i < right.length; i++) {
    if (!find(right[i], result)) { result.push(right[i]); }
  }
  return result;
}

function allbound(goalVars, bound) {
  for (var i = 0; i < goalVars.length; i++) {
    if (!find(goalVars[i], bound)) { return false; }
  }
  return true;
}

function sameorder(left, right) {
  if (left.length !== right.length) { return false; }
  for (var i = 0; i < left.length; i++) {
    if (!equalp(left[i], right[i])) { return false; }
  }
  return true;
}

//==============================================================================
// Node
//==============================================================================

// C is tuned by Bigswitch analysis during start.
var C = 70;

function makenode(state, parent) {
  return {
    state: state,
    parent: parent,
    actions: null,
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
    if (node.children.length < node.actions.length) {
      return expand(node);
    }
    if (allchildrensolved(node)) {
      updatesolvedup(node);
      return null;
    }
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
  if (runtimePolicy.opponentModel === "none") { return true; }
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

function rollout(startstate, deadline) {
  var current = startstate;
  var depth = 0;
  while (!findterminalp(current, library) && depth < runtimePolicy.rolloutMaxDepth) {
    if (timeup(deadline)) { return cutoffvalue(current); }
    var actions = findlegals(current, library);
    if (actions.length === 0) { return cutoffvalue(current); }
    current = simulate(actions[Math.floor(Math.random() * actions.length)], current, library);
    depth++;
  }
  if (findterminalp(current, library)) {
    return findreward(role, current, library) * 1;
  }
  return cutoffvalue(current);
}

function cutoffvalue(position) {
  if (runtimePolicy.useIntermediateRewards) {
    var reward = numberize(findreward(role, position, library));
    if (!isNaN(reward)) { return reward; }
  }
  return 50;
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

  if (runtimePolicy.opponentModel !== "none" && findcontrol(child.state, library) !== role) {
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

  for (var i = 0; i < node.actions.length; i++) {
    if (timeup(deadline)) { return; }
    var child = ensurechildat(node, i, deadline);
    if (child === null) { return; }
    analyzetactical(child, deadline);
    scoreunvisited(child, deadline);
  }

  var replyIndex = 0;
  while (!timeup(deadline)) {
    var expandedAny = false;
    for (var rootIndex = 0; rootIndex < node.children.length; rootIndex++) {
      if (timeup(deadline)) { return; }
      var rootChild = node.children[rootIndex];
      if (rootChild.solved) { continue; }
      if (runtimePolicy.opponentModel === "none" || findcontrol(rootChild.state, library) === role) { continue; }
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
  if (runtimePolicy.opponentModel !== "none" && findcontrol(node.state, library) !== role && node.children.length > 0) {
    value = 100;
    for (var i = 0; i < node.children.length; i++) {
      var replyValue = childaverage(node.children[i]);
      if (replyValue < value) { value = replyValue; }
    }

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
  for (var i = 0; i < node.children.length; i++) {
    if (equalp(move, node.actions[i])) {
      var child = node.children[i];
      child.parent = null;
      return child;
    }
  }
  var newstate = simulate(move, node.state, library);
  return makenode(newstate, null);
}

//==============================================================================
// End of player code
//==============================================================================
