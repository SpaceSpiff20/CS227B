var manager = "manager";
var player = "hail_mary_minimax_ab_bounded_depth";

var role = "robot";
var rules = [];
var startclock = 10;
var playclock = 10;

var library = [];
var roles = [];
var state = [];

//==============================================================================

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
  console.log("[start] role=" + role + " startclock=" + startclock + " playclock=" + playclock + " roles=" + roles.length);
  return "ready";
}

function play(move) {
  if (move !== nil) {
    state = simulate(move, state, library);
  }
  if (findcontrol(state, library) !== role) {
    return false;
  }
  return playminimax(role);
}

function stop(move) {
  return false;
}

function abort() {
  return false;
}

//==============================================================================
// bounded-depth minimax with alpha-beta pruning + heuristic fringe evaluation
//==============================================================================

var nodes = 0;
var terminals = 0;
var pruned = 0;
var fringes = 0;
var elapsed = 0;
var deadline = 0;
var maxDepth = 4;

function playminimax(role) {
  var actions = shuffle(findlegals(state, library));
  if (actions.length === 0) {
    console.log("[minimax_ab_bounded_depth] no legal actions");
    return false;
  }
  if (actions.length === 1) {
    console.log("[minimax_ab_bounded_depth] only one action, returning immediately");
    return actions[0];
  }

  deadline = Date.now() + (playclock - 1) * 1000;
  var action = actions[0];
  var score = 0;
  nodes = 0;
  terminals = 0;
  pruned = 0;
  fringes = 0;
  var timedOut = false;

  console.log("[minimax_ab_bounded_depth] searching " + actions.length + " actions at depth " + maxDepth + ", deadline in " + (playclock - 1) + "s");

  for (var i = 0; i < actions.length; i++) {
    if (Date.now() > deadline) {
      timedOut = true;
      break;
    }
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate, score, 100, 1);
    if (newscore === 100) {
      console.log("[minimax_ab_bounded_depth] found winning move at action " + i + ", nodes=" + nodes + " terminals=" + terminals + " fringes=" + fringes + " pruned=" + pruned);
      return actions[i];
    }
    if (newscore > score) {
      action = actions[i];
      score = newscore;
    }
  }

  console.log(
    "[minimax_ab_bounded_depth] done — nodes=" + nodes +
      " terminals=" + terminals +
      " fringes=" + fringes +
      " pruned=" + pruned +
      " bestScore=" + score +
      (timedOut ? " (timed out after " + i + "/" + actions.length + " actions)" : "")
  );
  return action;
}

function testminimax(role, state) {
  nodes = 0;
  terminals = 0;
  pruned = 0;
  fringes = 0;
  var beg = performance.now();
  var result = minimax(role, state, 0, 100, 0);
  var end = performance.now();
  elapsed = Math.round(end - beg);
  return result;
}

function mobilityEval(role, state) {
  var active = findcontrol(state, library);
  var legalMoves = findlegals(state, library).length;
  var scaledMobility = Math.min(100, legalMoves * 10);
  if (active === role) {
    return scaledMobility;
  }
  return 100 - scaledMobility;
}

function fringeEval(role, state) {
  // Blend "intermediate reward" and mobility to score non-terminal fringe states.
  var reward = findreward(role, state, library) * 1;
  var mobility = mobilityEval(role, state);
  return Math.round(0.7 * reward + 0.3 * mobility);
}

function minimax(role, state, alpha, beta, depth) {
  nodes = nodes + 1;

  if (Date.now() > deadline) {
    fringes = fringes + 1;
    return fringeEval(role, state);
  }

  if (findterminalp(state, library)) {
    terminals = terminals + 1;
    return findreward(role, state, library) * 1;
  }

  if (depth >= maxDepth) {
    fringes = fringes + 1;
    return fringeEval(role, state);
  }

  var active = findcontrol(state, library);
  if (active === role) {
    return maximize(active, role, state, alpha, beta, depth);
  }
  return minimize(active, role, state, alpha, beta, depth);
}

function maximize(active, role, state, alpha, beta, depth) {
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    fringes = fringes + 1;
    return fringeEval(role, state);
  }
  var score = alpha;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate, score, beta, depth + 1);
    if (newscore >= beta) {
      pruned = pruned + 1;
      return newscore;
    }
    if (newscore > score) {
      score = newscore;
    }
  }
  return score;
}

function minimize(active, role, state, alpha, beta, depth) {
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    fringes = fringes + 1;
    return fringeEval(role, state);
  }
  var score = beta;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate, alpha, score, depth + 1);
    if (newscore <= alpha) {
      pruned = pruned + 1;
      return newscore;
    }
    if (newscore < score) {
      score = newscore;
    }
  }
  return score;
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
