var manager = "manager";
var player = "hail_mary_minimax_ab_mobility";

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
// minimax with alpha-beta pruning + mobility evaluation
//==============================================================================

var nodes = 0;
var terminals = 0;
var pruned = 0;
var elapsed = 0;
var deadline = 0;

function playminimax(role) {
  var actions = shuffle(findlegals(state, library));
  if (actions.length === 0) {
    console.log("[minimax_ab_mobility] no legal actions");
    return false;
  }
  if (actions.length === 1) {
    console.log("[minimax_ab_mobility] only one action, returning immediately");
    return actions[0];
  }
  deadline = Date.now() + (playclock - 1) * 1000;
  var action = actions[0];
  var score = 0;
  nodes = 0;
  terminals = 0;
  pruned = 0;
  var timedOut = false;
  console.log("[minimax_ab_mobility] searching " + actions.length + " actions, deadline in " + (playclock - 1) + "s");
  for (var i = 0; i < actions.length; i++) {
    if (Date.now() > deadline) {
      timedOut = true;
      break;
    }
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate, score, 100);
    if (newscore === 100) {
      console.log("[minimax_ab_mobility] found winning move at action " + i + ", nodes=" + nodes + " terminals=" + terminals + " pruned=" + pruned);
      return actions[i];
    }
    if (newscore > score) {
      action = actions[i];
      score = newscore;
    }
  }
  console.log("[minimax_ab_mobility] done — nodes=" + nodes + " terminals=" + terminals + " pruned=" + pruned + " bestScore=" + score + (timedOut ? " (timed out after " + i + "/" + actions.length + " actions)" : ""));
  return action;
}

function testminimax(role, state) {
  nodes = 0;
  terminals = 0;
  pruned = 0;
  var beg = performance.now();
  var result = minimax(role, state, 0, 100);
  var end = performance.now();
  elapsed = Math.round(end - beg);
  return result;
}

function mobilityEval(role, state) {
  if (findterminalp(state, library)) {
    terminals = terminals + 1;
    return findreward(role, state, library) * 1;
  }

  var active = findcontrol(state, library);
  var legalMoves = findlegals(state, library).length;
  var scaledMobility = Math.min(100, legalMoves * 10);

  // If we control this state, more moves is better.
  if (active === role) {
    return scaledMobility;
  }

  // If opponent controls this state, fewer moves for them is better for us.
  return 100 - scaledMobility;
}

function minimax(role, state, alpha, beta) {
  nodes = nodes + 1;
  if (Date.now() > deadline) {
    return mobilityEval(role, state);
  }
  if (findterminalp(state, library)) {
    return mobilityEval(role, state);
  }
  var active = findcontrol(state, library);
  if (active === role) {
    return maximize(active, role, state, alpha, beta);
  }
  return minimize(active, role, state, alpha, beta);
}

function maximize(active, role, state, alpha, beta) {
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    return mobilityEval(role, state);
  }
  var score = alpha;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate, score, beta);
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

function minimize(active, role, state, alpha, beta) {
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    return mobilityEval(role, state);
  }
  var score = beta;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate, alpha, score);
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
