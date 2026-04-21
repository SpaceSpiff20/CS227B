var manager = "manager";
var player = "hail_mary_minimax_single";

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
  return "ready";
}

function bestmove(state) {
  var actions = findlegals(state, library);
  var action = actions[0];
  var score = 0;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate);
    if (newscore > score) {
      score = newscore;
      action = actions[i];
    }
  }
  return action;
}

function minimax(role, state) {
  console.log("minimaxing");
  if (findterminalp(state, library)) {
    return findreward(role, state, library);
  }
  var active = findcontrol(state, library);
  if (active === role) {
    return maximize(active, role, state);
  }
  return minimize(active, role, state);
}

function maximize(active, role, state) {
  console.log("maximizing");
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    return 0;
  }
  var score = 0;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate);
    if (newscore > score) {
      score = newscore;
    }
  }
  return score;
}

function minimize(active, role, state) {
  console.log("minimizing");
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    return 0;
  }
  var score = 100;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimax(role, newstate);
    if (newscore < score) {
      score = newscore;
    }
  }
  return score;
}

function play(move) {
  if (move !== nil) {
    state = simulate(move, state, library);
  }
  if (findcontrol(state, library) !== role) {
    return false;
  }
  return bestmove(state);
}

function stop(move) {
  return false;
}

function abort() {
  return false;
}
