//==============================================================================
// minimaxid.js
// This is a player for minimax with iterative deepening.
//==============================================================================

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

function play(move) {
  if (move !== nil) {
    compexecute(move, state, library);
  }
  if (findcontrol(state, library) !== role) {
    return false;
  }
  return playminimaxid(role);
}

function stop(move) {
  return false;
}

function abort() {
  return false;
}

//==============================================================================
// minimaxid
//==============================================================================

var nodes = 0;
var terminals = 0;

function playminimaxid(role) {
  var deadline = Date.now() + (playclock - 2) * 1000;
  console.log(deadline);
  var best = findlegalx(state, library);
  for (var k = 1; k < 25; i = k++) {
    var action = simpleminimaxid(role, state, k, deadline);
    if (action === false) {
      console.log(k - 1);
      return best;
    }
    best = action;
  }
  return best;
}

function simpleminimaxid(role, state, depth, deadline) {
  var actions = shuffle(findlegals(state, library));
  if (actions.length === 0) {
    return false;
  }
  if (actions.length === 1) {
    return actions[0];
  }
  var best = actions[0];
  var score = 0;
  nodes = 0;
  for (var i = 0; i < actions.length; i++) {
    //console.log(grind(actions[i]));
    var newstate = simulate(actions[i], state, library);
    var newscore = minimaxid(role, newstate, depth, deadline);
    if (newscore === false) {
      return false;
    }
    //console.log(newscore);
    if (newscore === 100) {
      return actions[i];
    }
    if (newscore > score) {
      best = actions[i];
      score = newscore;
    }
  }
  return best;
}

function minimaxid(role, state, depth, deadline) {
  nodes = nodes + 1;
  if (findterminalp(state, library)) {
    terminals = terminals + 1;
    return findreward(role, state, library) * 1;
  }
  if (depth <= 0) {
    terminals = terminals + 1;
    return findreward(role, state, library) * 1;
  }
  if (Date.now() > deadline) {
    return false;
  }
  var active = findcontrol(state, library);
  if (active === role) {
    return maximizeid(active, role, state, depth, deadline);
  }
  return minimizeid(active, role, state, depth, deadline);
}

function maximizeid(active, role, state, depth, deadline) {
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    return 0;
  }
  var score = 0;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimaxid(role, newstate, depth - 1, deadline);
    if (newscore === false) {
      return false;
    }
    if (newscore === 100) {
      return 100;
    }
    if (newscore > score) {
      score = newscore;
    }
  }
  return score;
}

function minimizeid(active, role, state, depth, deadline) {
  var actions = findlegals(state, library);
  if (actions.length === 0) {
    return 0;
  }
  var score = 100;
  for (var i = 0; i < actions.length; i++) {
    var newstate = simulate(actions[i], state, library);
    var newscore = minimaxid(role, newstate, depth - 1, deadline);
    if (newscore === false) {
      return false;
    }
    if (newscore === 0) {
      return 0;
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
