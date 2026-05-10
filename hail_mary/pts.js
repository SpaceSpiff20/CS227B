var manager = "manager";
var player = "hail_mary_pts";

var role = "robot";
var rules = [];
var startclock = 10;
var playclock = 10;

var library = [];
var roles = [];
var state = [];
var tree = {};

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
  var reward = parseInt(findreward(role, state, library));
  tree = makenode(state, findcontrol(state, library), reward);
  return "ready";
}

function play(move) {
  if (move !== nil) {
    tree = subtree(move, tree);
    state = tree.state;
  }
  if (findcontrol(state, library) !== role) { return false; }
  var deadline = Date.now() + (playclock - 2) * 1000;
  while (Date.now() < deadline) { process(tree); }
  return selectaction(tree);
}

function stop(move) { return false; }
function abort() { return false; }

//==============================================================================

function makenode(state, mover, reward) {
  return { state:state, actions:[], children:[], mover:mover, utility:reward, visits:0 };
}

function process(node) {
  if (findterminalp(node.state, library)) { return true; }
  if (node.children.length === 0) { expand(node); }
  else { process(select(node)); }
  update(node);
  return true;
}

function expand(node) {
  node.actions = findlegals(node.state, library);
  for (var i = 0; i < node.actions.length; i++) {
    var newstate = simulate(node.actions[i], node.state, library);
    var newmover = findcontrol(newstate, library);
    var newscore = parseInt(findreward(role, newstate, library));
    node.children[i] = makenode(newstate, newmover, newscore);
  }
  return true;
}

function select(node) {
  var total = node.visits;
  var best = node.children[0];
  var score = value(best.utility, best.visits, total);
  for (var i = 1; i < node.children.length; i++) {
    var newscore = value(node.children[i].utility, node.children[i].visits, total);
    if (newscore > score) { best = node.children[i]; score = newscore; }
  }
  return best;
}

function value(utility, visits, total) {
  return utility + Math.round((1 - visits / (total + 1)) * 100);
}

function update(node) {
  if (node.mover === role) { node.utility = scoremax(node); }
  else { node.utility = scoremin(node); }
  node.visits = node.visits + 1;
  return true;
}

function scoremax(node) {
  var score = node.children[0].utility;
  for (var i = 1; i < node.children.length; i++) {
    if (node.children[i].utility > score) { score = node.children[i].utility; }
  }
  return score;
}

function scoremin(node) {
  var score = node.children[0].utility;
  for (var i = 1; i < node.children.length; i++) {
    if (node.children[i].utility < score) { score = node.children[i].utility; }
  }
  return score;
}

function selectaction(node) {
  if (node.children.length === 0) { expand(node); }
  var best = node.actions[0];
  var score = node.children[0].utility;
  for (var i = 1; i < node.children.length; i++) {
    if (node.children[i].utility > score) {
      best = node.actions[i];
      score = node.children[i].utility;
    }
  }
  return best;
}

function subtree(move, node) {
  if (node.children.length === 0) { expand(node); }
  for (var i = 0; i < node.actions.length; i++) {
    if (equalp(move, node.actions[i])) { return node.children[i]; }
  }
  return node;
}

//==============================================================================