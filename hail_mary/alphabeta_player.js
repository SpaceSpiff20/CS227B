<script type='text/javascript'>

//==============================================================================
// Alpha-Beta Player
//==============================================================================

var manager = 'manager';
var player = 'hail_mary_alphabeta';

var role = 'robot';
var rules = [];
var startclock = 10;
var playclock = 10;

var library = [];
var roles = [];
var state = [];

//==============================================================================

function ping () { return 'ready'; }

function start (r,rs,sc,pc)
{
  role = r;
  rules = rs.slice(1);
  startclock = numberize(sc);
  playclock = numberize(pc);
  library = definemorerules([],rules);
  roles = findroles(library);
  state = findinits(library);
  return 'ready';
}

//==============================================================================
// MAIN PLAY FUNCTION
//==============================================================================

function play (move)
{
  if (move !== nil) {
    state = simulate(move, state, library);
  }

  if (findcontrol(state, library) !== role) {
    return false;
  }

  var moves = findlegals(state, library);
  var bestMove = moves[0];
  var bestScore = -Infinity;

  for (var i = 0; i < moves.length; i++) {
    var next = simulate(moves[i], state, library);
    var score = alphabeta(next, -Infinity, Infinity);

    if (score > bestScore) {
      bestScore = score;
      bestMove = moves[i];
    }
  }

  return bestMove;
}

//==============================================================================
// ALPHA-BETA SEARCH
//==============================================================================

function alphabeta(state, alpha, beta)
{
  if (findterminal(state, library)) {
    return findreward(role, state, library);
  }

  var control = findcontrol(state, library);

  if (control === role) {
    return maxValue(state, alpha, beta);
  } else {
    return minValue(state, alpha, beta);
  }
}

function maxValue(state, alpha, beta)
{
  var moves = findlegals(state, library);
  var value = -Infinity;

  for (var i = 0; i < moves.length; i++) {
    var next = simulate(moves[i], state, library);
    value = Math.max(value, alphabeta(next, alpha, beta));

    if (value >= beta) {
      return value; // PRUNE
    }

    alpha = Math.max(alpha, value);
  }

  return value;
}
function minValue(state, alpha, beta)
{
  var moves = findlegals(state, library);
  var value = Infinity;

  for (var i = 0; i < moves.length; i++) {
    var next = simulate(moves[i], state, library);
    value = Math.min(value, alphabeta(next, alpha, beta));

    if (value <= alpha) {
      return value; // PRUNE
    }
    beta = Math.min(beta, value);
  }

  return value;
}

function stop (move) { return false; }
function abort () { return false; }

</script>
