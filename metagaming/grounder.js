//==============================================================================
// grounder.js
// requires epilog.js
// assumes rules are relationally indexed
//==============================================================================

var deadline = 0;

//==============================================================================
// groundrules
//==============================================================================

function groundrules (rules,limit)
 {if (limit===undefined) {limit = 5000};
  var facts = groundfacts(rules,limit);
  if (facts===false) {return false};
  var actions = compactions(rules);
  var exprs = facts.concat(actions);
  var newrules = [];
  for (var i=0; i<rules.length; i++)
      {try {newrules = groundrule(rules[i],exprs,newrules)}
       catch (err) {return false}};
  return zniquify(newrules)}

function groundrule (rule,facts,rules)
 {if (symbolp(rule)) {rules[rules.length] = rule; return rules};
  if (rule[0]==='rule') {return groundviewrule(rule,facts,rules)};
  if (rule[0]==='handler') {return groundhandler(rule,facts,rules)};
  rules[rules.length] = rule;
  return rules}

function groundviewrule (rule,facts,rules)
 {return rules.concat(findall(rule,maksand(rule.slice(2)),facts))}

function groundhandler (rule,facts,rules)
 {var condition = rule[1];
  if (!symbolp(rule[2]) && rule[2][0]==='transition')
     {condition = makeconjunction(condition,rule[2][1])};
  return rules.concat(findall(rule,condition,facts))}

//==============================================================================
// groundfacts
//==============================================================================

function groundfacts (rules,limit)
 {if (!groundablep(rules)) {return false};
  if (limit===undefined) {limit = 5000};
  deadline = Date.now()+limit;
  var bases = compbases(rules);
  var atoms = compatoms(rules);
  var facts = bases.concat(atoms);
  for (var i=0; i<facts.length; i++) {fullindex(facts[i],facts[i],facts)};
  for (var i=0; i<facts.length; i++)
      {try {facts = addconsequences(facts[i],facts,rules)}
       catch (err) {return false}};
  return facts}

function addconsequences (fact,facts,rules)
 {for (var i=0; i<rules.length; i++)
      {addruleconsequences(fact,rules[i],facts)}
  return facts}

function addruleconsequences (fact,rule,facts)
 {if (symbolp(rule)) {return facts};
  if (rule[0]!=='rule') {return facts};
  for (var i=2; i<rule.length; i++)
      {var subgoal = rule[i];
       if (!symbolp(subgoal) && subgoal[0]==='not') {subgoal = rule[i][1]};
       var al = matcher(subgoal,fact);
       if (al) {userule(2,rule,al,facts)}};
  return facts}

function userule (n,rule,al,facts)
 {if (Date.now()>deadline) {throw "Timeout"};
  if (n>=rule.length) {compsave(plug(rulehead(rule),al),facts); return true};
  if (!symbolp(rule[n]) && rule[n][0]==='distinct')
     {if (!equalp(plug(rule[n][1],al),plug(rule[n][2],al)))
         {userule(n+1,rule,al,facts)};
      return true};
  if (!symbolp(rule[n]) && rule[n][0]==='not')
     {userule(n+1,rule,al,facts); return true};
  var data = indexees(operator(rule[n]),facts);
  for (var i=0; i<data.length; i++)
      {var bl = match(rule[n],data[i],al);
       if (bl) {userule(n+1,rule,bl,facts)}};
  return true}

function compsave (fact,facts)
 {if (find(fact,fullindexps(fact,facts))) {return fact};
  facts.push(fact);
  fullindex(fact,fact,facts);
  return fact}

function rulehead (p)
 {if (symbolp(p)) {return p};
  if (p[0]==='rule') {return p[1]};
  return p}

//==============================================================================

function groundablep (rules)
 {for (var i=0; i<rules.length; i++)
      {if (!groundablerulep(rules[i])) {return false}};
  return true}

function groundablerulep (rule)
 {if (symbolp(rule)) {return true};
  if (rule[0]==='rule')
     {for (var j=2; j<rule.length; j++)
          {if (!groundablegoalp(rule[j])) {return false}}};
  if (rule[0]==='handler')
     {if (symbolp(rule[2])) {return true};
      if (rule[2][0]!=='transition') {return true};
      return groundablegoalp(rule[2][1])};
  return true}

function groundablegoalp (p)
 {if (symbolp(p)) {return true};
  if (p[0]==='countofall') {return false};
  if (p[0]==='not') {return groundablegoalp(p[1])};
  if (p[0]==='and' || p[0]==='or')
     {for (var j=1; j<p.length; j++)
          {if (!groundablegoalp(p[j])) {return false}}};
  return true}

//==============================================================================

function compatoms (rules)
 {var bases = [];
  for (var i=0; i<rules.length; i++)
      {if (symbolp(rules[i])) {bases.push(rules[i])};
       if (rules[i][0]==='rule') {continue};
       if (rules[i][0]==='handler') {continue};
       bases.push(rules[i])};
  return bases}

//==============================================================================

function compbases (rules)
 {return compfinds('P',seq('base','P'),seq(),rules)}

//==============================================================================

function compactions (rules)
 {return compfinds('A',seq('action','A'),seq(),rules).sort()}

//==============================================================================

function findall (x,p,facts)
 {return findallexp(x,p,[],nil,[],facts)}

function findallexp (x,p,pl,al,results,facts)
 {if (Date.now()>deadline) {throw "Timeout"};
  if (symbolp(p))  {return findallbase(x,p,pl,al,results,facts)};
  if (p[0]==='plus') {return findallplus(x,p,pl,al,results,facts)};
  if (p[0]==='minus') {return findallminus(x,p,pl,al,results,facts)};
  if (p[0]==='leq') {return findallleq(x,p,pl,al,results,facts)};
  if (p[0]==='same') {return findallsame(x,p,pl,al,results,facts)};
  if (p[0]==='distinct') {return findalldistinct(x,p,pl,al,results,facts)};
  if (p[0]==='not') {return findallexit(x,pl,al,results,facts)};
  if (p[0]==='and') {return findalland(x,p,pl,al,results,facts)};
  return findallbase(x,p,pl,al,results,facts)}

function findallatom (x,p,pl,al,results,facts)
 {if (findq(p,facts)) {return findallexit(x,pl,al,results,facts)};
  return results}

function findallplus (x,p,pl,al,results,facts)
 {var result = 0;
  for (var i=1; i<p.length-1; i++)
      {var arg = plug(p[i],al);
       var val = numberize(arg);
       if (isNaN(val)) {return results};
       result = result + val};
  var bl = match(p[p.length-1],stringize(result),al);
  if (bl) {return findallexit(x,pl,bl,results,facts)};
  return results}

function findallminus (x,p,pl,al,results,facts)
 {var start = plug(p[1],al);
  var result = numberize(start);
  if (isNaN(result)) {return results};
  for (var i=2; i<p.length-1; i++)
      {var arg = plug(p[i],al);
       var val = numberize(arg);
       if (isNaN(val)) {return results};
       result = result - val};
  var bl = match(p[p.length-1],stringize(result),al);
  if (bl) {return findallexit(x,pl,bl,results,facts)};
  return results}

function findallleq (x,p,pl,al,results,facts)
 {p = plug(p,al);
  var argx = numberize(p[1]);
  var argy = numberize(p[2]);
  if (isNaN(argx)) {return results};
  if (isNaN(argy)) {return results};
  if (argx<=argy) {return findallexit(x,pl,al,results,facts)};
  return results}

function findallsame (x,p,pl,al,results,facts)
 {p = plug(p,al);
  if (equalp(p[1],p[2])) {return findallexit(x,pl,al,results,facts)};
  return results}

function findalldistinct (x,p,pl,al,results,facts)
 {p = plug(p,al);
  if (equalp(p[1],p[2])) {return results};
  return findallexit(x,pl,al,results,facts)}

function findalland (x,p,pl,al,results,facts)
 {return findallexp(x,p[1],p.slice(2).concat(pl),al,results,facts)}

function findallbase (x,p,pl,al,results,facts)
 {for (var i=0; i<facts.length; i++)
      {var bl = match(p,facts[i],al);
       if (bl) {results = findallexit(x,pl,bl,results,facts)}};
  return results}

function findallexit (x,pl,al,results,facts)
 {if (pl.length===0) {results.push(plug(x,al)); return results};
  return findallexp(x,pl[0],pl.slice(1),al,results,facts)}

//==============================================================================
// End
//==============================================================================