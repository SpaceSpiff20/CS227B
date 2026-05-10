//==============================================================================
// symbol.js
//==============================================================================
//==============================================================================
// Initialization
//==============================================================================

indexing = false;
dataindexing = false;
ruleindexing = true;

//==============================================================================
// symbol
//==============================================================================

function findroles (rules)
 {return compfinds('R',seq('role','R'),seq(),rules)}

function findbases (rules)
 {return compfinds('P',seq('base','P'),seq(),rules)}

function findactions (rules)
 {return compfinds('A',seq('action','A'),seq(),rules)}

function findinits (rules)
 {return makestate(basefinds('P',seq('init','P'),seq(),rules))}

function findcontrol (facts,rules)
 {return symbolitem('control',facts,rules)}

function findlegalp (move,facts,rules)
 {return symbolfindp(seq('legal',move),facts,rules)}

function findlegalx (facts,rules)
 {return symbolitem('legal',facts,rules)}

function findlegals (facts,rules)
 {return symbolitems('legal',facts,rules)}

function findreward (role,facts,rules)
 {var value = symbolvalue('goal',role,facts,rules);
  if (value) {return value};
  return 0}

function findterminalp (facts,rules)
 {return symbolfindp('terminal',facts,rules)}

function simulate (move,state,rules)
 {var deltas = symbolexpand(move,state,rules);
  var newstate = Object.assign({},state);
  for (var i=0; i<deltas.length; i++)
      {var delta = deltas[i];
       if (!symbolp(delta) && delta[0]==='not') {delete(newstate[delta[1]])}};
  for (var i=0; i<deltas.length; i++)
      {var delta = deltas[i];
       if (symbolp(delta)) {newstate[delta] = true; continue};
       if (delta[0]==='not') {continue};
       newstate[delta] = true};
  return newstate}

function makestate (facts)
 {var newstate = {};
  for (var i=0; i<facts.length; i++)
      {newstate[facts[i]] = true};
  return newstate}

//==============================================================================
// symbolfindp
// symbolitem
// symbolitems
// symbolvalue
// symbolvalues
// symbolexpand
//==============================================================================

function symbolfindp (p,facts,rules)
 {inferences = inferences + 1;
  if (symbolp(p)) {return symbolfindatom(p,facts,rules)};
  if (p[0]==='same') {return equalp(p[1],p[2])};
  if (p[0]==='distinct') {return !equalp(p[1],p[2])};
  if (p[0]==='not') {return !symbolfindp(p[1],facts,rules)};
  if (p[0]==='and') {return symbolfindand(p,facts,rules)};
  if (symbolfindbackground(p,facts,rules)) {return true};
  return symbolfindrs(p,facts,rules)}

function symbolcompute (rel,facts,rules)
 {var answers = seq();
  var data = facts;
  for (var i=0; i<data.length; i++)
      {if (operator(data[i])===rel) {answers.push(data[i])}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {if (equalp(data[i],rel)) {answers.push(rel)}}
       else if (data[i][0]!=='rule')
               {if (equalp(operator(data[i]),rel)) {answers.push(data[i])}}
       else {if (equalp(operator(data[i]),rel) &&
                 symbolfindsubs(data[i],facts,rules))
                {answers.push(data[i][1])}}};
  return uniquify(answers)}

function symbolfindatom (p,facts,rules)
 {if (p==='true') {return true};
  if (p==='false') {return false};
  if (symbolfindbackground(p,facts,rules)) {return true};
  return symbolfindrs(p,facts,rules)}

function symbolfindand (p,facts,rules)
 {for (var j=1; j<p.length; j++)
      {if (!symbolfindp(p[j],facts,rules)) {return false}};
  return true}

function symbolfindbackground (p,facts,rules)
 {return (facts[p]===true)}

function symbolfindrs (p,facts,rules)
 {var data = viewindexps(p,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {if (equalp(data[i],p)) {return true}}
       else if (data[i][0]!=='rule') {if (equalp(data[i],p)) {return true}}
       else {if (equalp(data[i][1],p) && symbolfindsubs(data[i],facts,rules))
                {return true}}};
  return false}

function symbolfindsubs (rule,facts,rules)
 {for (var j=2; j<rule.length; j++)
      {if (!symbolfindp(rule[j],facts,rules)) {return false}};
  return true}

function factindexps (p,theory)
 {if (symbolp(p)) {return indexees(p,theory)};
  var best = indexees(p[0],theory);
  for (var i=1; i<p.length; i++)
      {var dum = factindexps(p[i],theory);
       if (dum.length<best.length) {best = dum}};
  return best}

//------------------------------------------------------------------------------

function symbolitem (rel,facts,rules)
 {var data = facts;
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]===rel) {return data[i][1]}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]!=='rule')
               {if (data[i][0]===rel) {return data[i][1]}}
       else {var head = data[i][1];
             if (operator(head)===rel &&
                 symbolfindsubs(data[i],facts,rules))
                {return (head[1])}}};
  return false}

function symbolitems (rel,facts,rules)
 {var answers=seq();
  var data = facts;
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]===rel)
               {answers.push(data[i][1])}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]!=='rule')
               {if (data[i][0]===rel)
                   {answers.push(data[i][1])}}
       else {var head=data[i][1];
             if (operator(head)===rel &&
                 symbolfindsubs(data[i],facts,rules))
                {answers.push(head[1])}}};
  return uniquify(answers)}

function symbolvalue (rel,obj,facts,rules)
 {var data = facts;
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]===rel && data[i][1]===obj) {return data[i][2]}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]!=='rule')
               {if (data[i][0]===rel && data[i][1]===obj) {return data[i][2]}}
       else {var head=data[i][1];
             if (operator(head)===rel && equalp(head[1],obj) &&
                 symbolfindsubs(data[i],facts,rules))
                {return data[i][1][2]}}};
  return false}

function symbolvalues (rel,obj,facts,rules)
 {var answers=seq();
  var data = facts;
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]===rel && data[i][1]===obj)
               {answers.push(data[i][2])}};
  data = indexees(rel,rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue}
       else if (data[i][0]!=='rule')
               {if (data[i][0]===rel && data[i][1]===obj)
                   {answers.push(data[i][2])}}
       else {var head=data[i][1];
             if (operator(head)===rel && equalp(head[1],obj) &&
                 symbolfindsubs(data[i],facts,rules))
                {answers.push(head[2])}}};
  return uniquify(answers)}

//------------------------------------------------------------------------------

function symbolexpand (seed,facts,rules)
 {return zniquify(symbolexpanddepth(seed,facts,rules,0))}

function symbolexpanddepth (seed,facts,rules,depth)
 {if (symbolp(seed)) {return symbolexpanddepthrs(seed,facts,rules,depth)};
  if (seed[0]==='not') {return [seed]};
  if (seed[0]==='and') {return symbolexpanddepthand(seed,facts,rules,depth)};
  if (seed[0]==='transition') {return symbolexpanddepthtransition(seed,facts,rules,depth)};
  if (depth>expanddepth) {return []};
  return symbolexpanddepthrs(seed,facts,rules,depth)}

function symbolexpanddepthand (seed,facts,rules,depth)
 {var updates = [];
  for (var i=1; i<seed.length; i++)
      {updates = updates.concat(symbolexpanddepth(seed[i],facts,rules,depth))};
  return updates}

function symbolexpanddepthtransition (seed,facts,rules,depth)
 {var updates = [];
  if (symbolfindp(seed[1],facts,rules))
     {updates = updates.concat(symbolexpanddepth(seed[2],facts,rules,depth))};
  return updates}

function symbolexpanddepthrs (seed,facts,rules,depth)
 {var data = lookuprules(seed,rules);
  var flag = false;
  var updates = [];
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue};
       if (data[i][0]!=='handler') {continue};
       if (equalp(data[i][1],seed))
          {flag = true;
           var rule = data[i][2];
           updates = updates.concat(symbolexpanddepth(rule,facts,rules,depth+1))}};
  if (flag) {return updates};
  return [seed]}

//==============================================================================
// idcharp -  new definition of subroutine in epilog.js
// needed to read symbols containing angle brackets produced by symbolizer.js
//==============================================================================

function idcharp (charcode)
 {if (charcode===42) {return true};
  if (charcode===43) {return true};
  if (charcode===45) {return true};
  if (charcode===46) {return true};
  if (charcode===47) {return true};
  if (charcode >= 48 && charcode <= 57) {return true};
  if (charcode===60) {return true};
  if (charcode===62) {return true};
  if (charcode >= 65 && charcode <= 90) {return true};
  if (charcode >= 97 && charcode <= 122) {return true};
  if (charcode===95) {return true};
  return false}

//==============================================================================
//==============================================================================
//==============================================================================