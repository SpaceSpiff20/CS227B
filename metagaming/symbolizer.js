//==============================================================================
// symbolizer.js
// requires epilog.js
// assumes rules are grounded
// produces symbolized rules
// except for role, base, action, init, control, legal, goal, possibly builtins
// angle brackets not idchars in epilog.js; use symbol.js or hybrid.js
//==============================================================================

function symbolizerules (rules)
 {var newrules = controlrules(rules);
  var newrules = newrules.concat(legalrules(rules));
  var newrules = newrules.concat(goalrules(rules));
  return newrules.concat(rules.map(symbolize))};

function controlrules (rules)
 {var newrules = [];
  for (var i=0; i<rules.length; i++)
      {var fact = gethead(rules[i]);
       if (!symbolp(head) && fact[0]==='role')
          {fact = seq('control',fact[1]);
           newrules.push(seq('rule',fact,symbolizeatom(fact)))}};
   return uniquify(newrules)}

function legalrules (rules)
 {var newrules = [];
  for (var i=0; i<rules.length; i++)
     {var fact = gethead(rules[i]);
       if (!symbolp(fact) && fact[0]==='legal')
          {var head = seq('legal',symbolizeatom(fact[1]));
           newrules.push(seq('rule',head,symbolizeatom(fact)))}};
   return zniquify(newrules)}

function goalrules (rules)
 {var newrules = [];
  for (var i=0; i<rules.length; i++)
     {var fact = gethead(rules[i]);
       if (!symbolp(fact) && fact[0]==='goal')
          {newrules.push(seq('rule',fact,symbolizeatom(fact)))}};
   return zniquify(newrules)}

function gethead (rule)
 {if (symbolp(rule)) {return rule};
  if (rule[0]==='rule') {return rule[1]};
  if (rule[0]==='handler') {return rule[1]};
  return rule}

function symbolize (p)
 {if (symbolp(p)) {return p};
  if (p[0]==='role') {return symbolizeparts(p)};
  if (p[0]==='base') {return symbolizeparts(p)};
  if (p[0]==='action') {return symbolizeparts(p)};
  if (p[0]==='init') {return symbolizeparts(p)};
  if (p[0]==='same') {return symbolizeparts(p)};
  if (p[0]==='distinct') {return symbolizeparts(p)};
  if (p[0]==='plus') {return symbolizeparts(p)};
  if (p[0]==='minus') {return symbolizeparts(p)};
  if (p[0]==='not') {return symbolizeparts(p)};
  if (p[0]==='and') {return symbolizeparts(p)};
  if (p[0]==='or') {return symbolizeparts(p)};
  if (p[0]==='rule') {return symbolizeparts(p)};
  if (p[0]==='transition') {return symbolizeparts(p)};
  if (p[0]==='handler') {return symbolizeparts(p)};
  return symbolizeatom(p)}

function symbolizeatom (p)
 {if (p===nil) {return p} else {p = grind(p)};
  p = p.replace(/,/g,"_");
  p = p.replace(/\x28/g,"<");
  p = p.replace(/\x29/g,">");
  return p} 

function unsymbolizeatom (p)
 {if (p===false) {return false};
  p = p.replace(/_/g,",");
  p = p.replace(/</g,"(");
  p = p.replace(/>/g,")");
  return read(p)} 

function symbolizeparts (p)
 {return p.map(symbolize)}

//==============================================================================
//==============================================================================
//==============================================================================