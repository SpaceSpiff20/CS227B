//==============================================================================
// pruner.js
// assumes rules are grounded and symbolized and simplified
// except for role, base, action, init, control, legal, goal
// assumes rules are rule indexed
//==============================================================================

var deadline = 0;

//==============================================================================
// pruneprogram
//==============================================================================

function pruneprogram (role,rules)
 {deadline = Date.now()+5000;
  var index = indexrules(rules.slice());
  var props = getgoalprops (role,rules);
  var actions = [];
  for (var i=0; i<props.length; i++)
      {try {actions = compchangers(props[i],actions,rules,index)}
       catch (err) {return rules}};
  var actions = compchangers('terminal',actions,rules,index);
  for (var i=0; i<actions.length; i++)
      {var prop = symbolizeatom(seq('legal',actions[i]));
       actions = compchangers(prop,actions,rules,index);
       actions = compchangersbase(actions[i],actions,rules,index);
       actions = compenablers(actions[i],actions,rules,index)};
  return adjustlegalities(actions,rules)}

//==============================================================================
// pruneactions
//==============================================================================

function pruneactions (role,rules)
 {var index = indexrules(rules.slice());
  var props = getgoalprops (role,rules);
  var actions = [];
  for (var i=0; i<props.length; i++)
      {actions = compchangers(props[i],actions,rules,index)};
  var actions = compchangers('terminal',actions,rules,index);
  for (var i=0; i<actions.length; i++)
      {var action = symbolizeatom(seq('legal',actions[i]));
       actions = compchangers(action,actions,rules,index);
       actions = compchangersbase(actions[i],actions,rules,index);
       actions = compenablers(actions[i],actions,rules,index)};
  return actions.sort()}

//==============================================================================
// indexrules
//==============================================================================

function indexrules (rules)
 {for (var i=0; i<rules.length; i++)
      {relindex(rules[i],rules[i],rules)};
  return rules}

function relindex (x,p,rules)
 {if (varp(x)) {return p};
  if (symbolp(x)) {return indexsymbol(x,p,rules)};
  if (x[0]==='rule' || x[0]==='handler' || x[0]==='definition' ||
      x[0]==='transition' || x[0]==='not' || x[0]==='and' || x[0]==='or')
     {for (var i=1; i<x.length; i++) {relindex(x[i],p,rules)}};
  return indexsymbol(x[0],p,rules)}

//==============================================================================
// getgoalprops
//==============================================================================

function getgoalprops (role,rules)
 {var data = indexees('goal',rules);
  var props = [];
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue};
       if (data[i][0]!=='rule') {continue};
       if (symbolp(data[i][1])) {continue};
       if (data[i][1][0]==='goal' && data[i][1][1]===role)
          {props = adjoinit(data[i][1],props)}}
  return props}

//==============================================================================
// compchangers
//==============================================================================

function compchangers (p,results,rules,index)
 {if (symbolp(p))
     {if (basep(p,rules)) {return compchangersbase(p,results,rules,index)};
      return compchangersdb(p,results,rules,index)};
  if (p[0]==='not') {return compchangersdb(p[1],results,rules,index)};
  if (p[0]==='and')
     {for (var i=1; i<p.length; i++)
          {results = compchangers(p[i],results,rules,index)};
      return results};
  if (basep(p[0],rules)) {return compchangersbase(p,results,rules,index)};
  return compchangersdb(p,results,rules,index)}

function compchangersdb (p,results,rules,index)
 {var data = indexees(operator(p),rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue};
       if (data[i][0]==='rule' && equalp(data[i][1],p))
          {for (var j=2; j<data[i].length; j++)
               {results = compchangers(data[i][j],results,rules,index)}}};
  return results}

//==============================================================================

function compchangersbase (p,results,rules,index)
 {var data = indexees(operator(p),index);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue};
       if (data[i][0]==='handler' && symbolp(data[i][2]))
          {if (data[i][2]===p)
              {results = adjoin(data[i][1],results)};
           continue};
       if (data[i][0]==='handler' && data[i][2][0]==='transition')
          {if (mentions(data[i][2][2],p))
              {results = adjoin(data[i][1],results)}
           continue};
       if (data[i][0]==='handler' && mentions(data[i][2],p))
          {results = adjoin(data[i][1],results)}};
  return results}

function mentions (item,factoid)
 {if (symbolp(item)) {return (item===factoid)};
  if (item[0]==='not') {return equalp(item[1],factoid)};
  if (item[0]==='and')
     {for (var i=1; i<item.length; i++)
          {if (mentions(item[i],factoid)) {return true}};
      return false};
  return equalp(item,factoid)}

//==============================================================================

function compenablers (x,results,rules,index)
 {var data = indexees(operator(x),rules);
  for (var i=0; i<data.length; i++)
      {if (symbolp(data[i])) {continue};
       if (data[i][0]!=='handler') {continue};
       if (!equalp(data[i][1],x)) {continue};
       if (symbolp(data[i][2])) {continue};
       if (data[i][2][0]!=='transition') {continue};
       results = compchangers(data[i][2][1],results,rules,index)};
  return compchangers(x,results,rules,index)}

//==============================================================================
// adjustlegalities
//==============================================================================

function adjustlegalities (actions,rules)
 {var oldlegals = indexees('legal',rules);
  var newlegals = getlegalities(actions,oldlegals);
  return difference(rules,oldlegals).concat(newlegals)}

function getlegalities (actions,rules)
 {var legals = [];
  for (var i=0; i<rules.length; i++)
      {var head = rulehead(rules[i]);
       if (!symbolp(head) && head[0]==='legal' && findp(head[1],actions))
       legals.push(rules[i])};
  return legals}

//==============================================================================
// End
//==============================================================================