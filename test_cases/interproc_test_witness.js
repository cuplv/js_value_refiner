var f = function(){return 1}
var g = function(){return f()}
// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(g() == 1) {} else {throw "Error"}
