var x = true;
var y = false;

x = y;

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(x == y) {} else {throw "Error"}
