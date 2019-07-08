var o = {prop : 0}
// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
var x = "prop"
if(o[x] == 1) {} else {throw "Error"}
