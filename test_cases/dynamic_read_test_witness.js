var o = {foo : 0}
// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
var x = "fo"
if(o[x + "o"] == 0) {} else {throw "Error"}

