var x = {}
var y = {}
x.n = 3
y.n = 5
// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if((x.n * x.m * y.n) == 60) {} else {throw "Error"}
