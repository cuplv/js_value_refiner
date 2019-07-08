var x = {n : 1}
var y = x
y.n = 2
x.n = 3

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(x.n != y.n) {} else {throw "Error"}
