var x = {n : 1}
var y = x
var z = y
x.n = 2
y.n = 3
z.n = 4

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(x.n == y.n) {} else {throw "Error"}
