var x = 0
var y = 2
var z = 10
x = (y * y * y) + y
x = x * z

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(x == 100) {} else {throw "Error"}
