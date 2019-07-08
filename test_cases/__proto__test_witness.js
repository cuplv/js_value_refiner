var x = {n : 5}
var y = {__proto__ : x}
var z = {__proto__ : y}

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(z.n == 5) {} else {throw "Error"}
