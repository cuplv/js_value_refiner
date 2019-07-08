var x = {n : 5}
var o = {}
var y = {__proto__ : o}
var z = {__proto__ : y}

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(z.n && (z.n != 5)) {} else {throw "Error"}
