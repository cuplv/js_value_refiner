var F = function(a){this.x = a}
var o = {f : F}
o.f(5)

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if (o.x == 5) {} else {throw "Error"}
