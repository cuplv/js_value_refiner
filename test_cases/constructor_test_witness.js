var F = function(){this.x = 5}
var o = new F()

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if (o.x == 5) {} else {throw "Error"}
