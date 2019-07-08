var x = function(){}
var y = new x()
x.prototype.n = 5

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(y.n != 5) {} else {throw "Error"}
