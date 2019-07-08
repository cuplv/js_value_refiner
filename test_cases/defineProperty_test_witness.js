var o = {}
Object.defineProperty(o, "x", {value: "foo"})

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(o.x == "foo") {} else {throw "Error"}
