var a = false
var b = false

var o = {x : 1, y : 2}

for(var p in o) {
    if(p == "x")
        a = true
    else if (p == "y")
        b = true
}

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(a != b) {} else {throw "Error"}
