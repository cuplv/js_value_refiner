var x = true

while(false) {
    x = false;
}

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(x) {} else {throw "Error"}
