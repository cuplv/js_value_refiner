var x = 0

while(x < 5){
    x += 1
}

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(x >= 5) {} else {throw "Error"}
