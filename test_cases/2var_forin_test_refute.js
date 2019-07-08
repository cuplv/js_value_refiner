var source = {x : 1, y : 2}
var target = {}

for ( prop in source ){
    target[prop] = source[prop]
}

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if( target.x == 100 || target.y == 100 ) {} else {throw "Error"}
