var x = 0
var z = 0

while(x < 5) { 
    x += 1

    var y = 2
    while(y > 0) {
	y -= 1
    }
}

// Using this if-statement as a pseudo-assert
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(z != 0) {} else {throw "Error"}
