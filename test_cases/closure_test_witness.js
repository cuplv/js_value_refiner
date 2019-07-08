function counter(){
    var count = 0;
    return function(){ count += 1 ; return count }
}

var c1 = counter()
var c2 = counter()
c1()
c2()

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(c1() == 2) {} else {throw "Error"}
//TAJS_assert(c1()==2)