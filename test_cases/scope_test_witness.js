var x = 0

var f = function() { x = 1; } 

var g = function() {var x = 2;  f(); x = 0}

g()

if (x == 1) {} else {throw "Error"}
