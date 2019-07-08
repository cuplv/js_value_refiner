var u = js_value_refiner_debug_top ? true: false;

var foo = function(){ return {sum: 0}; }
var x = foo()
var y = foo()
var do_stuff = function() {
    if(u){
	x.sum += 1;
    }
    if(u) {
	y.sum = "blah"
    }
    if(u){
	x.sum -= 1;
    }    
}
do_stuff();
if(x.sum == 0) {} else {throw "Error"}
