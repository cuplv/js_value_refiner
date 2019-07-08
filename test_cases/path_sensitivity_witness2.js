var u = js_value_refiner_debug_top;
//var foo = function(){ return {x: 0, y: 0, z: 0}; }
var o = {x: 0, y: 0, z: 0}
// o.x == 0
if(u){
    o.x += 1
} else {
    o.x += 1
}
// o.x == 1

if(!u) {
    o.y -= 1
    o.z = "foobarbaz"
}
o.x += 1
//o.x == 2
for(p in o){
    o[p] += 1
    if(p == 'x'){
	o[p] += 1
    }
}
//o.x == 4
for(p in o){
    o[p] += 1
}
//o.x == 5
if(o.x == 5) {} else {throw "Error"}
