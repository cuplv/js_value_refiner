var u = js_value_refiner_debug_top ? true: false;
var sum = 0;
if(u){
  sum += 1;
}
if(u){
  sum -= 1;
}
if(sum == 0) {} else {throw "Error"}
