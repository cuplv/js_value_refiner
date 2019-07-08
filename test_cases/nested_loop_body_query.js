var o1 = {foo: null, bar: null};
var o2 = {baz: null, qux: null};
for (var p1 in o1) {
    for (var p2 in o2){
	var x = p1 + p2
    }
}
