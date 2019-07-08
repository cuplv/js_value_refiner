// LIBRARY
var _ = {}
_.keys = function(obj) {
    if (typeof obj != "object") return [];
    var keys = [];
    for (var key in obj) if (_.has(obj, key)) keys.push(key);
    return keys;
};
_.has = function(obj, key) {
    return obj != null && hasOwnProperty.call(obj, key);
};
_.map = function(obj, iteratee) {
    var keys = _.keys(obj),
        length = keys.length,
        results = Array(length)
    for (var index = 0; index < length; index++) {
	var currentKey = keys ? keys[index] : index;
	results[index] = iteratee(obj[currentKey]);
    }
    return results;
};

// CLIENT
var memo = {}
var f = function(x){ return x * x; }
var memo_f = function(x){ memo[x] = f(x) }
o = {a: 1, b: 2, c: 3}
_.map(o,memo_f)
TAJS_assertEquals(memo[3], 9);
