// LIBRARY
var _ = {}
_.pick = function(object, oiteratee, context) {
    var result = {}, obj = object, iteratee, keys;
    if (obj == null) return result;
    if (_.isFunction(oiteratee)) {
	keys = _.allKeys(obj);
	iteratee = optimizeCb(oiteratee, context);
    } else {
	keys = oiteratee
	iteratee = function(value, key, obj) { return key in obj; };
	obj = Object(obj);
    }
    for (i in keys){
	var key = keys[i];
	var value = obj[key];
	if (iteratee(value, key, obj)) result[key] = value;
    }
    return result;
};
_.isFunction = function(obj) {
    return typeof obj == 'function' || false;
};

// CLIENT

var obj = {
    foo: function() {return "foo";},
    bar: function() {return "bar";},
    baz: function() {return "baz";}
}

var obj_prime = _.pick(obj, ['bar']);

TAJS_assertEquals(undefined, obj_prime.foo)
TAJS_assertEquals(undefined, obj_prime.bar)
TAJS_assertEquals(obj.bar, obj_prime.bar)
