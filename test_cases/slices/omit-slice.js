//LIBRARY
var _ = {}
_.contains = _.includes = _.include = function(obj, item, fromIndex, guard) {
    if (typeof fromIndex != 'number' || guard) fromIndex = 0;
    return _.indexOf(obj, item, fromIndex) >= 0;
};
_.allKeys = function(obj) {
    var keys = [];
    for (var key in obj) keys.push(key);
    // Ahem, IE < 9.
    return keys;
};
_.pick = function(object, oiteratee, context) {
    var result = {}, obj = object, iteratee, keys;
    if (obj == null) return result;
    if (_.isFunction(oiteratee)) {
	keys = _.allKeys(obj);
	iteratee = oiteratee //optimizeCb(oiteratee, context);
    } else {
	keys = flatten(arguments, false, false, 1);
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

// Return a copy of the object without the blacklisted properties.
_.omit = function(obj, blacklist, context) {
    iteratee = function(value, key) {
	for(idx in blacklist) {
	    if(blacklist[idx] == key) return false
	}
	return true
    };
    return _.pick(obj, iteratee, context);
};

_.isFunction = function(obj) {
    return typeof obj == 'function' || false;
};


//CLIENT

var foo = function() {return "foo";},
    bar = function() {return "bar";};

var obj = {foo: foo, bar: bar};
var obj_prime = _.omit(obj, ["bar"]);

TAJS_assertEquals(undefined, obj_prime.bar);
TAJS_assertEquals(foo, obj_prime.foo)
