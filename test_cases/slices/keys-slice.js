// LIBRARY
  var _ = {}
  _.VERSION = '1.8.3';
  _.keys = function(obj) {
    if (typeof obj != "object") return [];
    var keys = [];
    for (var key in obj) if (_.has(obj, key)) keys.push(key);
    return keys;
  };
  _.has = function(obj, key) {
    return obj != null && hasOwnProperty.call(obj, key);
  };

// CLIENT
var o = {foo: 'bar'}
TAJS_assertEquals(_.keys(o)[0], 'foo')
