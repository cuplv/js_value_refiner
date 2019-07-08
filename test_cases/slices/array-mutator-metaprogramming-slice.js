// LIBRARY
  var _ = function(obj) {
    if (obj instanceof _) return obj;
    if (!(this instanceof _)) return new _(obj);
    this._wrapped = obj;
  };
  _.VERSION = '1.8.3';
  var isArrayLike = function(collection) {
    var length = collection.length;
      return typeof length == 'number' && length >= 0;
  };
  _.each = _.forEach = function(obj, iteratee, context) {

    var i, length;
    if (isArrayLike(obj)) {
      for (i = 0, length = obj.length; i < length; i++) {
        iteratee(obj[i], i, obj);
      }
    } else {
      var keys = _.keys(obj);
      for (i = 0, length = keys.length; i < length; i++) {
        iteratee(obj[keys[i]], keys[i], obj);
      }
    }
    return obj;
  };
  // Add all mutator Array functions to the wrapper.

  _.each(['pop', 'push', 'reverse', 'shift', 'sort', 'splice', 'unshift'], function(name) {
    var method = Array.prototype[name];
    _.prototype[name] = function() {
      var obj = this._wrapped;
      method.apply(obj, arguments);
      if ((name === 'shift' || name === 'splice') && obj.length === 0) delete obj[0];
      return obj;
    };
  });

// CLIENT
var abcd = _(["A", "B", "C"]).push("D")
TAJS_assertEquals(4, abcd.length)

