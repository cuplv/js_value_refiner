// LIBRARY
  var _ = {}
  _.VERSION = '1.8.3';
  _.isMatch = function(object, attrs) {
      var keys = Object.keys(attrs), length = keys.length;
    if (object == null) return !length;
    var obj = Object(object);
    for (var i = 0; i < length; i++) {
      var key = keys[i];
      if (attrs[key] !== obj[key] || !(key in obj)) return false;
    }
    return true;
  };

// CLIENT
var obj = {x : 0}
var props_match = {x : 0}
var props_diff  = {x : 1}
TAJS_assert(_.isMatch(obj, props_match))
TAJS_assert(_.isMatch(obj, props_diff ), "isMaybeFalseButNotTrue")
