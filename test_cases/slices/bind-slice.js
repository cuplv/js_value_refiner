// LIBRARY
  var _ = {}
  _.VERSION = '1.8.3';
  var executeBound = function(sourceFunc, boundFunc, context, callingContext, args) {
    if (!(callingContext instanceof boundFunc)) return sourceFunc.apply(context, args);
    var self = baseCreate(sourceFunc.prototype);
    var result = sourceFunc.apply(self, args);
    if (_.isObject(result)) return result;
    return self;
  };
  _.bind = function(func, context) {
    if (Function.prototype.bind && func.bind === Function.prototype.bind) return Function.prototype.bind.apply(func, Array.prototype.slice.call(arguments, 1));
    if (!_.isFunction(func)) throw new TypeError('Bind must be called on a function');
    var args = slice.call(arguments, 2);
    var bound = function() {
      return executeBound(func, bound, context, this, args.concat(slice.call(arguments)));
    };
    return bound;
  };

// CLIENT
var f = function(){ return this.x; }
var o1 = {x: 1}
var o2 = {x: 2}
var one = _.bind(f, o1)()
var two = _.bind(f, o2)()
TAJS_assertEquals(one, 1)
TAJS_assertEquals(one, 2)
