// POLYFILL
if (!Array.prototype.forEach) {
    Object.defineProperty(Array.prototype, "forEach", {
        writable: true, enumerable: false, configurable: true,
        value: function forEach(fun /*, thisArg */) {
            "use strict";
            TAJS_makeContextSensitive(fun, 1, {caller: forEach});
            TAJS_makeContextSensitive(fun, 2, {caller: forEach});
            if (this === void 0 || this === null)
                throw new TypeError();

            var t = Object(this);
            var len = t.length >>> 0;
            if (typeof fun !== "function")
                throw new TypeError();

            var thisArg = arguments.length >= 2 ? arguments[1] : void 0;
            for (var i = 0; i < len; i++) {
                if (i in t)
                    fun.call(thisArg, t[i], i, t);
            }
        }
    });
    TAJS_makeContextSensitive(Array.prototype.forEach, 0);
    TAJS_makeContextSensitive(Array.prototype.forEach, -1);
}

// LIBRARY
var _ = {};
_.each = function(obj, iterator, context) {
    obj.forEach(iterator, context);
};

_.each(['Arguments', 'Function', 'String', 'Number', 'Date', 'RegExp', 'Error'], function(name) {
    _['is' + name] = function(obj) {
	return toString.call(obj) === '[object ' + name + ']';
    };
});

var f = function(){}

TAJS_assert(_.isString("Hello!"))
TAJS_assert(_.isFunction(f))

