// LIBRARY
var _ = {}
_.times = function(n, iteratee) {
    var accum = Array(n);
    for (var i = 0; i < n; i++) accum[i] = iteratee(i);
    return accum;
};

// CLIENT

var f = function(x) { return x * x }

var series = _.times(5,f)

TAJS_assert(series[4] == 16)
