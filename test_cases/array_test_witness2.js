var arr = {0 : 'foo', 1 : 'bar'}

// Using this if-statement as a pseudo-assert.
// I.E. checking reachability of the program endpoint is equivalent to checking the condition
if(arr[0] + arr[1] == 'foobar') {} else {throw "Error"}

