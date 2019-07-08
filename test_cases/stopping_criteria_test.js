//3 Stopping criteria: 
//    D: DefiniteValueFound; stop as soon as the tracked expression has no symbolic variables in it.  weakest/fastest possible strategy
//    F: FunctionEntrypoint; stop as soon as the tracked expression has no symbolic variables in it, AND we've reached the entrypoint of the function in which the query originated
//    P: ProgramEntrypoint; execute all the way back to the program entrypoint.  strongest/slowest possible strategy

// x==5 at end of function j: Refuted by D,F,P
// x==5 at end of function f: Refuted by F,P
// x==5 at end of function h: Refuted by P
// x==5 at end of function i: not refuted

function f() {
    if(false){
	x=5
    } else {
	throw "Error"
    }
    x//no op
}

function g(){
    if(false)
      {h()}
}


function h(){
    x = 5
}

function i(){
    x = 5
}

function j(){
    x = 5

    if(true){throw "Error"}
    x
}

i()
f()
g()
j()
