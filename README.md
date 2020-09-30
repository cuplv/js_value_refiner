# JavaScript Value Refiner
[Demand-Driven Value Refinement](http://plv.colorado.edu/benno/oopsla19.pdf) for JavaScript

This repository contains the source for a value refinement engine for JavaScript, based on the technique described in the paper linked above.
The analysis operates over TAJS IR and is tightly integrated with a [fork](https://github.com/cs-au-dk/tajs_vr) of the TAJS analysis, which issues queries on-demand to this refiner whenever it encounters imprecise property accesses.

To build the combined analysis, perform the following steps:

1. Ensure dependencies are satisfied:
 * Java 8
 * Scala 2.10
 * `ant`
 * `sbt`
 
2. `git clone https://github.com/cs-au-dk/tajs_vr_experiments`

3. `cd tajs_vr_experiments`

4. `git submodule update --init --recursive`

5. `ant`

Then, the analysis can be run as specified [here](https://github.com/cs-au-dk/tajs_vr_experiments#running-tajs-vr-experiments), either by using pre-configured settings to analyze the paper's benchmarks or by passing custom settings to analyze other JavaScript programs.
