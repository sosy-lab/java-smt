# Known Solver Issues

## Princess

 - Princess is recursive and might require a large amount of stack memory.
If you experience stack overflows or Princess returns `OutOfMemory`,
try increasing the stack size with the JVM parameter `-Xss`.
 - Requesting termination via the [ShutdownNotifier][] works only in limited circumstances.

## SMTInterpol

 - SMTInterpol does not support multiple concurrent stacks under the same context.
 - Variables and UFs that are used for the first time after a solver stack has been created
will be deleted on the next call to `pop()` and will be invalid afterwards.
This will change with one of the next SMTInterpol versions (cf. [#69](https://github.com/sosy-lab/java-smt/issues/69)).

## Z3

 - Z3 interpolation procedure might require a large amount of stack memory.
If you get segmentation fault on interpolation, try increasing the stack size 
with the JVM parameter `-Xss`.
