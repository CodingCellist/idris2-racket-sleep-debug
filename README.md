# idris2-racket-sleep-debug
Debugging the Idris2 `sleep` function under the Racket codegen (cg).

# Overview
- **00-motivating-example:** Contains Idris2 code and modified versions of the
    Racket codegen which show that the odd behaviour is to do with the
    `System-sleep` function from the cg.
- **01-minimal-example:** Contains C and Racket code which show that the problem
    occurs on Racket FFI-calls to C's `nanosleep`. (Note: Using `unistd.h`
    instead of `time.h` and `sleep` instead of `nanosleep` respectively,
    achieves the same odd behaviour...)

# Problem description
When using the `fork` function supplied by
[Idris2 PR #968](https://github.com/idris-lang/Idris2/pull/968) and the `sleep`
function to force things to happen in a certain order, the threads seem to run
sequentially (with the main thread run first, then the children) when using the
Racket cg.

# Running
For the C files, first run `make`. This is especially important for the minimal
example, since the shared library otherwise doesn't exist. Then run the
resulting executable

For the Racket files, run `racket <filename>.rkt`.

For the Idris files, run
```
idris2 --no-banner --no-colour --cg racket <filename>.idr --exec main
```
optionally using `dmain` instead of main to run the desugared `main` function in
`desugar.idr`.

