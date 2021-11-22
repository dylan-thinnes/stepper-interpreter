# Stepper-Interpreter

The stepper-interpreter takes an expression and shows all of the steps that
Haskell executes in order to finally reduce the expression.

For example, given the following expression:

```hs
let y = 3 + 5
    x = 2
in
x * y
```

The stepper-interpreter would display the following:

```hs
let y = 3 + 5
    x = 2
in
x * y
```

```hs
let y = 3 + 5
    x = 2
in
2 * y
```

```hs
let y = 3 + 5
    x = 2
in
2 * (3 + 5)
```

```hs
let y = 3 + 5
    x = 2
in
2 * 8
```

```hs
let y = 3 + 5
    x = 2
in
16
```

## Usage / Installation

### Prerequisites

Before running this, you will need `ghc` (the Glasgow Haskell Compiler),
`cabal` (a Haskell package manager), and `git` (a version control system). I
have only tested this on GHC 8.10.5.

If you do not have `ghc` or `cabal` installed, or would like to install a
different version of GHC, I recommend using [`ghcup`](https://www.haskell.org/ghcup/).

If you do not have `git` installed, I recommend searching "install git" in your
search engine of choice, and following the instructions.

### Building

In order to use the stepper-interpreter, begin by downloading the source code
and building it:

```sh
# Clone the repository
git clone https://github.com/dylan-thinnes/stepper-interpreter.git

# Change into the directory
cd stepper-interpreter

# Build with cabal
cabal build
```

### Running

The tool is currently a series of functions meant to be used from within GHCi
(the GHC interpreter). Begin by starting GHCi:

```sh
cabal repl
```

Then, within GHCi prompt, load the evaluation demo and activate the
"TemplateHaskell" language feature.

```sh
> :load Demos.Evaluator
> :seti -XTemplateHaskell # You will need to rerun this every time you restart GHCi
```

In order to run any of the predefined demos, call `run` on the given demo, e.g.

```sh
> run testFilter
# ... or ...
> run testCase
```

In order to `run` a custom expression, we will need to "lift" it using Template
Haskell, which for our purposes means surrounding the expression like this:
`$(lift =<< [| <your expression here> |])`.

For example, in order to run the example given in the introduction:

```hs
> run $(lift =<< [| let y = 3 + 5; x = 2 in x * y |])
```

### Troubleshooting / Errors

If cabal replies with issues about dependencies, please make sure you are using
GHC version 8.10.5. If you are and it still does not work, feel free to leave
an issue on this Github page.

If GHCi says `parse error on input ‘$’`, make sure you have run `:seti
-XTemplateHaskell`. You will need to run this each time you restart GHCi.

The stepper-interpreter is by no means complete - there are many language
features it would still struggle with, including list comprehensions,
do-notation, and typeclass-generic code. If there is any language feature you
feel is really missing, please raise an issue! It's fun to find out about
somebody using my software.
