### Development in Idris of standard meta-theory for a simply-typed lambda calculus with recursion


The main goal of this development are implementations of lambda calculus interpreters that are certified correct with respect to independently specified evaluation semantics.

The interpreters are implemented as functions that evaluate lambda calculus terms.
Since Idris is a dependently-typed language, the interpreter functions can be given expressive type signatures that amount to certificates of correctness.
In bringing up these interpreters together with their certificates, the standard substitution lemma and progress theorem are established as total functions in Idris.
From this the certified interpreters follow easily.

Additional meta-theory is established, namely determinism for small-step and big-step evaluation relations and the equivalence of small-step and bis-step semantics.

#### Lambda calculi 

The main object of study is a simply-typed lambda calculus with natural numbers and general recursion.
This calculus is commonly known as Plotkin’s PCF.
The developments that are worked out for PCF are repeated for a simply-typed lambda calculus with only primitive recursion, known as Gödel’s T, and for the untyped lambda calculus.


#### Project structure

```
typed/src   --- Idris sources for the certified PCF interpreters and meta-theory.
total/src   --- Idris sources for the analogous developments for Gödel’s T.
untyped/src --- Idris sources for the untyped lambda calculus.
test        --- Tests that execute simple functions on natural numbers.
```
In each calculus the functions addition, multiplication, and factorial are implemented.
Several simple test programs, located in the `test` folder, execute these functions using the different interpreters that are available for each of the calculi.


#### Compiling and building

The main purpose of this project is the development of certified interpreters, with special emphasis on establishing the certificates and proving meta-theoretic results.
To this end, the Idris type checker (including its totality checker) acts as a proof checker.
The most important aspect in building this project is therefore that the sources for the lambda calculi and the interpreters pass the Idris type checker.
Of course this entails that the Idris compiler can turn the source code for the interpreters into executable binaries.

Several simple test programs are provided for testing that the interpreters behave as expected.
To build the test programs for all available interpreters in each of the calculi, run

  ```make all```

in the top-level folder.
This produces a new subfolder `bin` containing the executable binaries for the tests.


#### Notes on totality

Both the untyped lambda calculus and PCF are not total, i.e. these calculi allow definitions of functions with general recursion that need not terminate.
Gödel’s T, however, is total, i.e. only total functions can be defined in this calculus.
This is proven in the present project by relying on meta-theoretic properties of Idris:
an environment-based interpreter is implemented for Gödel’s T;
this interprets terms in the calculus as values in Idris;
and the Idris totality checker verifies that this interpreter is indeed a total function.


#### Bug reports & suggestion

Please report bugs and suggestions to norman.rink@tu-dresden.de.
