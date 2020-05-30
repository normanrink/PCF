### Development in Idris of standard meta-theory for a simply-typed lambda calculus with recursion


The main goal of this development are implementations of lambda calculus interpreters that are certified correct with respect to independently specified evaluation semantics.

The interpreters are implemented as functions that evaluate lambda calculus terms.
Since [Idris](https://www.idris-lang.org/) is a dependently-typed language, the interpreter functions can be given expressive type signatures that amount to certificates of correctness.
In bringing up these interpreters together with their certificates, the standard substitution lemma and progress theorem are established as total functions in Idris.
From this the certified interpreters follow easily.

Additional meta-theory is established, namely determinism for small-step and big-step evaluation relations and the equivalence of small-step and big-step semantics.
Moreover, co-inductive small-step and big-step semantics for PCF are also defined and their relationship between each other and also with the corresponding inductive semantics is studied, following parts of [1].

#### Lambda calculi 

The main object of study is a simply-typed lambda calculus with natural numbers and general recursion.
This calculus is commonly known as Plotkin’s PCF.
The developments that are worked out for PCF are repeated for a simply-typed lambda calculus with only primitive recursion, known as Gödel’s T, for the untyped lambda calculus, and for PCF with co-inductively defined semantics.


#### Project structure

```
typed/src         --- Idris sources for the certified PCF interpreters and meta-theory.
total/src         --- Idris sources for the analogous developments for Gödel’s T.
untyped/src       --- Idris sources for the untyped lambda calculus.
conventional/src  --- Idris sources for a development of PCF analogous to the one in 'typed/src' except
                      with a more conventional treatment of de Bruijn indices. Here, "conventional"
                      means that contexts are lists of (object-language) types and that a de Bruijn index
                      constitutes proof that an entry in the context has a certain type. (The treatment
                      in 'typed/src' defines contexts as fixed length vectors of types; and a de Bruijn
                      index is indeed just an index into this vector, albeit with an equality proof for
                      the type at the given index in the context.)
codata/src        --- Idris sources for the development of PCF with both inductive *and* co-inductive
                      semantics. (Non-)Equivalences between the different semantics are studied by
                      considering diverging PCF terms.
totality/src      --- Development of the standard proof of totality for Gödel's T. The standard argument
                      relies on a (unary) logical relation. Unlike the devlopments in other source folders,
                      the development in 'totality/src' is based on untyped lambda calculus terms and
                      introduces the typing judgment as a separate (Idris) data type.
test              --- Tests that execute simple functions on natural numbers.
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

Note that type checking and compiling of Idris source files has been tested with [Idris version 1.3.0](https://github.com/idris-lang/Idris-dev).
(Meanwhile, [Idris 2](https://github.com/idris-lang/Idris2) is also available.)


#### Notes on totality

Both the untyped lambda calculus and PCF are not total, i.e. these calculi allow definitions of functions with general recursion that need not terminate.
Gödel’s T, however, is total, i.e. only total functions can be defined in this calculus.
This is proven in the present project by relying on meta-theoretic properties of Idris:
an environment-based interpreter is implemented for Gödel’s T;
this interprets terms in the calculus as values in Idris;
and the Idris totality checker verifies that this interpreter is indeed a total function.
An alternative proof of totality for Gödel's T is developed in the subfolder `totality`.
This is the standard proof based on a (unary) logical relation, cf. Chapter 12 of [2].


#### References

[1] Xavier Leroy and Hervé Grall. 2009. [Coinductive big-step operational semantics](https://doi.org/10.1016/j.ic.2007.12.004). Inf. Comput. 207, 2 (February 2009), 284–304.

[2] Benjamin C. Pierce. 2002. [Types and Programming Languages](https://www.cis.upenn.edu/~bcpierce/tapl/). Cambridge, MA, USA: The MIT Press.
