# jensfest-agda

> Agda code corresponding to a semantics of inheritance

This repository contains the Agda source code for a paper ([Mosses 2024])
accepted for presentation at [JensFest] in October 2024.
The Agda types and function definitions correspond closely to those given in
([Cook 1989]; [Cook and Palsberg 1989]; [Cook and Palsberg 1994]).

Agda verifies that the definitions given here are well-typed,
and checks that proofs of the stated results are valid.
The code imports various modules from the [standard Agda library version 2.1],
and type-checks with Agda version 2.6.4.3.

In denotational semantics, types are generally taken to be Scott domains,
so that they can be defined recursively (up to isomorphism).
Similarly, functions between domains are required to be Scott-continuous,
so that endofunctions on domains have least fixed points.
Lambda-abstraction and function application preserve continuity,
so functions defined by lambda-expressions are automatically continuous.

To specify denotational semantics properly in Agda,
the type-theoretic structure of Scott domains has to be made explicit,
and all functions have to be accompanied by proofs of their continuity.
The [DomainTheory] modules from the [TypeTopology] library define 
Scott domains as types of dcpos (directed-complete posets),
and define types of functions that respect that structure.

However, it would be notationally quite burdensome to use those modules:
every lambda-abstraction has to be proved continuous,
and every function application has to discard the proof of its continuity.
Such pedantic details significantly undermine simplicity and conciseness
when defining functions in Agda using lambda-notation.

The compromise adopted here is to leave the structure of domains *implicit*,
and *assume* the existence of isomorphisms between domains and
their definitions.
Functions defined by lambda-expressions are simply assumed to be continuous,
as are all abstracted functions.
The impossibility of discharging these assumptions does not interfere with
type-checking and proof validation in Agda.

[Mosses 2024]: TBA
[JensFest]: https://2024.splashcon.org/home/jensfest-2024
[Cook 1989]: https://cs.brown.edu/research/pubs/theses/phd/1989/cook.pdf "PhD thesis"
[Cook and Palsberg 1989]: https://doi.org/10.1145/74877.74922 "OOPSLA '89"
[Cook and Palsberg 1994]: https://doi.org/10.1006/INCO.1994.1090 "Inf. Comput."
[standard Agda library version 2.0]: https://agda.github.io/agda-stdlib/v2.0/
[DomainTheory]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/DomainTheory.index.html
[TypeTopology]: https://www.cs.bham.ac.uk/~mhe/TypeTopology/