This Agda project plays with composable Mealy machines with compositional/functorial semantics to generate computational hardware.

Circuit graph rendering requires [GraphViz](https://graphviz.org/).

https://github.com/agda/agda/issues/3619

Makefile targets:

*   `compile`: compiles the `Test` module, though doing so faster from within the Emacs mode (`∁-c C­x C-C`).
*   `tests`: generates circuit diagrams in the `Figures` subdirectory (dot files and their PDF renderings).


If you get an error message "`Could not find module ‘Numeric.IEEE’`", then there is one Haskell package you need to have installed:
```
cabal v1-install ieee754
```

A quick summary of the important modules:

*   `Category`: Simple type classes for flavors of categories.
    The main programming interface for most types in the implementation.
*   `VecFun`: The main semantic model: `∀ {n} → Vec A n → Vec B n`.
    Intended to be causal, i.e., something like `∀ m → f ∘ take m ≡ take m ∘ f`.
*   `Mealy`: Semantic Mealy machines with a homomorphic mapping into `VecFun`.
*   `Ty`: inductive encoding of the supported types.
    Currently just `⊤`, `Bool`, and (inductively) products, but can be extended.
    Used to index most of the implementation.
    Also a type `TyIx` of indices into type structure, and a representable functor `TyF` indexed by `TyIx`.
*   `Symbolic.Extrinsic`: "symbolic" representations of computations, with homomorphic/functorial semantic functions.
    See also `Symbolic.Intrinsic`, a variation indexed by denotation (currently unused).
*   `Symbolic.StackProg`: a linearized representation of functional computations designed to explain the essence of stack machines and  compiling to them in [*Calculating compilers categorically*](http://conal.net/papers/calculating-compilers-categorically/).
    I think it elegantly captures the essence of not only stack-based computation, but of hardware netlists and [SSA](https://en.wikipedia.org/wiki/Static_single_assignment_form) as well.
*   `Dot`: generation of [GraphViz *dot* format](https://en.wikipedia.org/wiki/DOT_%28graph_description_language%29) from the stack program category.
*   `Test`: examples with dot file generation.
    Compile this module and run the executable to generate dot files and render them into PDFs.
    The Makefile relies on having [GraphViz](https://graphviz.org/) installed for the `dot` executable.
    See above for `make` incantations.

There are many semantic functions (`⟦_⟧`) mapping between categories.
Every one of them should be functorial, which is to say that the representation faithfully implements its meaning.
