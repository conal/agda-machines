*This project has been archived and is being superceded by [agda-hardware](https://github.com/conal/agda-hardware).*

## Introduction

This Agda project aims to synthesize machine-verified, parallel hardware designs from high-level denotational specifications.
The common algebraic abstraction is categories, as described in the talks [*From Haskell to Hardware via CCCs*](https://github.com/conal/talk-2015-haskell-to-hardware/blob/post-tabula/README.md) and [*Teaching new tricks to old programs*](https://github.com/conal/2017-talk-teaching-new-tricks-to-old-programs#readme), as well as the paper [*Compiling to categories*](http://conal.net/papers/compiling-to-categories/).

## Dependencies

*   [Agda compiler](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installing-the-agda-and-the-agda-mode-programs)
*   Haskell [ieee754 package](https://github.com/agda/agda/issues/3619) (as described under Troubleshooting below)
*   [GraphViz](https://graphviz.org/) for circuit graph rendering

## Building

Makefile targets:

*   `compile`: compiles the `Test` module, but you can compile faster from within the Emacs mode (`∁-c C­x C-c`).
*   `tests`: generates circuit diagrams in the `Figures` subdirectory (dot files and their PDF renderings).
*   `listings`: renders source code to deeply hyper-linked HTML.
    Start perusing at `html/Everything.html`.

## Summary of important modules

***This section is out of date.***

A quick summary of the important modules:

*   `Category`: Simple type classes for flavors of categories.
    The main programming interface for most types in the implementation.
*   `VecFun`: The main semantic model: `∀ {n} → Vec A n → Vec B n`.
    Intended to be causal, i.e., `∀ m → f ∘ take m ≡ take m ∘ f`.
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

## Troubleshooting

You might see an error message like this:

```
Calling: ghc -O -o /Users/sseefried/code/agda-machines/Test -Werror -i/Users/sseefried/code/agda-machines -main-is MAlonzo.Code.Test /Users/sseefried/code/agda-machines/MAlonzo/Code/Test.hs --make -fwarn-incomplete-patterns -fno-warn-overlapping-patterns
[  1 of 153] Compiling MAlonzo.RTE      ( MAlonzo/RTE.hs, MAlonzo/RTE.o )
Compilation error:

MAlonzo/RTE.hs:9:1: error:
    Could not find module ‘Numeric.IEEE’
    Use -v (or `:set -v` in ghci) to see a list of the files searched for.
  |
9 | import Numeric.IEEE ( IEEE(identicalIEEE, nan) )
  | ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

You can fix this with:

```
cabal v2-install ieee754
```

You can find out how to more about this issue [here](https://github.com/agda/agda/issues/3619#issuecomment-665232148) and
[here](https://agda.readthedocs.io/en/latest/getting-started/installation.html#installing-the-agda-and-the-agda-mode-programs).
