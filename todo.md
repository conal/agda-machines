## To do

*   More examples of various difficulties.
    Some ideas:
    *   [Ready/valid handshake](https://stackoverflow.com/questions/53583946/valid-ready-handshake-in-verilog).
    *   Carry look-ahead counter (log depth instead of linear).
        Extract the essential, general technique for reuse.
    *   Prove correctness of the binary up counter, i.e., that the meaning of the bits patterns generated indeed count the number of true inputs so far.
        Start with a vector function version and its proof, and then transfer the proofs to lower level representations via denotational homomorphisms.
*   Look for sequential (rather than combinational) decompositions of current examples.
*   Can Dot produce more spatially symmetrical layouts?
    The `rankdir` choices seem to be horizontal and vertical, while I sometimes want roughly equal edge lengths.
    There may be some helpful examples in the [GraphViz gallery](https://graphviz.org/gallery/).
    Maybe the answer is to use a renderer other than `dot`, e.g., `neato`, `circo`, `fdp`, or `twopi`.
    Oh. The port positions are biased for left-to-right.
    Perhaps there are other ways to identify ports.
*   Organize example suite so that every example is presented in several forms, all connected by denotational homomorphisms to guarantee semantic equivalence:
    *   As vector functions, defined conveniently in the usual pointful lambda notation.
    *   Redefined equivalently (still as vector functions) but using only (point-free) categorical vocabulary.
    *   Generalized to other categories (but in the same vocabulary)
    *   Re-specialized to hardware.
*   Blog posts of pretty examples.
*   Add lots of algebraic optimizations that get applied during circuit construction, such as multiplication by zero or one and addition with zero, and similar identities for `∧`, `∨`, and `xor`.
    Also, constant folding in general and common subexpression elimination.
    These optimizations were *very* effective in my Haskell-to-Hardware project and were mostly applied in the graph-construction category.
    The `Stack` category is the closest counterpart in this project.
    Implementation idea: for each primitive added, check whether there's already the same primitive fed by the "same" inputs in a suitable sense.
    If so, reuse that primitive instance with suitable routing added; otherwise add as done currently.
*   Level-generalize the instances of `products` and `boolean` for functions in `Category`.
    This one is trickier than I expected, as there are so many uses of that category.
*   Add laws to the category classes.
*   Recreate compiling-to-categories so we can write and read lambda notation instead of combinators!
    See how far we can get with Agda's reflection mechanism.
*   Add causality definition and proofs to `VecFun`.

*   At some point, try using [agda-categories](https://github.com/agda/agda-categories) instead our own.
*   Maybe parametrize machines by the stream functions they implement.
*   Consider making machines universe-level-polymorphic (easy).

## Did

*   Parametrize some constructions to be parametric over an underlying category:
    *   `Symbolic.StackProg`, now `Stack`
    *   `Mealy`
    *   `Symbolic.Extrinsic`, now `Symbolic`
*   LFSR (linear feedback shift register) example.
    Change to size `suc n`, eliminating the `false` for `zero`.
*   Omit components if inputs and outputs are both empty (hence disconnected).
    Or maybe just for `input` and `output` at first, to see if any other disconnected components appear.
*   Update `VecFun` with a record wrapper and use of category vocabulary.
*   Get `VecFun` and `Mealy` back in the game.
*   Replace most uses of `_∘′_` with `_∘_` (now that `Function` is a category).
*   Remove `Boolᵗ` now that `Bool` has many meanings.
*   Rename `Ty` constructors to start with backquote.
    Revisit all `Category` imports to remove `hiding` of the old `Ty` names.
*   Treat `Bool` like `⊤` and `_×_`, hoisting out of `Boolean` into a class of objects rather than of morphisms.
    Rename the morphism class from "`Boolean`" to "`Logic`".
    Revisit `TyUtils`, replacing ``Bool` by `Bool`.
*   Rename `Constants` class to "`Constant`".
*   Gather all of the instances in `Category` under one `instance` heading.
    Then submerge in a local module, and replace the names by generic names (as used elsewhere).
*   Do I need to name instances at all? Yes.
*   Remove `false` and `true` from `Boolean` in favor of `const`.
    Then fix all module-qualified uses of `false` and `true`.
*   Add type classes for primitives and for constants, with many instances.
    Obviates explicit use of embedding functions like `prim` and `comb`.
    Define the semantics of symbolic instances as the instances of the semantic instances.
*   Add category classes to remove the need for many module prefixes and to share definitions of derived categorical operations.
    Then drop `Misc` in favor of `Category`.
*   Replace bit vectors with `TyF`.
    Non-injectivity of addition really hurts type inference, leading to a lot of tedious explicitly given implicit arguments.
    Big overhaul, but worth doing.
    *   Use `TyIx` in `Ty` for routing.
    *   The `Dot` module now uses vectors of output port names, manipulating them with routings.
        Instead, use `TyF` in `Ty`.
*   Examples.
*   Module with list function semantics.
*   State & prove properties, including how `run` relates machine combinators to stream function combinators.
