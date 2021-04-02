## To do

*   Level-generalize the instances of `products` and `boolean` for functions in `Category`.
    This one is trickier than I expected, as there are so many uses of that category.
*   Update `VecFun` with a record wrapper and use of category vocabulary.
*   Get `VecFun` and `Mealy` back in the game.
*   Add laws to the category classes.
*   Recreate compiling-to-categories so we can write and read lambda notation instead of combinators!
    See how far we can get with Agda's reflection mechanism.
*   Add causality definition and proofs to `VecFun`.

*   At some point, try using [agda-categories](https://github.com/agda/agda-categories) instead our own.
*   Maybe parametrize machines by the stream functions they implement.
*   Consider making machines universe-level-polymorphic (easy).

## Did

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
