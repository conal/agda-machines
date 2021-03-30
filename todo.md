## To do

*   Replace bit vectors with `Ty`.
    Non-injectivity of addition really hurts type inference, leading to a lot of tedious explicitly given implicit arguments.
    Big overhaul, but worth doing.
    *   Use `TyIx` in `Ty` for routing.
    *   The `Dot` module now uses vectors of output port names, manipulating them with routings.
        Instead, use `TyF` in `Ty`.

*   Add category classes to remove the need for many module prefixes and to share definitions of derived categorical operations.
    At some point, try using agda-categories.
*   Recreate compiling-to-categories so we can write and read lambda notation instead of combinators.

*   Maybe parametrize machines by the stream functions they implement.
*   Consider making machines universe-level-polymorphic (easy).

## Did

*   Examples.
*   Module with list function semantics.
*   State & prove properties, including how `run` relates machine combinators to stream function combinators.
