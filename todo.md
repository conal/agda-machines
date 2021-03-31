## To do

*   Add category classes to remove the need for many module prefixes and to share definitions of derived categorical operations.
    At some point, try using [agda-categories](https://github.com/agda/agda-categories) instead.
*   Recreate compiling-to-categories so we can write and read lambda notation instead of combinators!
    See how far we can get with Agda's reflection mechanism.
*   Add causality to `VecFun`.

*   Maybe parametrize machines by the stream functions they implement.
*   Consider making machines universe-level-polymorphic (easy).

## Did

*   Replace bit vectors with `TyF`.
    Non-injectivity of addition really hurts type inference, leading to a lot of tedious explicitly given implicit arguments.
    Big overhaul, but worth doing.
    *   Use `TyIx` in `Ty` for routing.
    *   The `Dot` module now uses vectors of output port names, manipulating them with routings.
        Instead, use `TyF` in `Ty`.
*   Examples.
*   Module with list function semantics.
*   State & prove properties, including how `run` relates machine combinators to stream function combinators.
