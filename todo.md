## To do

*   Replace bit vectors with `Ty`.
    Non-injectivity of addition leads to a lot of tedious explicitly given implicit arguments.
    Big overhaul, but well worth the effort.
    Use `BitIdx` in `Ty` for routing.

*   Add category classes to remove the need for many module prefixes and to share definitions of derived categorical operations.
    At some point, try using agda-categories.
*   Recreate compiling-to-categories so we can write and read lambda notation instead of combinators.

*   Maybe parametrize machines by the stream functions they implement.
*   Consider making machines universe-level-polymorphic (easy).

## Did

*   Examples.
*   Module with list function semantics.
*   State & prove properties, including how `run` relates machine combinators to stream function combinators.
