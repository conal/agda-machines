This Agda project plays with composable Mealy machines with compositional/functorial semantics to generate computational hardware.

*   "`make compile`" to compile the test program, though faster from within the IDE (`∁-c C­x C-C`).
*   "`make figures`" to generate circuit diagrams in the `figures` subdirectory.

A quick summary of the important modules:

*   `VecFun`: The main semantic model: `∀ {n} → Vec A n → Vec B n`. Intended to be causal, i.e., something like `∀ m → f ∘ take m ≡ take m ∘ f`. TODO: add this law to the representation.
*   `Mealy`: Semantic Mealy machines with a homomorphic mapping into `VecFun`.
*   
