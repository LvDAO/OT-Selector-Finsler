import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.Kernel.Disintegration.StandardBorel

/-!
# Kernels

Conditions: Finite measures and standard Borel targets with the exact measurable-space premises stated in Lean.

Objects: An alias for kernel conditional independence and the actual Measure.condKernel disintegration.

Proof detail: Define conditional independence using the conditional-expectation kernel and trimmed base measure; expose mathlib’s disintegrate identity without adding an axiom.

Relation to primary sources: The conditional-independence declaration is a project-facing definition. The disintegration theorem is a thin wrapper around mathlib’s standard Borel construction; the textbook finite-probability construction is extended by that library to finite measures including zero.

References:
* D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009), 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary. https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=25
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 4.1, conditional-expectation definition and Uniqueness argument, pp. 205–206; Section 4.1.3, Theorems 4.1.16–4.1.18, pp. 214–215. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213
* Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF), Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=56
-/
/-!
# Kernel, disintegration, and conditional-independence interfaces

These declarations are thin names around mathlib.  In particular, regular conditional laws are the
actual `Measure.condKernel`; no project-local choice principle or disintegration axiom is added.
-/

open MeasureTheory ProbabilityTheory

namespace OTSelector

/-- Project-facing name for a conditionally independent family given a sub-sigma-algebra. -/
abbrev ConditionallyIndependent {Ω ι : Type*} {β : ι → Type*}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω] [∀ i, MeasurableSpace (β i)]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    (X : ∀ i, Ω → β i) (P : @Measure Ω mΩ) [IsFiniteMeasure P] : Prop :=
  Kernel.iIndepFun X (condExpKernel (mΩ := mΩ) P m) (@Measure.trim Ω m mΩ P hm)

/-- Standard-Borel disintegration supplied by mathlib. -/
theorem condKernel_disintegrates {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [StandardBorelSpace β] [Nonempty β] (ρ : Measure (α × β))
    [IsFiniteMeasure ρ] :
    ρ.fst ⊗ₘ ρ.condKernel = ρ :=
  ρ.disintegrate ρ.condKernel

end OTSelector
