import Mathlib.MeasureTheory.Measure.Real

/-!
# Triangular Array

Conditions: A sequence of probability spaces, real observables and scales; O_p is defined by eventual tail control. The sufficient helper supplies a uniform inverse-tail bound with its stated constants.

Objects: An eventual Big-O-in-probability proposition and a sufficient bound valid for changing sample spaces.

Proof detail: For each ε choose a large positive tail constant so K/C≤ε; the uniform estimate implies the eventual quantifier in the definition.

Relation to primary sources: A changing-space tightness formulation, directly derived from an inverse-tail estimate. The definition itself does not assume positive scales or uniform control over every n.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 3.2.2, Theorem 3.2.13, p. 122; Theorem 3.2.14, p. 123. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=130
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
-/
/-!
# Tight stochastic scales on varying sample spaces

The finite-`n` estimates used in the feedback construction live on a different product space for
each `n`.  This module gives the triangular-array meaning of `Xₙ = Oₚ(aₙ)` directly in terms of
uniform tail probabilities; it does not force all rows onto one artificial sample space.
-/

open Filter MeasureTheory
open scoped Topology

namespace OTSelector.Probability

/-- `Xₙ = Oₚ(aₙ)` for a triangular array whose row `n` may have its own sample space and law. -/
def IsBigOInProbability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (X : ∀ n, Ω n → ℝ) (scale : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ᶠ n in atTop, (P n).real {ω | C * scale n < |X n ω|} ≤ ε

/-- A uniform `K / d` tail at threshold `d aₙ` implies `Oₚ(aₙ)`, even when the sample space
depends on `n`. -/
theorem isBigOInProbability_of_uniform_inv_tail
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → ℝ) (scale : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (htail : ∀ d : ℝ, 0 < d → ∀ n,
      (P n).real {ω | d * scale n ≤ |X n ω|} ≤ K / d) :
    IsBigOInProbability P X scale := by
  intro ε hε
  let C := (K + 1) / ε
  have hC : 0 < C := div_pos (by linarith) hε
  refine ⟨C, hC, Filter.Eventually.of_forall fun n ↦ ?_⟩
  have hsubset : {ω | C * scale n < |X n ω|} ⊆
      {ω | C * scale n ≤ |X n ω|} := by
    intro ω hω
    change C * scale n < |X n ω| at hω
    change C * scale n ≤ |X n ω|
    exact hω.le
  have hratio : K / C < ε := by
    rw [div_lt_iff₀ hC]
    change K < ε * ((K + 1) / ε)
    calc
      K < K + 1 := lt_add_one K
      _ = ε * ((K + 1) / ε) := by field_simp
  exact (measureReal_mono hsubset).trans ((htail C hC n).trans hratio.le)

end OTSelector.Probability
