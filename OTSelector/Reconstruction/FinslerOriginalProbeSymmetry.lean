import OTSelector.Reconstruction.FinslerOriginalMaskedExchangeability

/-!
# Probe pair-functionality: the masked-matrix bridging lemma

This module closes the step *masked frozen matrix is a pair functional* modulo the
structural hypotheses on the mask and on the underlying entry, and hence provides the
**exchangeability fallback** for the plan-free lane.

**Proved (masked pair-functionality composition).**  If, for a fixed outcome, the mask
is pair functional,

  `(i,j) ∈ Q ↔ G (X i, Y j)`

and the underlying matrix entry is pair functional,

  `d i j = Φ (X i, Y j),`

then the *masked* entry is pair functional with the composed kernel
`Ψ p = if G p then Φ p else 0`:

  `maskedFrozenCost Q d i j = Ψ (X i, Y j).`

This is the deterministic bridging lemma between the geometry of the mask and the
exchangeability of the masked entries.

**Proved (exchangeability fallback).**  Consequently, in the probability setting of the
repo iid pair law, a matrix whose entries are masked copies of a pair-functional matrix
satisfies `MaskedEntryExchangeability`: all masked-entry integrals are equal.  This
removes the *mask* from the list of obstructions: the only structural hypothesis left
is pair-functionality of the entry, i.e. of the matrix probe `hprobe f t n s c`
(whose `(i,j)` entry must depend on the pair `(X i, Y j)` only, as a model probe
evaluated at the two marks does).

No `sorry`, `admit` or added axiom occurs.
-/

open Set Function Matrix Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

/-- **Masked pair-functionality composition.**  A masked matrix whose mask condition
and entries are both pair functionals is itself pair functional, with kernel
`if G then Φ else 0`. -/
theorem maskedFrozenCost_pairFunctional {M M' : Type*} {n : ℕ}
    (X : Fin (n + 1) → M) (Y : Fin (n + 1) → M')
    (Q : Set (Fin (n + 1) × Fin (n + 1))) (d : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : M × M' → Prop) [DecidablePred G] (Φ : M × M' → ℝ)
    (hQ : ∀ i j, (i, j) ∈ Q ↔ G (X i, Y j))
    (hd : ∀ i j, d i j = Φ (X i, Y j)) (i j : Fin (n + 1)) :
    maskedFrozenCost Q d i j = (fun p : M × M' ↦ if G p then Φ p else 0) (X i, Y j) := by
  have hunfold : maskedFrozenCost Q d i j =
      (Q.indicator (fun p : Fin (n + 1) × Fin (n + 1) ↦ d p.1 p.2)) (i, j) := rfl
  rw [hunfold]
  by_cases h : (i, j) ∈ Q
  · rw [Set.indicator_of_mem h, hd i j]
    have hG : G (X i, Y j) := (hQ i j).mp h
    simp only [hG, ite_true]
  · rw [Set.indicator_of_notMem h]
    have hG : ¬ G (X i, Y j) := fun hg ↦ h ((hQ i j).mpr hg)
    simp only [hG, ite_false]

/-- **Exchangeability fallback.**  If the mask condition and the entries are pair
functionals and the sample families satisfy the repo iid pair-law hypotheses, then the
masked matrix satisfies masked-entry exchangeability: all masked-entry integrals
coincide.  The mask is thus eliminated as an obstruction; only pair-functionality of
the entry (the matrix probe) remains. -/
theorem maskedEntryExchangeability_of_mask_pairFunctional
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
    {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} (X : Fin (n + 1) → Ω → M) (Y : Fin (n + 1) → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (Q : Ω → Set (Fin (n + 1) × Fin (n + 1)))
    (d : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (G : M × M' → Prop) [DecidablePred G] (Φ : M × M' → ℝ)
    (hΦ : Measurable (fun p : M × M' ↦ if G p then Φ p else 0))
    {B : ℝ} (hB : ∀ p, |(fun p : M × M' ↦ if G p then Φ p else 0) p| ≤ B)
    (hQ : ∀ s (i j : Fin (n + 1)), (i, j) ∈ Q s ↔ G (X i s, Y j s))
    (hd : ∀ s (i j : Fin (n + 1)), d s i j = Φ (X i s, Y j s)) :
    MaskedEntryExchangeability P (fun s ↦ maskedFrozenCost (Q s) (d s)) := by
  have hE : ∀ s (i j : Fin (n + 1)),
      maskedFrozenCost (Q s) (d s) i j =
        (fun p : M × M' ↦ if G p then Φ p else 0) (X i s, Y j s) :=
    fun s i j ↦ maskedFrozenCost_pairFunctional (fun i ↦ X i s) (fun j ↦ Y j s)
      (Q s) (d s) G Φ (hQ s) (hd s) i j
  exact maskedEntryExchangeability_of_pairFunctional X Y hX hY hXlaw hYlaw hpair
    (fun s ↦ maskedFrozenCost (Q s) (d s))
    (fun p : M × M' ↦ if G p then Φ p else 0) hΦ hB hE

end OTSelector.Reconstruction
