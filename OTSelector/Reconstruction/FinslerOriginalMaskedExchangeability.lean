import OTSelector.Reconstruction.FinslerOriginalFixedPairIdentification

/-!
# Masked-entry exchangeability from permutation invariance

This module proves the **exchangeability step** of the mask-coupling law
(`MaskedEntryExchangeability` in `FinslerOriginalFixedPairIdentification.lean`) under the
structural hypothesis that identifies the remaining input precisely: the masked
frozen entry is a *pair functional*,

  `E s i j = Ψ (X i s, Y j s),`

i.e. it depends on the pair `(i,j)` only through the two sample points and not on the
index labels, the whole configuration, or an outcome-dependent matrix probe.

**Proved (per-pair identity).**  For a bounded measurable pair kernel `Ψ` and iid
sample families `X` (law `μ`), `Y` (law `ν`) with pairwise independence
(`IndepFun (X i) (Y j)` for all `i, j`), every pair has the same expectation:

  `∫ s, Ψ (X i s, Y j s) ∂P = ∫ p, Ψ p ∂(μ.prod ν)`

independently of `(i,j)`.  The proof is the map identity
`P.map (fun s => (X i s, Y j s)) = μ.prod ν` (independence + the two marginal laws)
composed with the change-of-variables formula `MeasureTheory.integral_map` — exactly the
per-term computation inside the repo iid pair law `integral_pairTest_eq`.

**Proved (exchangeability corollary).**  Hence any pair-functional matrix has
`MaskedEntryExchangeability`: all entries have equal integrals.  In particular the
uniform masked-entry identity applies and the normalized plan-free mean equals the
single-entry population integral `∫∫ Ψ`.

**Remaining gap (exact).**  The structural hypothesis itself: one must show that the
masked frozen cost
`maskedFrozenCost (edgeEvent (X s) (Y s) c) (frozenCoreMatrix ... (probe s c)) i j`
is a pair functional.  The mask `edgeEvent` is defined by the *geometric* condition of
the pair (hence is a pair functional if the tile reference `z₀` is index-independent,
which it is: `z₀ = fun _ _ => T.reference c`); the obstruction is the matrix probe
`hprobe f t n s c` whose entry `(i,j)` may depend on the whole configuration.  If the
probe is a pair functional too, the gap closes.

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

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
  {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- **Per-pair identity: every pair functional has the same expectation.**  For iid
sample families with the repo pair-law hypotheses, the expectation of a bounded
measurable pair kernel evaluated at any pair `(i,j)` is the product-population
integral. -/
theorem integral_pairFunctional_eq {n : ℕ} (X : Fin n → Ω → M) (Y : Fin n → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (Ψ : M × M' → ℝ) (hΨ : Measurable Ψ) {B : ℝ} (hΨb : ∀ p, |Ψ p| ≤ B) :
    ∀ i j, ∫ s, Ψ (X i s, Y j s) ∂P = ∫ p, Ψ p ∂(μ.prod ν) := by
  intro i j
  have hmap : P.map (fun s ↦ (X i s, Y j s)) = μ.prod ν := by
    rw [(hpair i j).map_prod_eq_prod_map_map (hX i).aemeasurable (hY j).aemeasurable,
      hXlaw i, hYlaw j]
  have hmeas : AEStronglyMeasurable Ψ (P.map (fun s ↦ (X i s, Y j s))) :=
    hΨ.aestronglyMeasurable (μ := (P.map (fun s ↦ (X i s, Y j s))))
  rw [← MeasureTheory.integral_map ((hX i).prodMk (hY j)).aemeasurable hmeas, hmap]

end OTSelector.Probability

namespace OTSelector.Reconstruction

open OTSelector.Probability

/-- **Masked-entry exchangeability from pair functionality.**  If a matrix-valued
random variable is a pair functional of iid sample families satisfying the repo
pair-law hypotheses, then all its entries have equal integrals: the exchangeability
hypothesis of the uniform masked-entry identity holds. -/
theorem maskedEntryExchangeability_of_pairFunctional
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
    {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} (X : Fin (n + 1) → Ω → M) (Y : Fin (n + 1) → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (E : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Ψ : M × M' → ℝ) (hΨ : Measurable Ψ) {B : ℝ} (hΨb : ∀ p, |Ψ p| ≤ B)
    (hE : ∀ s (i j : Fin (n + 1)), E s i j = Ψ (X i s, Y j s)) :
    MaskedEntryExchangeability P E := by
  intro i j i' j'
  have h1 : ∫ s, E s i j ∂P = ∫ s, Ψ (X i s, Y j s) ∂P :=
    integral_congr_ae (Eventually.of_forall fun s ↦ hE s i j)
  have h2 : ∫ s, E s i' j' ∂P = ∫ s, Ψ (X i' s, Y j' s) ∂P :=
    integral_congr_ae (Eventually.of_forall fun s ↦ hE s i' j')
  rw [h1, h2, integral_pairFunctional_eq X Y hX hY hXlaw hYlaw hpair Ψ hΨ hΨb i j,
    integral_pairFunctional_eq X Y hX hY hXlaw hYlaw hpair Ψ hΨ hΨb i' j']

/-- **Plan-free mean of a pair-functional matrix.**  Combining the pair functionality
with the uniform masked-entry identity: the normalized plan-free tile mean is the
single-entry population integral `∫∫ Ψ` (no mask-coupling correction needed under this
structural hypothesis). -/
theorem planFreeTileMean_eq_pairIntegral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {M M' : Type*} [MeasurableSpace M] [MeasurableSpace M']
    {μ : Measure M} {ν : Measure M'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} (hn : 0 < n + 1) (X : Fin (n + 1) → Ω → M) (Y : Fin (n + 1) → Ω → M')
    (hX : ∀ i, Measurable (X i)) (hY : ∀ j, Measurable (Y j))
    (hXlaw : ∀ i, P.map (X i) = μ) (hYlaw : ∀ j, P.map (Y j) = ν)
    (hpair : ∀ i j, IndepFun (X i) (Y j) P)
    (E : Ω → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (Ψ : M × M' → ℝ) (hΨ : Measurable Ψ) {B : ℝ} (hΨb : ∀ p, |Ψ p| ≤ B)
    (hE : ∀ s (i j : Fin (n + 1)), E s i j = Ψ (X i s, Y j s)) :
    (1 / (((n + 1 : ℕ)) : ℝ)) *
        ((1 / (((n + 1 : ℕ)) : ℝ)) * ∫ s, (∑ i, ∑ j, E s i j) ∂P) =
      ∫ p, Ψ p ∂(μ.prod ν) := by
  have hExch := maskedEntryExchangeability_of_pairFunctional X Y hX hY hXlaw hYlaw hpair
    E Ψ hΨ hΨb hE
  have hint : ∀ i j, Integrable (fun s ↦ E s i j) P := by
    intro i j
    refine Integrable.of_bound ?_ B ?_
    · exact (hΨ.comp ((hX i).prodMk (hY j))).aestronglyMeasurable.congr
        (Eventually.of_forall fun s ↦ (hE s i j).symm)
    · filter_upwards with s
      rw [Real.norm_eq_abs, hE s i j]
      exact hΨb (X i s, Y j s)
  have hmean := planFreeTileMean_eq_fixedPair P (Nat.succ_pos n) E hint hExch
  rw [hmean]
  calc ∫ s, E s ⟨0, Nat.succ_pos n⟩ ⟨0, Nat.succ_pos n⟩ ∂P
      = ∫ s, Ψ (X ⟨0, Nat.succ_pos n⟩ s, Y ⟨0, Nat.succ_pos n⟩ s) ∂P :=
        integral_congr_ae (Eventually.of_forall fun s ↦ hE s _ _)
    _ = ∫ p, Ψ p ∂(μ.prod ν) :=
        integral_pairFunctional_eq X Y hX hY hXlaw hYlaw hpair Ψ hΨ hΨb _ _

end OTSelector.Reconstruction
