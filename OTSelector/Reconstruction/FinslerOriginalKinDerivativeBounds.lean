import OTSelector.Reconstruction.FinslerOriginalKinLipschitzDerived

/-!
# Coefficient-lane derivative data for kin and g

This module packages the coefficient-lane differentiability data that
`FinslerOriginalKinLipschitzDerived` consumes into a single named interface and
composes it with the mean value Lipschitz step.

The coefficient lane supplies, on the compact convex chart image `K` of the retained
roots, the differentiability of the kinetic mark function `kin` and of the probe `g`
with Frechet derivatives `kin'`, `g'` (the derivatives of the frozen coefficient
quadratic form / population seed pair deficit in the label coordinates), together
with a bounded derivative norm on `K`.  The predicate
`HasBoundedFDerivOn E K f C` is exactly that interface: a derivative family `f'`
with `HasFDerivWithinAt f (f' x) K x` for every `x ∈ K` and `‖f' x‖₊ ≤ C` there.

From the interface the module derives the `LipschitzOnWith` bounds and the
`HasMarkLipschitzConstantsOn` interface of the mark modulus lane, so that the lane
only needs the two named analytic inputs and compact-sup bookkeeping.

Exact remaining sub-gap: producing `HasBoundedFDerivOn E K kin Ck` and
`HasBoundedFDerivOn E K g Cg` from the coefficient smoothness lemmas themselves
(C1 regularity of the frozen coefficient matrix / quadratic form in the label
coordinates, `FinslerCoefficientPressureFreezing`, `FinslerTileBlockFrozenComparison`)
together with the compactness sup: continuity of the derivative family on the
compact `K` yields a uniform constant.
-/

noncomputable section
namespace OTSelector.Reconstruction

open scoped NNReal ENNReal

/-- The coefficient-lane derivative interface: `f` is differentiable on `K` with a
derivative family whose operator norm is bounded by `C` on `K`. -/
def HasBoundedFDerivOn (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) (f : E → ℝ) (C : ℝ≥0) : Prop :=
  ∃ f' : E → E →L[ℝ] ℝ, (∀ x ∈ K, HasFDerivWithinAt f (f' x) K x) ∧
    (∀ x ∈ K, ‖f' x‖₊ ≤ C)

/-- The derivative interface yields the Lipschitz bound on the convex root family. -/
theorem lipschitzOnWith_of_hasBoundedFDerivOn {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hK : Convex ℝ K) {f : E → ℝ} {C : ℝ≥0}
    (h : HasBoundedFDerivOn E K f C) : LipschitzOnWith C f K := by
  obtain ⟨f', hdiff, hbound⟩ := h
  exact lipschitzOnWith_of_bounded_fderiv hK hdiff hbound

/-- **Composition to the mark modulus interface.**  The two coefficient-lane
derivative inputs (for `kin` and for `g`) give the mark-Lipschitz constants of the
retained root family. -/
theorem hasMarkLipschitzConstantsOn_of_hasBoundedFDerivOn {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : Convex ℝ K)
    {kin g : E → ℝ} {Ck Cg : ℝ≥0}
    (hkin : HasBoundedFDerivOn E K kin Ck)
    (hg : HasBoundedFDerivOn E K g Cg) :
    HasMarkLipschitzConstantsOn E K kin g := by
  obtain ⟨kin', hkin_diff, hkin_bound⟩ := hkin
  obtain ⟨g', hg_diff, hg_bound⟩ := hg
  exact hasMarkLipschitzConstantsOn_of_bounded_fderiv hK hkin_diff hkin_bound
    hg_diff hg_bound

end OTSelector.Reconstruction
