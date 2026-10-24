import OTSelector.Reconstruction.FinslerOriginalKinDerivativeBounds

/-!
# Coefficient smoothness instantiation

This module closes the compact-sup bookkeeping of the coefficient lane: on the
compact retained-root family `K`, continuity of the derivative family produces an
explicit uniform bound on its operator norm, hence the `HasBoundedFDerivOn`
interface of `FinslerOriginalKinDerivativeBounds` and the mark-Lipschitz constants.

For a continuous map into a normed space on a nonempty compact set there is a
uniform norm bound (`exists_norm_le_of_compact`); applied to the coefficient-lane
derivative families `kin'`, `g'` this gives `HasBoundedFDerivOn E K kin Ck` and
`HasBoundedFDerivOn E K g Cg`, and then `HasMarkLipschitzConstantsOn E K kin g`
unconditionally from differentiability and derivative continuity on `K`.

Remaining analytic input still stated explicitly: differentiability of `kin`, `g`
on the retained-root family with the coefficient-lane derivative formulas
(the C1 coefficient matrix smoothness lane), and continuity of those derivative
families on `K`.
-/

noncomputable section
namespace OTSelector.Reconstruction

open scoped NNReal ENNReal

/-- A continuous map on a nonempty compact set has a uniform norm bound. -/
theorem exists_norm_le_of_compact {E G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {f' : E → G}
    (hcont : ContinuousOn f' K) :
    ∃ C : ℝ≥0, ∀ x ∈ K, ‖f' x‖ ≤ (C : ℝ) := by
  have hcont_norm : ContinuousOn (fun x : E => ‖f' x‖) K :=
    continuous_norm.comp_continuousOn hcont
  obtain ⟨xmax, hxmax, hmax⟩ := hK.exists_isMaxOn hne hcont_norm
  refine ⟨⟨‖f' xmax‖, norm_nonneg _⟩, ?_⟩
  intro x hx
  exact hmax hx

/-- On a nonempty compact set, differentiability with continuous derivative family
gives the bounded-derivative interface with an explicit constant. -/
theorem exists_hasBoundedFDerivOn_of_compact {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K) (hne : K.Nonempty)
    {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    (hdiff : ∀ x ∈ K, HasFDerivWithinAt f (f' x) K x)
    (hcont : ContinuousOn f' K) : ∃ C : ℝ≥0, HasBoundedFDerivOn E K f C := by
  obtain ⟨C, hC⟩ := exists_norm_le_of_compact hK hne hcont
  refine ⟨C, f', hdiff, ?_⟩
  intro x hx
  exact (NNReal.coe_le_coe).mp (by simpa using hC x hx)

/-- **Unconditional mark-Lipschitz constants from the coefficient lane.**  A convex
nonempty compact root family, differentiability of `kin` and `g` with the
coefficient-lane derivative formulas, and continuity of those derivatives give
`HasMarkLipschitzConstantsOn` with no further input. -/
theorem hasMarkLipschitzConstantsOn_of_compact_coefficient_lane {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) (hconv : Convex ℝ K) {kin g : E → ℝ}
    {kin' : E → E →L[ℝ] ℝ} {g' : E → E →L[ℝ] ℝ}
    (hkin_diff : ∀ x ∈ K, HasFDerivWithinAt kin (kin' x) K x)
    (hkin_cont : ContinuousOn kin' K)
    (hg_diff : ∀ x ∈ K, HasFDerivWithinAt g (g' x) K x)
    (hg_cont : ContinuousOn g' K) : HasMarkLipschitzConstantsOn E K kin g := by
  obtain ⟨Ck, hCk⟩ := exists_hasBoundedFDerivOn_of_compact hK hne hkin_diff hkin_cont
  obtain ⟨Cg, hCg⟩ := exists_hasBoundedFDerivOn_of_compact hK hne hg_diff hg_cont
  exact hasMarkLipschitzConstantsOn_of_hasBoundedFDerivOn hconv hCk hCg

end OTSelector.Reconstruction
