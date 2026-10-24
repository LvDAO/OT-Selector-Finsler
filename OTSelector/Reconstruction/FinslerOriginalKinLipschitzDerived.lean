import Mathlib.Analysis.Calculus.MeanValue
import OTSelector.Reconstruction.FinslerOriginalMarkLipschitzConstants

/-!
# Mean value Lipschitz step for kin and g

This module derives the Lipschitz bounds that `FinslerOriginalMarkLipschitzConstants`
takes as hypothesis, by the mean value inequality from a bounded Frechet derivative.

On a compact convex chart image `K` of the retained roots, the kinetic mark function
`kin` and the probe `g` are differentiable with bounded derivative (the C1/C2
coefficient smoothness of the compact-root lane).  The mean value inequality
(`Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le`) then gives
`LipschitzOnWith Ck kin K` and `LipschitzOnWith Cg g K`, with `Ck`, `Cg` the sup of
the Frechet derivative norms.  Restricting to `K` and reading `dist` on `ℝ` as
`|· - ·|` produces the pairwise mark-Lipschitz bounds, hence the interface
`HasMarkLipschitzConstantsOn E K kin g` consumed by the mark modulus lane.

Everything here is a genuine derivation from the bounded-derivative data; no
Lipschitz constant is assumed.  The data still supplied as explicit hypotheses are
(a) the differentiability of `kin` and `g` on `K` with the chosen derivative
functions (the coefficient-lane differentiability) and (b) the derivative norm
bounds `Ck`, `Cg`; extracting these bounds as a constant from compactness of `K`
and continuity of the derivative is the only remaining bookkeeping step, and it is
stated precisely below rather than assumed silently.
-/

noncomputable section
namespace OTSelector.Reconstruction

open scoped NNReal ENNReal

/-- **Mean value Lipschitz step.**  A differentiable function on a convex set with
bounded Frechet derivative is Lipschitz on the set, with the derivative sup as
constant. -/
theorem lipschitzOnWith_of_bounded_fderiv {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {K : Set E} (hK : Convex ℝ K) {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {C : ℝ≥0}
    (H : ∀ x ∈ K, HasFDerivWithinAt f (f' x) K x)
    (hC : ∀ x ∈ K, ‖f' x‖₊ ≤ C) : LipschitzOnWith C f K :=
  hK.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le H hC

/-- The pairwise real form of the Lipschitz bound on `K`. -/
theorem abs_sub_le_of_lipschitzOnWith {E : Type*} [PseudoMetricSpace E]
    {K : Set E} {f : E → ℝ} {C : ℝ≥0} (h : LipschitzOnWith C f K)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    |f x - f y| ≤ (C : ℝ) * dist x y := by
  have hd := h.dist_le_mul x hx y hy
  simpa [Real.dist_eq] using hd

/-- **The derived mark-Lipschitz constants.**  Differentiability of `kin` and `g`
on the convex retained root family with derivative norm bounds `Ck`, `Cg` yields
the interface consumed by the mark modulus lane. -/
theorem hasMarkLipschitzConstantsOn_of_bounded_fderiv {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} (hK : Convex ℝ K)
    {kin g : E → ℝ} {kin' : E → E →L[ℝ] ℝ} {g' : E → E →L[ℝ] ℝ}
    {Ck Cg : ℝ≥0}
    (Hkin : ∀ x ∈ K, HasFDerivWithinAt kin (kin' x) K x)
    (hCkin : ∀ x ∈ K, ‖kin' x‖₊ ≤ Ck)
    (Hg : ∀ x ∈ K, HasFDerivWithinAt g (g' x) K x)
    (hCg : ∀ x ∈ K, ‖g' x‖₊ ≤ Cg) :
    HasMarkLipschitzConstantsOn E K kin g := by
  have hlk : LipschitzOnWith Ck kin K := lipschitzOnWith_of_bounded_fderiv hK Hkin hCkin
  have hlg : LipschitzOnWith Cg g K := lipschitzOnWith_of_bounded_fderiv hK Hg hCg
  constructor
  · refine ⟨(Ck : ℝ), by positivity, ?_⟩
    intro x hx y hy
    exact abs_sub_le_of_lipschitzOnWith hlk hx hy
  · refine ⟨(Cg : ℝ), by positivity, ?_⟩
    intro x hx y hy
    exact abs_sub_le_of_lipschitzOnWith hlg hx hy

end OTSelector.Reconstruction
