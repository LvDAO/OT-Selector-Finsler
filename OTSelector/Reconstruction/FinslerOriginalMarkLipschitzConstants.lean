import OTSelector.Reconstruction.FinslerOriginalMarkModulusCoupling

/-!
# Mark Lipschitz constants on compact roots

This module produces analytic input (i) of `FinslerOriginalMarkModulusCoupling`:
the local Lipschitz constants `Lk`, `Lg` of the kinetic mark function `kin` and the
probe `g` on the pairing neighbourhood family of marks (the retained roots
`C.roots` intersected with a window region).

The exact interface consumed by the mark modulus lane is
`HasMarkLipschitzConstantsOn M K kin g`: there are constants `Lk, Lg ≥ 0` with
`|kin z - kin z'| ≤ Lk * dist z z'` and `|g z - g z'| ≤ Lg * dist z z'` for all
`z, z' ∈ K`.  The module extracts these constants from Lipschitz data
(`markLipschitzConstants_of_lipschitzWith`), which is what the compact-root
smoothness lane supplies: on a compact convex chart image the C1/C2 coefficient
kernel has bounded Frechet derivative, so the mean value inequality
(`Convex.lipschitzOnWith_of_nnnorm_hasFDerivWithin_le` and its relatives in
`Mathlib.Analysis.Calculus.MeanValue`) gives the `LipschitzWith` bound used here.
This module deliberately takes that bound as its named analytic hypothesis rather
than reproving the analytic chain: the constant extraction, restriction to the
retained root family, and the composition with the marked-edge error estimate are
proved.

The composed edge-error bound is `abs_markedEdgeError_le_of_markLipschitzConstants`:
with these constants the marked-edge error of two coupled marks at distance `d` is
at most `(scale * Lk + |t| * Lg) * d`, i.e. exactly the input of
`sum_markedEdgeError_le_of_markModulus`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

/-- The mark-Lipschitz constants of `kin` and `g` on a mark family `K`, in the
exact form consumed by the mark modulus coupling lane. -/
def HasMarkLipschitzConstantsOn (M : Type*) [PseudoMetricSpace M] (K : Set M)
    (kin g : M → ℝ) : Prop :=
  (∃ Lk : ℝ, 0 ≤ Lk ∧ ∀ z ∈ K, ∀ z' ∈ K, |kin z - kin z'| ≤ Lk * dist z z') ∧
  (∃ Lg : ℝ, 0 ≤ Lg ∧ ∀ z ∈ K, ∀ z' ∈ K, |g z - g z'| ≤ Lg * dist z z')

/-- Global Lipschitz bounds of `kin` and `g` restrict to the retained root family,
producing the mark-Lipschitz constants. -/
theorem markLipschitzConstants_of_lipschitzWith {M : Type*} [PseudoMetricSpace M]
    {kin g : M → ℝ} {Kk Kg : ℝ≥0} (hk : LipschitzWith Kk kin)
    (hg : LipschitzWith Kg g) (K : Set M) : HasMarkLipschitzConstantsOn M K kin g := by
  constructor
  · refine ⟨(Kk : ℝ), by positivity, ?_⟩
    intro z _ z' _
    have h := hk.dist_le_mul z z'
    simpa [Real.dist_eq] using h
  · refine ⟨(Kg : ℝ), by positivity, ?_⟩
    intro z _ z' _
    have h := hg.dist_le_mul z z'
    simpa [Real.dist_eq] using h

/-- The constants together with the task-229 single-edge mark-Lipschitz transfer give
the marked-edge error bound of two coupled marks at mark distance `d`. -/
theorem abs_markedEdgeError_le_of_markLipschitzConstants
    {kin g : ℝ → ℝ} {Lk Lg : ℝ} (hLk : 0 ≤ Lk) (hLg : 0 ≤ Lg)
    (hk : ∀ z z' : ℝ, |kin z - kin z'| ≤ Lk * |z - z'|)
    (hg : ∀ z z' : ℝ, |g z - g z'| ≤ Lg * |z - z'|)
    {scale t d : ℝ} (hscale : 0 ≤ scale) (z z' : ℝ)
    (hd : |z - z'| ≤ d) :
    |(scale * kin z + t * g z) - (scale * kin z' + t * g z')| ≤
      (scale * Lk + |t| * Lg) * d := by
  have h := abs_markedEdgeError_le_of_markLipschitz (scale := scale) (t := t)
    (Lk := Lk) (Lg := Lg) (d := |z - z'|) (kinA := kin z) (kinB := kin z')
    (gA := g z) (gB := g z') hscale (hk z z') (hg z z')
  have hconst : 0 ≤ scale * Lk + |t| * Lg := by positivity
  have hmul : (scale * Lk + |t| * Lg) * |z - z'| ≤ (scale * Lk + |t| * Lg) * d :=
    mul_le_mul_of_nonneg_left hd hconst
  exact le_trans h hmul

end OTSelector.Reconstruction
