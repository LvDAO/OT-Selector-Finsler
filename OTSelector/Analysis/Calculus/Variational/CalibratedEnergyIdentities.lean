import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedVelocity
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthHessian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedEnergyIdentities.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedEnergyIdentities`; the selected original proof blocks follow. -/
section

/-!
Conditions: A differentiable energy touches a supporting linear expression, or its value and momentum are constant along the indicated open base slice.

Objects: Actual fiber differential identities and vanishing base or mixed Hessian blocks, with squared-length and chart variants.

Proof detail: Apply Fermat to the touching difference; differentiate the constant base identities and expand the half-square derivative by the chain rule.

Sources: Stephen Boyd, Section 3.1.3, first-order condition, pp. 69–70 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=83); Jiří Lebl, Section 8.6, Proposition 8.6.2, pp. 60–61 (equality of mixed second partial derivatives) (https://www.jirka.org/ra/realanal2.pdf#page=60); Matias Dahl, Section 1.1, Definition 1.2, Remarks 1.3 and Propositions 1.4–1.5, pp. 4–5 (https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=4).
Relation: Locally derived calculus consequences of support and actual derivatives. They do not assert a global eikonal equation from a single contact.
-/

/-!
# Actual first and second energy identities on a calibrated coordinate domain

A fixed covector bounding the original length and saturating a fixed unit velocity
identifies the true length and energy fiber derivatives by Fermat. On an open base
domain the original energy and momentum at that velocity are constant. Their actual
base derivatives vanish; the whole energy differential is the fixed vertical covector.
Differentiating this identity and using the actual Hessian symmetry eliminates both
mixed blocks and the base-base block. No independent quadratic form is prescribed.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {B E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
/-- A differentiable scalar function meeting its linear lower support has precisely
that support covector as its actual differential. -/
theorem fderiv_eq_of_linear_support {L : E → ℝ} (p : E →L[ℝ] ℝ) {v : E}
    (hL : DifferentiableAt ℝ L v) (hbound : ∀ w, p w ≤ L w) (hsat : p v = L v) :
    fderiv ℝ L v = p := by
  have hmin : IsLocalMin (fun w ↦ L w - p w) v := by
    apply Filter.Eventually.of_forall
    intro w
    change L v - p v ≤ L w - p w
    rw [hsat, sub_self]
    exact sub_nonneg.mpr (hbound w)
  exact sub_eq_zero.mp (hmin.hasFDerivAt_eq_zero (hL.hasFDerivAt.sub p.hasFDerivAt))

/-- Constant actual energy and actual vertical momentum at a fixed velocity determine
the complete joint differential; the base component vanishes. -/
theorem fderiv_eq_of_constant_value_and_fiberLegendre
    {L : B × E → ℝ} {U : Set B} (hU : IsOpen U) {v₀ : E} {c : ℝ}
    (p : E →L[ℝ] ℝ) (hvalue : ∀ x ∈ U, L (x, v₀) = c)
    (hmomentum : ∀ x ∈ U, fiberLegendre L (x, v₀) = p)
    {x : B} (hx : x ∈ U) (hL : DifferentiableAt ℝ L (x, v₀)) :
    fderiv ℝ (fun y ↦ L (y, v₀)) x = 0 ∧
      fderiv ℝ L (x, v₀) = p.comp (ContinuousLinearMap.snd ℝ B E) := by
  have heq : (fun y ↦ L (y, v₀)) =ᶠ[𝓝 x] (fun _ ↦ c) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hvalue y hy
  have hbase : fderiv ℝ (fun y ↦ L (y, v₀)) x = 0 := by
    rw [heq.fderiv_eq]
    simp
  refine ⟨hbase, ?_⟩
  have hb (u : B) : fderiv ℝ L (x, v₀) (u, 0) = 0 := by
    have hc : HasFDerivAt (fun y : B ↦ L (y, v₀))
        ((fderiv ℝ L (x, v₀)).comp (ContinuousLinearMap.inl ℝ B E)) x :=
      hL.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x v₀)
    have h := congrArg (fun D ↦ D u) hc.fderiv
    rw [hbase] at h
    exact h.symm
  have hv (w : E) : fderiv ℝ L (x, v₀) (0, w) = p w := by
    have h := congrArg (fun D ↦ D w)
      (hL.hasFDerivAt.comp v₀ (hasFDerivAt_prodMk_right x v₀)).fderiv
    change fiberLegendre L (x, v₀) w = fderiv ℝ L (x, v₀) (0, w) at h
    rw [hmomentum x hx] at h
    exact h.symm
  apply ContinuousLinearMap.ext
  intro z
  have hsplit : z = (z.1, (0 : E)) + ((0 : B), z.2) := by simp
  rw [hsplit, map_add, hb, hv, zero_add]
  simp

/-- Differentiating the actual constant joint differential eliminates every Hessian
entry whose first argument is a base direction, and symmetry eliminates the reverse. -/
theorem hessian_base_zero_of_constant_value_and_fiberLegendre
    {L : B × E → ℝ} {U : Set B} (hU : IsOpen U) {v₀ : E} {c : ℝ}
    (p : E →L[ℝ] ℝ) (hvalue : ∀ x ∈ U, L (x, v₀) = c)
    (hmomentum : ∀ x ∈ U, fiberLegendre L (x, v₀) = p)
    (hL : ∀ x ∈ U, ContDiffAt ℝ 2 L (x, v₀)) {x : B} (hx : x ∈ U) :
    (∀ u : B, fderiv ℝ (fderiv ℝ L) (x, v₀) (u, 0) = 0) ∧
      ∀ u : B, ∀ z : B × E, fderiv ℝ (fderiv ℝ L) (x, v₀) z (u, 0) = 0 := by
  have heq : (fun y ↦ fderiv ℝ L (y, v₀)) =ᶠ[𝓝 x]
      (fun _ ↦ p.comp (ContinuousLinearMap.snd ℝ B E)) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (fderiv_eq_of_constant_value_and_fiberLegendre hU p hvalue hmomentum hy
      ((hL y hy).differentiableAt (by norm_num))).2
  have hd := ((hL x hx).fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hh : ∀ u : B, fderiv ℝ (fderiv ℝ L) (x, v₀) (u, 0) = 0 := by
    intro u
    have hc : HasFDerivAt (fun y : B ↦ fderiv ℝ L (y, v₀))
        ((fderiv ℝ (fderiv ℝ L) (x, v₀)).comp
          (ContinuousLinearMap.inl ℝ B E)) x :=
      hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x v₀)
    have hg := congrArg (fun D ↦ D u) hc.fderiv
    rw [heq.fderiv_eq] at hg
    simpa using hg.symm
  refine ⟨hh, ?_⟩
  intro u z
  rw [((hL x hx).isSymmSndFDerivAt (by norm_num)).eq z (u, 0), hh, zero_apply]

/-- A genuine calibrated length and its actual half-square energy yield all first
identities and all zero base Hessian blocks on an open base domain. The length and
energy may be supplied by an actual coordinate pullback of the original geometry. -/
theorem calibrated_half_sq_energy_identities {L G : B × E → ℝ}
    {U : Set B} (hU : IsOpen U) (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hsq : ∀ y ∈ U, ∀ w : E, L (y, w) = G (y, w) ^ 2 / 2)
    (hunit : ∀ y ∈ U, G (y, v₀) = 1)
    (hbound : ∀ y ∈ U, ∀ w : E, p w ≤ G (y, w))
    (hG : ∀ y ∈ U, DifferentiableAt ℝ (fun w ↦ G (y, w)) v₀)
    (hL : ∀ y ∈ U, ContDiffAt ℝ 2 L (y, v₀)) {x : B} (hx : x ∈ U) :
    fderiv ℝ (fun w ↦ G (x, w)) v₀ = p ∧
    L (x, v₀) = 1 / 2 ∧
    fiberLegendre L (x, v₀) = p ∧
    fderiv ℝ (fun y ↦ L (y, v₀)) x = 0 ∧
    fderiv ℝ (fun y ↦ fiberLegendre L (y, v₀)) x = 0 ∧
    fderiv ℝ L (x, v₀) = p.comp (ContinuousLinearMap.snd ℝ B E) ∧
    (∀ u : B, fderiv ℝ (fderiv ℝ L) (x, v₀) (u, 0) = 0) ∧
    ∀ u : B, ∀ z : B × E, fderiv ℝ (fderiv ℝ L) (x, v₀) z (u, 0) = 0 := by
  have hvalue (y : B) (hy : y ∈ U) : L (y, v₀) = 1 / 2 := by
    rw [hsq y hy, hunit y hy]
    norm_num
  have hlength (y : B) (hy : y ∈ U) :
      fderiv ℝ (fun w ↦ G (y, w)) v₀ = p :=
    fderiv_eq_of_linear_support p (hG y hy) (hbound y hy) (hp.trans (hunit y hy).symm)
  have hmomentum (y : B) (hy : y ∈ U) : fiberLegendre L (y, v₀) = p := by
    have hf : DifferentiableAt ℝ (fun w ↦ L (y, w)) v₀ :=
      ((hL y hy).differentiableAt (by norm_num)).comp v₀
        (differentiableAt_const y |>.prodMk differentiableAt_id)
    exact fderiv_half_sq_eq_of_unit_calibration p (hsq y hy) hf
      (hunit y hy) (hbound y hy) hp
  have hfirst := fderiv_eq_of_constant_value_and_fiberLegendre hU p hvalue hmomentum hx
    ((hL x hx).differentiableAt (by norm_num))
  have hsecond := hessian_base_zero_of_constant_value_and_fiberLegendre hU p hvalue
    hmomentum hL hx
  have hpbase : fderiv ℝ (fun y ↦ fiberLegendre L (y, v₀)) x = 0 := by
    have heq : (fun y ↦ fiberLegendre L (y, v₀)) =ᶠ[𝓝 x] (fun _ ↦ p) := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hmomentum y hy
    rw [heq.fderiv_eq]
    simp
  exact ⟨hlength x hx, hvalue x hx, hmomentum x hx, hfirst.1, hpbase,
    hfirst.2, hsecond.1, hsecond.2⟩

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}
  (hF : F.IsSmoothStronglyConvex)
include hF

omit [NormedAddCommGroup B] [NormedSpace ℝ B] in
/-- A fixed unit velocity calibrated throughout an actual open chart domain has the
original energy value and momentum, zero base differential, and zero actual xx/xv/vx
Hessian blocks. All differentials belong to the given Finsler length and energy. -/
theorem chartEnergy_calibrated_identities (old : M) {U : Set E} (hU : IsOpen U)
    (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target) (p : E →L[ℝ] ℝ) {v₀ : E}
    (hp : p v₀ = 1) (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1)
    (hbound : ∀ x ∈ U, ∀ w : E, p w ≤ (F.chartLength old (x, w) : ℝ))
    {x : E} (hx : x ∈ U) :
    fderiv ℝ (fun w ↦ (F.chartLength old (x, w) : ℝ)) v₀ = p ∧
    F.chartEnergy old (x, v₀) = 1 / 2 ∧
    fiberLegendre (F.chartEnergy old) (x, v₀) = p ∧
    fderiv ℝ (fun y ↦ F.chartEnergy old (y, v₀)) x = 0 ∧
    fderiv ℝ (fun y ↦ fiberLegendre (F.chartEnergy old) (y, v₀)) x = 0 ∧
    fderiv ℝ (F.chartEnergy old) (x, v₀) = p.comp (ContinuousLinearMap.snd ℝ E E) ∧
    (∀ u : E, fderiv ℝ (fderiv ℝ (F.chartEnergy old)) (x, v₀) (u, 0) = 0) ∧
    ∀ u : E, ∀ z : E × E,
      fderiv ℝ (fderiv ℝ (F.chartEnergy old)) (x, v₀) z (u, 0) = 0 := by
  have hv₀ : v₀ ≠ 0 := by
    intro hv
    rw [hv, _root_.map_zero] at hp
    exact zero_ne_one hp
  apply calibrated_half_sq_energy_identities (L := F.chartEnergy old)
    (G := fun z ↦ (F.chartLength old z : ℝ)) (x := x) hU p hp
    (fun y _ w ↦ F.chartEnergy_eq_chartLength_sq old (y, w))
    (fun y hy ↦ by exact_mod_cast hunit y hy) hbound
  · intro y hy
    exact (hF.contDiffAt_chartFiberLength old (z := (y, v₀)) ⟨hsub hy, hv₀⟩)
      |>.differentiableAt (by simp)
  · intro y hy
    exact ((hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds
        (show (y, v₀) ∈ chartEnergyDomain old from ⟨hsub hy, hv₀⟩))).of_le (by simp)
  · exact hx

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
