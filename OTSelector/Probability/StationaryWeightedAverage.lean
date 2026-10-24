import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import OTSelector.Analysis.InnerProductSpace.TranslationCoboundary
import OTSelector.Probability.StationaryHyperplaneInvariantProjection

/-!
Conditions: A finite-dimensional real parameter space, a real Hilbert space and a strongly continuous family of linear isometries; coboundary/limit statements additionally assume the displayed action law and an arbitrary integrable scalar weight.

Objects: L1 continuity of translated weights, actual bounded Bochner orbit-average operators and their vanishing on the orthogonal complement of the invariant subspace; arbitrary scale-dependent offsets are permitted in the face specialization.

Proof detail: Change variables in a coboundary average to a small translation difference of the L1 weight. Uniform operator bounds extend this vanishing from coboundaries to the invariant orthogonal complement; factor offsets as norm-preserving commuting isometries.

References: Terence Tao: Section 1.4, Exercises 1.4.12–1.4.13, pp. 52–53; Sheldon Axler: Section 8B, Definition 8.34, p. 227; Theorem 8.37 and proof, p. 228.
Relation: A locally proved continuous multiparameter weighted mean argument using Hilbert projection/coboundary closure. The references support those elementary ingredients; no uninspected printed theorem with this arbitrary integrable weight and offset is claimed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.StationaryWeightedFaceAverage.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.StationaryWeightedFaceAverage`; the selected original proof blocks follow. -/
section

/-! Weighted spatial averages of genuine strongly continuous isometric orbits. -/
open Set Function Filter MeasureTheory
open scoped ENNReal Topology InnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

variable {ι : Type*} [Fintype ι]

/-- Integrable scalar spatial weights are continuous under actual translations
in L1. The proof uses Mathlib's continuous measure-preserving composition. -/
theorem tendsto_integral_norm_weight_translation_sub
    {w : (ι → ℝ) → ℝ} (hw : Integrable w volume) :
    Tendsto (fun a : ι → ℝ ↦ ∫ y, ‖w (y - a) - w y‖) (𝓝 0) (𝓝 0) := by
  let f : Lp ℝ 1 (volume : Measure (ι → ℝ)) := hw.toL1 w
  let g : C((ι → ℝ), C((ι → ℝ), (ι → ℝ))) :=
    (ContinuousMap.mk (fun p : (ι → ℝ) × (ι → ℝ) ↦ p.2 - p.1)
      (continuous_snd.sub continuous_fst)).curry
  have hgm : ∀ a, MeasurePreserving (g a) volume volume := by
    intro a
    exact measurePreserving_sub_right volume a
  have hc : Continuous (fun a ↦ Lp.compMeasurePreserving (g a) (hgm a) f) :=
    continuous_const.compMeasurePreservingLp g.continuous hgm (by norm_num)
  have hzero : Lp.compMeasurePreserving (g 0) (hgm 0) f = f := by
    have hg0 : (g 0 : (ι → ℝ) → (ι → ℝ)) = id := by
      funext y
      exact sub_zero y
    simp only [hg0, Lp.compMeasurePreserving_id, AddMonoidHom.id_apply]
  have hlim : Tendsto (fun a ↦ ‖Lp.compMeasurePreserving (g a) (hgm a) f - f‖)
      (𝓝 0) (𝓝 0) := by
    simpa only [hzero, sub_self, norm_zero] using
      ((hc.tendsto 0).sub (tendsto_const_nhds :
        Tendsto (fun _ : ι → ℝ ↦ f) (𝓝 0) (𝓝 f))).norm
  apply hlim.congr'
  filter_upwards [] with a
  rw [← dist_eq_norm, L1.dist_eq_integral_dist]
  apply integral_congr_ae
  have hshift := (hgm a).quasiMeasurePreserving.ae_eq_comp hw.coeFn_toL1
  filter_upwards [Lp.coeFn_compMeasurePreserving f (hgm a), hshift, hw.coeFn_toL1]
    with y hy hs hf
  simp only [Function.comp_apply] at hy hs
  rw [hy, hs, hf, dist_eq_norm]
  rfl

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (U : (ι → ℝ) → H ≃ₗᵢ[ℝ] H) (hcont : ∀ x, Continuous (fun v ↦ U v x))
  {w : (ι → ℝ) → ℝ} (hw : Integrable w volume)
include hcont hw

omit [CompleteSpace H] in
/-- The actual scalar-weighted isometric orbit is Bochner integrable. -/
theorem integrable_stationaryWeightedOrbit (R : ℝ) (x : H) :
    Integrable (fun y ↦ w y • U (R • y) x) volume := by
  have hc : Continuous (fun y : ι → ℝ ↦ U (R • y) x) :=
    (hcont x).comp (show Continuous (fun y : ι → ℝ ↦ R • y) by fun_prop)
  exact hw.smul_bdd ‖x‖ hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y ↦ ((U (R • y)).norm_map x).le)

omit hcont hw [CompleteSpace H] in
/-- An integrable scalar weight bounds its actual orbit average uniformly
in the spatial scale by its L1 norm times the original vector norm. -/
theorem norm_integral_stationaryWeightedOrbit_le (R : ℝ) (x : H) :
    ‖∫ y, w y • U (R • y) x‖ ≤ (∫ y, ‖w y‖) * ‖x‖ := by
  calc
    _ ≤ ∫ y, ‖w y • U (R • y) x‖ := norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_smul, (U _).norm_map]
      exact integral_mul_const _ _

/-- The literal weighted spatial orbit average as a linear map. -/
def stationaryWeightedAverageLinear (R : ℝ) : H →ₗ[ℝ] H where
  toFun x := ∫ y, w y • U (R • y) x
  map_add' x y := by
    simp_rw [map_add, smul_add]
    exact integral_add (integrable_stationaryWeightedOrbit U hcont hw R x)
      (integrable_stationaryWeightedOrbit U hcont hw R y)
  map_smul' c x := by
    simp_rw [map_smul, smul_comm (w _) c]
    exact integral_smul c _

/-- Weighted spatial averages are bounded linear operators, with a fixed
positive bound independent of the spatial scale. -/
def stationaryWeightedAverage (R : ℝ) : H →L[ℝ] H :=
  (stationaryWeightedAverageLinear U hcont hw R).mkContinuous ((∫ y, ‖w y‖) + 1)
    (fun x ↦ (norm_integral_stationaryWeightedOrbit_le U R x).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)))

omit [CompleteSpace H] in
/-- The bounded operator retains the exact original weighted integral. -/
theorem stationaryWeightedAverage_apply (R : ℝ) (x : H) :
    stationaryWeightedAverage U hcont hw R x = ∫ y, w y • U (R • y) x := rfl

omit [CompleteSpace H] in
/-- The weighted operators have one uniform deterministic norm bound. -/
theorem norm_stationaryWeightedAverage_le (R : ℝ) :
    ‖stationaryWeightedAverage U hcont hw R‖ ≤ (∫ y, ‖w y‖) + 1 := by
  exact LinearMap.mkContinuous_norm_le _ (by positivity) _

variable (hadd : ∀ a b x, U a (U b x) = U (a + b) x)
include hadd

omit [CompleteSpace H] in
/-- The weighted average of an actual translation difference is exactly
an integral against the translated difference of the original scalar weight. -/
theorem integral_stationaryWeightedOrbit_coboundary_eq
    {R : ℝ} (hR : R ≠ 0) (a : ι → ℝ) (x : H) :
    (∫ y, w y • U (R • y) (U a x - x)) =
      ∫ y, (w (y - R⁻¹ • a) - w y) • U (R • y) x := by
  have hscale : R • (R⁻¹ • a) = a := by rw [smul_smul, mul_inv_cancel₀ hR, one_smul]
  have hshift : Integrable (fun y ↦ w (y - R⁻¹ • a)) volume :=
    hw.comp_sub_right (R⁻¹ • a)
  calc
    _ = ∫ y, w y • U (R • y) (U a x) - w y • U (R • y) x := by
      congr 1
      funext y
      rw [map_sub, smul_sub]
    _ = (∫ y, w y • U (R • y) (U a x)) - ∫ y, w y • U (R • y) x :=
      integral_sub (integrable_stationaryWeightedOrbit U hcont hw R (U a x))
        (integrable_stationaryWeightedOrbit U hcont hw R x)
    _ = (∫ y, w (y - R⁻¹ • a) • U (R • y) x) - ∫ y, w y • U (R • y) x := by
      congr 1
      rw [← integral_sub_right_eq_self (fun y ↦ w y • U (R • y) (U a x)) (R⁻¹ • a)]
      congr 1
      funext y
      rw [hadd, smul_sub, hscale, sub_add_cancel]
    _ = _ := by
      rw [← integral_sub (integrable_stationaryWeightedOrbit U hcont hshift R x)
        (integrable_stationaryWeightedOrbit U hcont hw R x)]
      congr 1
      funext y
      rw [sub_smul]

omit [CompleteSpace H] in
/-- Actual weighted averages annihilate every genuine translation coboundary.
Only the scalar weight's L1 translation continuity enters the estimate. -/
theorem tendsto_stationaryWeightedAverage_coboundary (a : ι → ℝ) (x : H) :
    Tendsto (fun R : ℝ ↦ stationaryWeightedAverage U hcont hw R (U a x - x))
      atTop (𝓝 0) := by
  have hshift : Tendsto (fun R : ℝ ↦ R⁻¹ • a) atTop (𝓝 0) := by
    simpa only [zero_smul] using
      (tendsto_inv_atTop_zero : Tendsto (fun R : ℝ ↦ R⁻¹) atTop (𝓝 0)).smul_const a
  have hlim := (tendsto_integral_norm_weight_translation_sub hw).comp hshift
  have hlim' : Tendsto (fun R : ℝ ↦
      (∫ y, ‖w (y - R⁻¹ • a) - w y‖) * ‖x‖) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul] using hlim.mul_const ‖x‖
  apply tendsto_zero_iff_norm_tendsto_zero.2
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _)
    (Filter.eventually_atTop.2 ⟨1, fun R hR ↦ ?_⟩) hlim'
  rw [stationaryWeightedAverage_apply,
    integral_stationaryWeightedOrbit_coboundary_eq U hcont hw hadd (by linarith) a x]
  exact norm_integral_stationaryWeightedOrbit_le U R x

/-- Integrable scalar-weighted spatial averages tend to zero whenever the
actual vector has zero component in the full joint invariant subspace. -/
theorem tendsto_stationaryWeightedAverage_zero
    {x : H} (hx : x ∈ (translationFixedSubspace U ⊤)ᗮ) :
    Tendsto (fun R : ℝ ↦ stationaryWeightedAverage U hcont hw R x) atTop (𝓝 0) := by
  let C : ℝ := (∫ y, ‖w y‖) + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  let A : ℝ → H →L[ℝ] H := fun R ↦ C⁻¹ • stationaryWeightedAverage U hcont hw R
  have hA : ∀ R, ‖A R‖ ≤ 1 := by
    intro R
    dsimp only [A]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hC]
    calc
      C⁻¹ * ‖stationaryWeightedAverage U hcont hw R‖ ≤ C⁻¹ * C :=
        mul_le_mul_of_nonneg_left (norm_stationaryWeightedAverage_le U hcont hw R)
          (by positivity)
      _ = 1 := inv_mul_cancel₀ hC.ne'
  have hcob : ∀ a y, Tendsto (fun R : ℝ ↦ A R (U a y - y)) atTop (𝓝 0) := by
    intro a y
    simpa only [A, smul_apply, smul_zero] using
      (tendsto_stationaryWeightedAverage_coboundary U hcont hw hadd a y).const_smul C⁻¹
  have hzero := tendsto_contractions_zero_of_translation_coboundaries atTop U A hA hcob hx
  have hout := hzero.const_smul C
  simp only [smul_zero] at hout
  apply hout.congr'
  filter_upwards [] with R
  dsimp only [A]
  rw [smul_apply, smul_smul, mul_inv_cancel₀ hC.ne', one_smul]

omit hcont hw hadd

/-- Every integrable face weight has vanishing actual averages when the
face-invariant component is zero. The offset may depend arbitrarily on R:
normal and tangential shifts act by a commuting isometry outside the integral. -/
theorem tendsto_stationaryWeightedFaceAverage_zero
    {G : Type*} [AddCommGroup G] [Module ℝ G]
    (V : G → H ≃ₗᵢ[ℝ] H) (haddV : ∀ a b x, V a (V b x) = V (a + b) x)
    (L : (ι → ℝ) →ₗ[ℝ] G)
    (hcontV : ∀ x, Continuous (fun v ↦ V (L v) x))
    {w : (ι → ℝ) → ℝ} (hw : Integrable w volume)
    {x : H} (hx : (translationFixedSubspace V L.range).starProjection x = 0)
    (offset : ℝ → G) :
    Tendsto (fun R : ℝ ↦ ∫ y, w y • V (offset R + L (R • y)) x) atTop (𝓝 0) := by
  have haddL : ∀ a b x, V (L a) (V (L b) x) = V (L (a + b)) x := by
    intro a b z
    simpa only [map_add] using haddV (L a) (L b) z
  have hx' : x ∈ (translationFixedSubspace (fun v ↦ V (L v)) ⊤)ᗮ := by
    rw [translationFixedSubspace_comp_linearMap]
    exact (Submodule.starProjection_apply_eq_zero_iff
      (translationFixedSubspace V L.range)).1 hx
  have hlim := tendsto_stationaryWeightedAverage_zero
    (fun v ↦ V (L v)) hcontV hw haddL hx'
  apply tendsto_zero_iff_norm_tendsto_zero.2
  have hnorm : Tendsto (fun R : ℝ ↦
      ‖stationaryWeightedAverage (fun v ↦ V (L v)) hcontV hw R x‖) atTop (𝓝 0) := by
    simpa only [norm_zero] using hlim.norm
  apply hnorm.congr'
  filter_upwards [] with R
  simp only [stationaryWeightedAverage_apply]
  have he : (∫ y, w y • V (offset R + L (R • y)) x) =
      V (offset R) (∫ y, w y • V (L (R • y)) x) := by
    calc
      _ = ∫ y, (V (offset R)).toLinearIsometry (w y • V (L (R • y)) x) := by
        congr 1
        funext y
        change w y • V (offset R + L (R • y)) x =
          V (offset R) (w y • V (L (R • y)) x)
        rw [map_smul (V (offset R)), haddV]
      _ = _ := (V (offset R)).toLinearIsometry.integral_comp_comm _
  rw [he, (V (offset R)).norm_map]



end OTSelector.Reconstruction

end
end
