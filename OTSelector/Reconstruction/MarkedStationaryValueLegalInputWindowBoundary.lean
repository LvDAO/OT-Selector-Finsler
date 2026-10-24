import OTSelector.Reconstruction.MarkedStationaryValueHaarRootBoundary
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputWindow

/-! The actual original Haar root is asymptotically interior to every fixed
physical observation window. All estimates use the same affine original box. -/

open Set Function Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- One unit of spare margin puts the entire closed observation window
strictly inside the actual open physical input box. -/
theorem haarRootCube_subset_legalInputPhysicalBox_of_inner_root
    (q : ℕ) {L S : ℝ} (hS : 0 ≤ S) (hmargin : S + 1 < L / 2)
    {z : Fin q → ℝ} (hz : z ∈ haarRootCube (Fin q) (L / 2 - S - 1)) :
    haarRootCube (Fin q) S ⊆ legalInputPhysicalBox q
      (fun i ↦ -L / 2 - z i) (Real.toNNReal L) := by
  have hL : 0 < L := by linarith
  intro x hx
  change affineHaarCubeCoord (ContinuousLinearEquiv.refl ℝ (Fin q → ℝ))
    (fun i ↦ -L / 2 - z i) (Real.toNNReal L) x ∈ seedUnitCube q
  intro i _
  change 0 < (Real.toNNReal L : ℝ)⁻¹ * (x i - (-L / 2 - z i)) ∧
    (Real.toNNReal L : ℝ)⁻¹ * (x i - (-L / 2 - z i)) < 1
  rw [Real.coe_toNNReal _ hL.le]
  have hxl := hx.1 i
  have hxu := hx.2 i
  have hzl := hz.1 i
  have hzu := hz.2 i
  dsimp at hxl hxu hzl hzu
  constructor
  · exact mul_pos (inv_pos.mpr hL) (by linarith)
  · rw [mul_comm, ← div_eq_mul_inv, div_lt_one hL]
    linarith

/-- The mass of one actual inner root cube is its exact volume ratio. -/
theorem haarCubeRootLaw_inner_cube (q : ℕ) {R S : ℝ}
    (hS : 0 ≤ S) (hR : S < R) :
    haarCubeRootLaw (Fin q) R (haarRootCube (Fin q) (R - S)) =
      ENNReal.ofReal (((R - S) / R) ^ q) := by
  have hRpos : 0 < R := lt_of_le_of_lt hS hR
  have hsub : haarRootCube (Fin q) (R - S) ⊆ haarRootCube (Fin q) R := by
    intro z hz
    constructor <;> intro i <;> have hl := hz.1 i <;> have hu := hz.2 i <;>
      dsimp at * <;> linarith
  rw [haarCubeRootLaw, cavityRootMeasure, Measure.smul_apply,
    Measure.restrict_apply (show MeasurableSet (haarRootCube (Fin q) (R - S)) from measurableSet_Icc),
    inter_eq_left.mpr hsub,
    volume_haarRootCube (Fin q) (sub_nonneg.mpr hR.le), Fintype.card_fin, smul_eq_mul,
    mul_comm, ← div_eq_mul_inv, ← ENNReal.ofReal_div_of_pos (pow_pos (by positivity) q)]
  congr 1
  rw [← div_pow]
  congr 1
  field_simp

/-- On the same actual normalized root law, the probability of being too
close to the boundary tends to zero along all real box radii. -/
theorem tendsto_haarCubeRootLaw_inner_compl (q : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    Tendsto (fun R : ℝ ↦ haarCubeRootLaw (Fin q) R
      (haarRootCube (Fin q) (R - S))ᶜ) atTop (𝓝 0) := by
  have hsmall : Tendsto (fun R : ℝ ↦ S / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hratio : Tendsto (fun R : ℝ ↦ (1 - S / R) ^ q) atTop (𝓝 (1 : ℝ)) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hsmall).pow q
  have hreal : Tendsto (fun R : ℝ ↦ ENNReal.ofReal ((1 - S / R) ^ q))
      atTop (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp hratio
  have hzero : Tendsto (fun R : ℝ ↦ 1 - ENNReal.ofReal ((1 - S / R) ^ q))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa only [Function.comp_def, tsub_self] using
      (ENNReal.continuous_sub_left (a := 1) (by simp)).continuousAt.tendsto.comp hreal
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop S] with R hR
  have hRpos : 0 < R := lt_of_le_of_lt hS hR
  let : IsProbabilityMeasure (haarCubeRootLaw (Fin q) R) :=
    isProbabilityMeasure_haarCubeRootLaw (Fin q) hRpos
  rw [measure_compl (show MeasurableSet (haarRootCube (Fin q) (R - S)) from measurableSet_Icc)
      (measure_ne_top _ _), measure_univ,
    haarCubeRootLaw_inner_cube q hS hR]
  congr 2
  field_simp

/-- The actual root normalization and physical box side used by the original
finite optimizer have the same vanishing boundary probability. -/
theorem tendsto_legalInput_inner_root_compl (q : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    Tendsto (fun L : ℝ ↦
      cavityRootMeasure (volume : Measure (Fin q → ℝ))
        (haarRootCube (Fin q) (L / 2)) (L ^ q)
        (haarRootCube (Fin q) (L / 2 - S - 1))ᶜ) atTop (𝓝 0) := by
  have hhalf : Tendsto (fun L : ℝ ↦ L / 2) atTop atTop :=
    tendsto_id.atTop_div_const (by norm_num)
  have h := (tendsto_haarCubeRootLaw_inner_compl q (show 0 ≤ S + 1 by linarith)).comp hhalf
  convert h using 1
  funext L
  simp only [haarCubeRootLaw, Fintype.card_fin, Function.comp_def,
    show 2 * (L / 2) = L by ring,
    show L / 2 - S - 1 = L / 2 - (S + 1) by ring]

end OTSelector.Reconstruction
