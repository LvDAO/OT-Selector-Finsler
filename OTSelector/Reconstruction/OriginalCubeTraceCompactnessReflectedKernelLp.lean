import OTSelector.Reconstruction.OriginalCubeTraceCompactnessReflectedKernel
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! Uniform actual Lp bounds for the literal reflected full-input response. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
namespace OTSelector.Reconstruction
open OTSelector.Probability
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The literal unit neighborhood of an input has its fixed original Haar volume. -/
theorem volume_originalInputUnitNeighborhood (x : ι → ℝ) :
    volume ((fun z : ι → ℝ ↦ z - x) ⁻¹' haarRootCube ι 1) =
      ENNReal.ofReal ((2 : ℝ)^Fintype.card ι) := by
  calc
    _ = volume (haarRootCube ι 1) :=
      (measurePreserving_sub_right volume x).measure_preimage
        (show NullMeasurableSet (haarRootCube ι 1) volume from measurableSet_Icc.nullMeasurableSet)
    _ = _ := by simp

/-- Actual unit-range support and amplitude give a dimension-only Lp response bound for
every exponent. Its observation measure is original volume on the actual original cube. -/
theorem eLpNorm_originalCubeReflectedInputResponse_le
    {η : (ι → ℝ) → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ v, |η v| ≤ M) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (p : ℝ≥0∞) (R : ℝ) (x : ι → ℝ) :
    eLpNorm (fun z ↦ originalCubeReflectedInputResponse η R z x) p
      (volume.restrict (haarRootCube ι R)) ≤
      ENNReal.ofReal (((3 : ℝ)^Fintype.card ι + 1) * M) *
        (ENNReal.ofReal ((2 : ℝ)^Fintype.card ι)) ^ (1 / p.toReal) := by
  let D : ℝ := ((3 : ℝ)^Fintype.card ι + 1) * M
  let C : Set (ι → ℝ) := (fun z ↦ z - x) ⁻¹' haarRootCube ι 1
  have hD : 0 ≤ D := mul_nonneg (by positivity) hM
  have hC : MeasurableSet C := measurableSet_Icc.preimage (measurable_id.sub_const x)
  have hbound : ∀ z : ι → ℝ,
      ‖(haarRootCube ι R).indicator (fun z ↦ originalCubeReflectedInputResponse η R z x) z‖ ≤
        ‖C.indicator (fun _ ↦ D) z‖ := by
    intro z
    by_cases hz : z ∈ haarRootCube ι R
    · rw [indicator_of_mem hz]
      by_cases hc : z ∈ C
      · rw [indicator_of_mem hc, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hD]
        exact abs_originalCubeReflectedInputResponse_le hM hηM R z x
      · rw [indicator_of_notMem hc, norm_zero]
        have hn : 1 ≤ ‖z - x‖ := by
          by_contra! hn
          exact hc ((mem_haarRootCube_iff_norm_le (by norm_num) (z - x)).mpr hn.le)
        rw [originalCubeReflectedInputResponse_eq_zero_of_one_le_norm_sub hηsupport hz hn,
          norm_zero]
    · rw [indicator_of_notMem hz, norm_zero]
      exact norm_nonneg _
  calc
    _ = eLpNorm ((haarRootCube ι R).indicator
        (fun z ↦ originalCubeReflectedInputResponse η R z x)) p volume :=
      (eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc).symm
    _ ≤ eLpNorm (C.indicator (fun _ ↦ D)) p volume := eLpNorm_mono hbound
    _ ≤ _ := by
      have h := eLpNorm_indicator_const_le (μ := volume) (s := C) (c := D) p
      rw [volume_originalInputUnitNeighborhood] at h
      simpa only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg hD] using h

/-- Every literal reflected full-input response has a true finite Lp moment on the actual
cube, internally from original measurable bounded unit-range kernel data. -/
theorem memLp_originalCubeReflectedInputResponse
    {η : (ι → ℝ) → ℝ} (hη : Measurable η) {M : ℝ} (hM : 0 ≤ M)
    (hηM : ∀ v, |η v| ≤ M) (hηsupport : ∀ v, 1 ≤ ‖v‖ → η v = 0)
    (p : ℝ≥0∞) (R : ℝ) (x : ι → ℝ) :
    MemLp (fun z ↦ originalCubeReflectedInputResponse η R z x) p
      (volume.restrict (haarRootCube ι R)) := by
  have hm : Measurable (fun z ↦ originalCubeReflectedInputResponse η R z x) :=
    (measurable_originalCubeReflectedInputResponse hη R).comp
      (measurable_id.prodMk measurable_const)
  refine ⟨hm.aestronglyMeasurable,
    (eLpNorm_originalCubeReflectedInputResponse_le hM hηM hηsupport p R x).trans_lt ?_⟩
  finiteness

end OTSelector.Reconstruction
