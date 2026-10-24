import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Probability.Kernel.Composition.Lemmas
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Tactic

/-!
Conditions: A finite retained pair kernel dominated by an actual Markov pair kernel, with measurable auxiliary retention parameters and a.e. retained masses tending to one where limits are asserted.

Objects: A positive-mass everywhere completion equal to the original retained kernel off its zero-mass labels, preserving its original weighted pair measure exactly and retaining the lost-mass limit.

Proof detail: On a zero-mass retained label use the existing probability kernel and set its retention weight to zero; elsewhere keep the original data. Check the identity by cases, then use eventual positivity from mass convergence.

References: D. H. Fremlin: 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula; D. H. Fremlin: Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
Relation: A measurable zero-weight normalization adapter. It changes only a representation of an unchanged weighted measure and does not insert new positive physical mass at originally null labels.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalRetainedKernelPositiveCompletion.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalRetainedKernelPositiveCompletion`; the selected original proof blocks follow. -/
section

/-! Null retained conditional roots admit a positive normalization factorization
that preserves their weighted ORIGINAL pair measure exactly. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
variable {Z : Type*} [MeasurableSpace Z]

/-- Only a zero retained conditional measure is filled by its unchanged
original pairing; its compensating scalar retention is exactly zero. -/
def originalPositiveRetainedPairKernel (χ γ : Kernel Z (ℝ × ℝ)) : Kernel Z (ℝ × ℝ) := by
  classical
  exact Kernel.piecewise (measurableSet_eq_fun (χ.measurable_coe MeasurableSet.univ)
    (measurable_const (a := (0 : ℝ≥0∞)))) γ χ

/-- Compensation is 1 precisely at an original null retained root, so its
physical retained mass remains zero under positive normalization. -/
def originalPositiveRetention (χ : Kernel Z (ℝ × ℝ)) (η : Z → ℝ) (z : Z) : ℝ :=
  if χ z univ = 0 then 1 else η z

theorem originalPositiveRetainedPairKernel_apply (χ γ : Kernel Z (ℝ × ℝ)) (z : Z) :
    originalPositiveRetainedPairKernel χ γ z = if χ z univ = 0 then γ z else χ z := by
  classical
  rfl

instance originalPositiveRetainedPairKernel_finite
    (χ γ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] [IsMarkovKernel γ] (z : Z) :
    IsFiniteMeasure (originalPositiveRetainedPairKernel χ γ z) := by
  classical
  rw [originalPositiveRetainedPairKernel_apply]
  split_ifs <;> infer_instance

/-- Positive completion is a measurable scalar, chosen on the original population. -/
theorem measurable_originalPositiveRetention (χ : Kernel Z (ℝ × ℝ))
    {η : Z → ℝ} (hη : Measurable η) : Measurable (originalPositiveRetention χ η) :=
  measurable_const.ite (measurableSet_eq_fun (χ.measurable_coe MeasurableSet.univ) measurable_const) hη

/-- Every completed normalization has genuinely positive actual mass. -/
theorem originalPositiveRetainedPairKernel_mass_pos
    (χ γ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] [IsMarkovKernel γ] (z : Z) :
    0 < (originalPositiveRetainedPairKernel χ γ z).real univ := by
  classical
  rw [originalPositiveRetainedPairKernel_apply]
  split_ifs with hz
  · simp only [probReal_univ]; norm_num
  · exact ENNReal.toReal_pos hz (measure_ne_top _ _)

/-- Completion remains below the SAME original conditional pairing. -/
theorem originalPositiveRetainedPairKernel_le
    (χ γ : Kernel Z (ℝ × ℝ)) (z : Z) (hχ : χ z ≤ γ z) :
    originalPositiveRetainedPairKernel χ γ z ≤ γ z := by
  classical
  rw [originalPositiveRetainedPairKernel_apply]
  split_ifs
  · exact le_rfl
  · exact hχ

/-- The entire weighted retained original pair measure is exactly unchanged.
This identity is chosen before samples and does not replace an adaptive remainder. -/
theorem originalPositiveRetention_smul_pairKernel_eq
    (χ γ : Kernel Z (ℝ × ℝ)) (η : Z → ℝ) (z : Z) :
    ENNReal.ofReal (1 - originalPositiveRetention χ η z) •
      originalPositiveRetainedPairKernel χ γ z = ENNReal.ofReal (1 - η z) • χ z := by
  classical
  rw [originalPositiveRetainedPairKernel_apply]
  by_cases hz : χ z univ = 0
  · have hzero : χ z = 0 := Measure.measure_univ_eq_zero.mp hz
    have he : originalPositiveRetention χ η z = 1 := by
      simp only [originalPositiveRetention,hz,ite_true]
    rw [he,sub_self,ENNReal.ofReal_zero,zero_smul,hzero,smul_zero]
  · simp only [originalPositiveRetention,hz,ite_false]

/-- Retained mass approaching the full original mass makes completion and
scalar compensation equal the original inputs eventually at each original root. -/
theorem eventually_originalPositiveRetainedPairKernel_eq
    (χ : ℕ → Kernel Z (ℝ × ℝ)) (γ : Kernel Z (ℝ × ℝ)) (η : ℕ → Z → ℝ) (z : Z)
    (hmass : Tendsto (fun n ↦ (χ n z).real univ) atTop (𝓝 1)) :
    ∀ᶠ n in atTop, originalPositiveRetainedPairKernel (χ n) γ z = χ n z ∧
      originalPositiveRetention (χ n) (η n) z = η n z := by
  filter_upwards [(tendsto_order.mp hmass).1 (0:ℝ) (by norm_num)] with n hn
  have hn0 : χ n z univ ≠ 0 := (ENNReal.toReal_pos_iff.mp hn).1.ne'
  simp only [originalPositiveRetainedPairKernel_apply,originalPositiveRetention,hn0,ite_false,and_self]

/-- The canonical completed lost-mass rate is in [0,1), tends to zero, and
satisfies exactly the existing retained-pressure factory's mass requirement.
The original retained conditional law may have zero mass at arbitrary early stages. -/
theorem ae_originalPositiveRetainedPairKernel_lost_mass_law
    (lambda : Measure Z) (χ : ℕ → Kernel Z (ℝ × ℝ))
    [∀ n z, IsFiniteMeasure (χ n z)] (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
    (hχ : ∀ᵐ z ∂lambda, ∀ n, χ n z ≤ γ z)
    (hmass : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ (χ n z).real univ) atTop (𝓝 1)) :
    ∀ᵐ z ∂lambda,
      (∀ n, originalPositiveRetainedPairKernel (χ n) γ z ≤ γ z) ∧
      Tendsto (fun n ↦ 1 - (originalPositiveRetainedPairKernel (χ n) γ z).real univ)
        atTop (𝓝 0) ∧
      ∀ n, 0 ≤ 1 - (originalPositiveRetainedPairKernel (χ n) γ z).real univ ∧
        1 - (originalPositiveRetainedPairKernel (χ n) γ z).real univ < 1 ∧
        1 - (1 - (originalPositiveRetainedPairKernel (χ n) γ z).real univ) ≤
          (originalPositiveRetainedPairKernel (χ n) γ z).real univ := by
  filter_upwards [hχ,hmass] with z hχz hmassz
  have heq := eventually_originalPositiveRetainedPairKernel_eq χ γ (fun _ _ ↦ 0) z hmassz
  have hmass' : Tendsto (fun n ↦ (originalPositiveRetainedPairKernel (χ n) γ z).real univ)
      atTop (𝓝 1) := hmassz.congr' (heq.mono fun n h ↦ by
        change (χ n z).real univ = (originalPositiveRetainedPairKernel (χ n) γ z).real univ
        rw [h.1])
  have hδ : Tendsto (fun n ↦ 1 - (originalPositiveRetainedPairKernel (χ n) γ z).real univ)
      atTop (𝓝 0) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (1:ℝ)) atTop (𝓝 1)).sub hmass'
    simpa only [sub_self] using hh
  refine ⟨fun n ↦ originalPositiveRetainedPairKernel_le (χ n) γ z (hχz n),hδ,?_⟩
  intro n
  have hpos := originalPositiveRetainedPairKernel_mass_pos (χ n) γ z
  have hle : (originalPositiveRetainedPairKernel (χ n) γ z).real univ ≤ 1 := by
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using
      ENNReal.toReal_mono (measure_ne_top (γ z) univ)
        (originalPositiveRetainedPairKernel_le (χ n) γ z (hχz n) univ)
  exact ⟨by linarith only [hle],by linarith only [hpos],by linarith⟩

end OTSelector.Reconstruction

end
end
