import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.RadonNikodym
import OTSelector.MeasureTheory.FiniteMeasureNormalizationVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalRetainedLawVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalRetainedLawVariation`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.RetainedLawVariation

## Lemma skeleton

* **Conditions:** A finite submeasure of an original probability law, with lost mass bounded by delta<1, eventually delta tending to zero for convergence.
* **Objects:** Exact variation of the lost positive measure, normalized retained-law variation and convergence of retained mass.
* **Proof detail:** Identify signed variation of a positive difference, split normalization from removal and bound the inverse retained mass by 1/(1-delta); squeeze as delta tends to zero.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=275): Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27): Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40.

Source relation (composition): Submeasure normalization estimates with full variation and the explicit coarse 2 delta/(1-delta) bound.
-/

/-! Actual retained sublaws approach their original probability law as their
recorded original lost mass tends to zero. No positive pointwise density
bound is used. -/
open Set Function MeasureTheory Filter
open scoped ENNReal NNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The signed variation of removing an actual submeasure is exactly its
original residual measure. -/
theorem totalVariation_submeasure_difference {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hle : ν ≤ μ) :
    (ν.toSignedMeasure - μ.toSignedMeasure).totalVariation = μ - ν := by
  rw [SignedMeasure.totalVariation,Measure.toJordanDecomposition_toSignedMeasure_sub]
  change (ν - μ) + (μ - ν) = μ - ν
  rw [Measure.sub_eq_zero_of_le hle,zero_add]

/-- A probability law is unchanged by normalization by its own actual mass. -/
theorem normalizedFiniteLaw_eq_self_of_probability {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] : normalizedFiniteLaw μ = μ := by
  simp only [normalizedFiniteLaw,probReal_univ,inv_one,Real.toNNReal_one,one_smul]

/-- The original lost-mass budget controls the normalized retained law in
variation, even if the original density vanishes on a nontrivial set. -/
theorem totalVariation_normalized_submeasure_le_of_mass
    {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsFiniteMeasure ν]
    (hle : ν ≤ μ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ < 1)
    (hmass : 1 - δ ≤ ν.real univ) :
    ((normalizedFiniteLaw ν).toSignedMeasure - μ.toSignedMeasure).totalVariation.real univ ≤
      2 * δ / (1 - δ) := by
  have hm : ν.real univ ≤ 1 := by
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using
      ENNReal.toReal_mono (measure_ne_top μ univ) (hle univ)
  have hp : 0 < ν.real univ := (sub_pos.mpr hδ1).trans_le hmass
  have hraw : (ν.toSignedMeasure - μ.toSignedMeasure).totalVariation.real univ = 1 - ν.real univ := by
    rw [totalVariation_submeasure_difference μ ν hle,measureReal_def,
      Measure.sub_apply MeasurableSet.univ hle,
      ENNReal.toReal_sub_of_le (hle univ) (measure_ne_top μ univ)]
    simp only [measure_univ,ENNReal.toReal_one,measureReal_def]
  have hb := totalVariation_normalizedFiniteLaw_le ν μ hp (by simp)
  simp only [normalizedFiniteLaw_eq_self_of_probability μ,hraw,probReal_univ,
    abs_of_nonpos (sub_nonpos.mpr hm)] at hb
  apply hb.trans
  calc
    _ ≤ (2 * δ) / ν.real univ := by
      apply div_le_div_of_nonneg_right _ hp.le
      linarith
    _ ≤ (2 * δ) / (1 - δ) := div_le_div_of_nonneg_left
      (mul_nonneg (by norm_num) hδ) (sub_pos.mpr hδ1) hmass


/-- Any family of actual retained sublaws converges in variation to the
unchanged original law when its recorded original lost masses vanish. The
retained sets, masks, and conditional densities may vary with the index. -/
theorem tendsto_totalVariation_normalized_submeasure_of_mass
    {X J : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : J → Measure X) [∀ j, IsFiniteMeasure (ν j)]
    (l : Filter J) (δ : J → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hdata : ∀ᶠ j in l, ν j ≤ μ ∧ 0 ≤ δ j ∧ δ j < 1 ∧ 1 - δ j ≤ (ν j).real univ) :
    Tendsto (fun j ↦ ((normalizedFiniteLaw (ν j)).toSignedMeasure -
      μ.toSignedMeasure).totalVariation.real univ) l (𝓝 0) := by
  have hb : Tendsto (fun j ↦ 2 * δ j / (1 - δ j)) l (𝓝 0) := by
    have hh := (hδ.const_mul 2).div (tendsto_const_nhds.sub hδ) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    change Tendsto (fun j ↦ 2 * δ j / (1 - δ j)) l (𝓝 ((2 : ℝ) * 0 / (1 - 0))) at hh
    simpa only [mul_zero,sub_zero,zero_div] using hh
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ ↦ measureReal_nonneg) _ hb
  filter_upwards [hdata] with j hj
  exact totalVariation_normalized_submeasure_le_of_mass μ (ν j) hj.1 hj.2.1 hj.2.2.1 hj.2.2.2


/-- The raw retained masses recover the full original probability mass as the
recorded original losses vanish. This uses no pointwise density lower bound. -/
theorem tendsto_submeasure_mass_of_lost_mass
    {X J : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : J → Measure X) [∀ j, IsFiniteMeasure (ν j)]
    (l : Filter J) (δ : J → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hdata : ∀ᶠ j in l, ν j ≤ μ ∧ 1 - δ j ≤ (ν j).real univ) :
    Tendsto (fun j ↦ (ν j).real univ) l (𝓝 1) := by
  have hlo : Tendsto (fun j ↦ 1 - δ j) l (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds.sub hδ :
      Tendsto (fun j ↦ (1 : ℝ) - δ j) l (𝓝 (1 - 0)))
  apply hlo.squeeze' tendsto_const_nhds (hdata.mono fun _ hj ↦ hj.2)
  filter_upwards [hdata] with j hj
  simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using
    ENNReal.toReal_mono (measure_ne_top μ univ) (hj.1 univ)

end OTSelector.Reconstruction

end
end
