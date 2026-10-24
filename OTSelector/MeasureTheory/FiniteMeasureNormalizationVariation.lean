import Mathlib.MeasureTheory.Measure.SubFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Variation.SignedMeasure
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** Finite laws, positive masses when normalized, and explicit relative mass/variation bounds.
* **Objects:** Normalized laws, their common submeasure and residual masses.
* **Proof detail:** Use Jordan/variation bounds and the triangle inequality; divide by positive mass and track constants.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 9A, Theorems 9.9–9.10, pp. 259–261 (total variation and density formula).
  https://measure.axler.net/MIRA.pdf#page=275
* D. H. Fremlin, *Measure Theory, Volume 2*, Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure.
  https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf

**Relationship to the sources:** The constants 3*eta/(1-eta), commonFiniteLaw encoding and freezing-bound structure are locally derived estimates, not attributed as textbook constants.
-/

/-!
# Normalization and common parts of finite laws

The two original laws retain their masses. Normalization is used only for
positive masses, and the common submeasure records the actual removable mass.
-/

open Set MeasureTheory
open scoped ENNReal

namespace OTSelector.Reconstruction

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Normalize a finite measure by its actual mass, with zero as the null fallback. -/
def normalizedFiniteLaw (μ : Measure X) : Measure X :=
  (μ.real univ)⁻¹.toNNReal • μ

instance (μ : Measure X) [IsFiniteMeasure μ] : IsFiniteMeasure (normalizedFiniteLaw μ) := by
  unfold normalizedFiniteLaw
  infer_instance

/-- A nonzero finite law normalizes to a probability law. -/
theorem normalizedFiniteLaw_probability (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : 0 < μ.real univ) : IsProbabilityMeasure (normalizedFiniteLaw μ) := by
  constructor
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) ENNReal.one_ne_top).mp
  change (normalizedFiniteLaw μ).real univ = 1
  rw [normalizedFiniteLaw, measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ (inv_nonneg.mpr hμ.le)]
  exact inv_mul_cancel₀ hμ.ne'

private theorem totalVariation_toSignedMeasure (μ : Measure X) [IsFiniteMeasure μ] :
    μ.toSignedMeasure.totalVariation = μ := by
  have h := Measure.toJordanDecomposition_toSignedMeasure_sub (μ := μ) (ν := 0)
  simp only [Measure.toSignedMeasure_zero, sub_zero] at h
  simp only [SignedMeasure.totalVariation, h,
    Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
    Measure.jordanDecompositionOfToSignedMeasureSub_negPart, Measure.sub_zero,
    Measure.zero_sub, add_zero]

private theorem totalVariation_add_le (s t : SignedMeasure X) :
    (s + t).totalVariation univ ≤ s.totalVariation univ + t.totalVariation univ := by
  simp only [SignedMeasure.totalVariation_eq_variation]
  exact VectorMeasure.variation_add_le univ

private theorem totalVariation_smul_real (s : SignedMeasure X) (c : ℝ) :
    (c • s).totalVariation.real univ = |c| * s.totalVariation.real univ := by
  simp only [SignedMeasure.totalVariation_eq_variation, VectorMeasure.variation_smul,
    measureReal_nnreal_smul_apply, coe_nnnorm, Real.norm_eq_abs]

/-- Normalization amplifies the raw variation and mass discrepancy only by the
inverse original mass. The frozen law may have a different mass. -/
theorem totalVariation_normalizedFiniteLaw_le (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : 0 < μ.real univ) (hν : 0 < ν.real univ) :
    ((normalizedFiniteLaw μ).toSignedMeasure -
      (normalizedFiniteLaw ν).toSignedMeasure).totalVariation.real univ ≤
      ((μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ +
        |μ.real univ - ν.real univ|) / μ.real univ := by
  let m := μ.real univ
  let n := ν.real univ
  have heq : (normalizedFiniteLaw μ).toSignedMeasure -
      (normalizedFiniteLaw ν).toSignedMeasure =
      m⁻¹ • (μ.toSignedMeasure - ν.toSignedMeasure) +
        (m⁻¹ - n⁻¹) • ν.toSignedMeasure := by
    simp only [normalizedFiniteLaw, Measure.toSignedMeasure_smul, NNReal.smul_def,
      Real.coe_toNNReal _ (inv_nonneg.mpr hμ.le),
      Real.coe_toNNReal _ (inv_nonneg.mpr hν.le), m, n]
    module
  rw [heq]
  have hb := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
      ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
    (totalVariation_add_le
      (m⁻¹ • (μ.toSignedMeasure - ν.toSignedMeasure))
      ((m⁻¹ - n⁻¹) • ν.toSignedMeasure))
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at hb
  change _ ≤ _ at hb
  rw [← measureReal_def, ← measureReal_def, ← measureReal_def,
    totalVariation_smul_real, totalVariation_smul_real,
    totalVariation_toSignedMeasure] at hb
  have hmn : |m⁻¹ - n⁻¹| * n = |m - n| / m := by
    have hm : 0 < m := hμ
    have hn : 0 < n := hν
    rw [inv_sub_inv hm.ne' hn.ne', abs_div, abs_mul, abs_of_pos hm, abs_of_pos hn,
      abs_sub_comm]
    field_simp
  rw [abs_inv, abs_of_pos hμ, hmn] at hb
  calc
    _ ≤ m⁻¹ * (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ +
        |m - n| / m := hb
    _ = _ := by dsimp [m, n]; ring

/-- Relative mass and raw variation estimates give an explicit probability-law
error, tending to zero with the original cell oscillation. -/
theorem totalVariation_normalizedFiniteLaw_le_of_relative (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {η : ℝ}
    (hη : 0 ≤ η) (hη1 : η < 1) (hν : 0 < ν.real univ)
    (hmass : |μ.real univ - ν.real univ| ≤ η * ν.real univ)
    (hvariation : (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ ≤
      2 * η * ν.real univ) :
    0 < μ.real univ ∧
      ((normalizedFiniteLaw μ).toSignedMeasure -
        (normalizedFiniteLaw ν).toSignedMeasure).totalVariation.real univ ≤
        3 * η / (1 - η) := by
  have hlo : (1 - η) * ν.real univ ≤ μ.real univ := by
    have := (abs_le.mp hmass).1
    linarith
  have hp : 0 < (1 - η) * ν.real univ := mul_pos (sub_pos.mpr hη1) hν
  have hμ := hp.trans_le hlo
  refine ⟨hμ, (totalVariation_normalizedFiniteLaw_le μ ν hμ hν).trans ?_⟩
  calc
    _ ≤ (3 * η * ν.real univ) / μ.real univ := by
      gcongr
      linarith
    _ ≤ (3 * η * ν.real univ) / ((1 - η) * ν.real univ) := by
      exact div_le_div_of_nonneg_left (by positivity) hp hlo
    _ = _ := by field_simp

/-- The common part is retained as an actual measure, rather than discarding a
probability discrepancy without recording the lost mass. -/
def commonFiniteLaw (μ ν : Measure X) : Measure X := μ - (μ - ν)

theorem commonFiniteLaw_le_left (μ ν : Measure X) : commonFiniteLaw μ ν ≤ μ :=
  Measure.sub_le

theorem commonFiniteLaw_le_right (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : commonFiniteLaw μ ν ≤ ν := by
  apply Measure.sub_le_iff_le_add.mpr
  rw [add_comm]
  exact Measure.sub_le_iff_le_add.mp (le_refl (μ - ν))

instance (μ ν : Measure X) [IsFiniteMeasure μ] : IsFiniteMeasure (commonFiniteLaw μ ν) :=
  Measure.isFiniteMeasure_sub

/-- Both residual laws have total mass bounded by the full raw variation. -/
theorem commonFiniteLaw_residual_bounds (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    μ - commonFiniteLaw μ ν = μ - ν ∧
      ν - commonFiniteLaw μ ν = ν - μ ∧
      (μ - commonFiniteLaw μ ν) univ ≤
        (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ∧
      (ν - commonFiniteLaw μ ν) univ ≤
        (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ := by
  let θ := commonFiniteLaw μ ν
  have hμ : θ + (μ - ν) = μ := by
    exact Measure.sub_add_cancel_of_le (μ := μ) (ν := μ - ν) Measure.sub_le
  have hν : θ + (ν - μ) = ν := by
    apply Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp
    have hs := Measure.sub_toSignedMeasure_eq_toSignedMeasure_sub (μ := μ) (ν := ν)
    have ht := Measure.toSignedMeasure_congr hμ
    rw [Measure.toSignedMeasure_add] at ht ⊢
    rw [← ht] at hs
    apply add_left_cancel (a := (μ - ν).toSignedMeasure)
    simpa only [add_assoc, add_left_comm, add_comm] using
      sub_eq_sub_iff_add_eq_add.mp hs
  have heμ : μ - θ = μ - ν := by
    calc
      μ - θ = (θ + (μ - ν)) - θ := congrArg (fun ξ ↦ ξ - θ) hμ.symm
      _ = μ - ν := by rw [add_comm, Measure.add_sub_cancel]
  have heν : ν - θ = ν - μ := by
    calc
      ν - θ = (θ + (ν - μ)) - θ := congrArg (fun ξ ↦ ξ - θ) hν.symm
      _ = ν - μ := by rw [add_comm, Measure.add_sub_cancel]
  have hTV : (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation =
      (μ - ν) + (ν - μ) := by
    rw [SignedMeasure.totalVariation, Measure.toJordanDecomposition_toSignedMeasure_sub]
    rfl
  refine ⟨heμ, heν, ?_, ?_⟩
  · rw [heμ, hTV, Measure.add_apply]
    exact le_self_add
  · rw [heν, hTV, Measure.add_apply]
    exact le_add_self

/-- The two residual probability laws have exactly the same mass. -/
theorem commonFiniteLaw_probability_residual_mass (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (μ - commonFiniteLaw μ ν) univ = (ν - commonFiniteLaw μ ν) univ := by
  rw [Measure.sub_apply MeasurableSet.univ (commonFiniteLaw_le_left μ ν),
    Measure.sub_apply MeasurableSet.univ (commonFiniteLaw_le_right μ ν)]
  simp only [measure_univ]

/-- Raw intensity and mark freezing data with both original masses retained. -/
structure FiniteLawFreezingBound (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (η : ℝ) : Prop where
  mass_error : |μ.real univ - ν.real univ| ≤ η * ν.real univ
  variation : (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation.real univ ≤
    2 * η * ν.real univ

namespace FiniteLawFreezingBound

variable {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {η : ℝ}

/-- The original mass is between the two relative perturbations of frozen mass. -/
theorem mass_bounds (D : FiniteLawFreezingBound μ ν η) :
    (1 - η) * ν.real univ ≤ μ.real univ ∧
      μ.real univ ≤ (1 + η) * ν.real univ := by
  obtain ⟨hl, hu⟩ := abs_le.mp D.mass_error
  constructor <;> linarith

/-- The unnormalized laws also retain a common submeasure; each actual leftover
has its original mass bounded by the raw variation estimate. -/
theorem raw_common_part (D : FiniteLawFreezingBound μ ν η) :
    ∃ θ : Measure X, θ ≤ μ ∧ θ ≤ ν ∧
      (μ - θ) univ ≤ ENNReal.ofReal (2 * η * ν.real univ) ∧
      (ν - θ) univ ≤ ENNReal.ofReal (2 * η * ν.real univ) := by
  have he := ENNReal.ofReal_toReal
    (measure_ne_top (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ)
  have hb : (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation univ ≤
      ENNReal.ofReal (2 * η * ν.real univ) := he ▸ ENNReal.ofReal_le_ofReal D.variation
  obtain ⟨_, _, hμ, hν⟩ := commonFiniteLaw_residual_bounds μ ν
  exact ⟨commonFiniteLaw μ ν, commonFiniteLaw_le_left μ ν,
    commonFiniteLaw_le_right μ ν, hμ.trans hb, hν.trans hb⟩

/-- A tolerance smaller than one makes a cell null for both raw laws at once. -/
theorem zero_iff (D : FiniteLawFreezingBound μ ν η) (hη1 : η < 1) : μ = 0 ↔ ν = 0 := by
  have hμ0 : μ = 0 ↔ μ.real univ = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)]
    exact Measure.measure_univ_eq_zero.symm
  have hν0 : ν = 0 ↔ ν.real univ = 0 := by
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff, or_iff_left (measure_ne_top _ _)]
    exact Measure.measure_univ_eq_zero.symm
  rw [hμ0, hν0]
  constructor
  · intro h
    have hd := D.mass_error
    rw [h, zero_sub, abs_neg, abs_of_nonneg measureReal_nonneg] at hd
    nlinarith [measureReal_nonneg (μ := ν) (s := univ)]
  · intro h
    have hd := D.mass_error
    rw [h, sub_zero, mul_zero, abs_of_nonneg measureReal_nonneg] at hd
    exact le_antisymm hd measureReal_nonneg

/-- The actual and frozen probability laws have error at most `3η/(1-η)`. -/
theorem normalized_variation (D : FiniteLawFreezingBound μ ν η)
    (hη : 0 ≤ η) (hη1 : η < 1) (hν : 0 < ν.real univ) :
    0 < μ.real univ ∧
      ((normalizedFiniteLaw μ).toSignedMeasure -
        (normalizedFiniteLaw ν).toSignedMeasure).totalVariation.real univ ≤
        3 * η / (1 - η) :=
  totalVariation_normalizedFiniteLaw_le_of_relative μ ν hη hη1 hν D.mass_error D.variation

/-- A real common probability submeasure leaves equal residual masses bounded by
the explicit normalization error. The original raw masses are not identified. -/
theorem normalized_common_part (D : FiniteLawFreezingBound μ ν η)
    (hη : 0 ≤ η) (hη1 : η < 1) (hν : 0 < ν.real univ) :
    ∃ θ : Measure X, θ ≤ normalizedFiniteLaw μ ∧ θ ≤ normalizedFiniteLaw ν ∧
      (normalizedFiniteLaw μ - θ) univ = (normalizedFiniteLaw ν - θ) univ ∧
      (normalizedFiniteLaw μ - θ) univ ≤ ENNReal.ofReal (3 * η / (1 - η)) := by
  have hv := D.normalized_variation hη hη1 hν
  let _instActual := normalizedFiniteLaw_probability μ hv.1
  let _instFrozen := normalizedFiniteLaw_probability ν hν
  refine ⟨commonFiniteLaw (normalizedFiniteLaw μ) (normalizedFiniteLaw ν),
    commonFiniteLaw_le_left _ _, commonFiniteLaw_le_right _ _,
    commonFiniteLaw_probability_residual_mass _ _, ?_⟩
  refine (commonFiniteLaw_residual_bounds _ _).2.2.1.trans ?_
  have he := ENNReal.ofReal_toReal (measure_ne_top
    ((normalizedFiniteLaw μ).toSignedMeasure -
      (normalizedFiniteLaw ν).toSignedMeasure).totalVariation univ)
  exact he ▸ ENNReal.ofReal_le_ofReal hv.2

end FiniteLawFreezingBound

end
end OTSelector.Reconstruction
