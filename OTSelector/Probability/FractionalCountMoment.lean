import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Fractional Count Moment

Conditions: A measurable natural-number count whose real cast is integrable and 0<r<1; for the retained version a measurable natural-number count bounded by the original.

Objects: Fractional-power integrability and E[N^r]≤(EN)^r, also for the dominated retained count.

Proof detail: Prove fractional-power integrability, apply Jensen for the concave power and use pointwise domination for retention.

Relation to primary sources: A direct Jensen specialization with the integrability proof included; no distributional or independence premise is needed.

References:
* Rick Durrett, Probability: Theory and Examples, fifth edition, author version 11 January 2019, Section 1.6.1, Theorem 1.6.2, p. 29. https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37
-/
/-! Genuine fractional moments of measurable original natural-number counts. -/

open MeasureTheory Set Filter

noncomputable section
namespace OTSelector.Reconstruction

/-- A real fractional count moment is integrable and satisfies Jensen's bound.
Its integrability and the concavity input are proved internally, including zero counts. -/
theorem count_rpow_integrable_and_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω) [IsProbabilityMeasure M]
    (N : Ω → ℕ) (hN : Measurable N) (hNI : Integrable (fun ω ↦ (N ω : ℝ)) M)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Integrable (fun ω ↦ (N ω : ℝ) ^ r) M ∧
      (∫ ω, (N ω : ℝ) ^ r ∂M) ≤ (∫ ω, (N ω : ℝ) ∂M) ^ r := by
  have hm : Measurable (fun ω ↦ (N ω : ℝ) ^ r) :=
    (Real.continuous_rpow_const hr₀.le).measurable.comp (measurable_from_nat.comp hN)
  have hb (ω : Ω) : (N ω : ℝ) ^ r ≤ (N ω : ℝ) := by
    by_cases hz : N ω = 0
    · simp [hz, Real.zero_rpow hr₀.ne']
    · exact Real.rpow_le_self_of_one_le
        (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hz) hr₁.le
  have hi : Integrable (fun ω ↦ (N ω : ℝ) ^ r) M :=
    hNI.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact hb ω)
  exact ⟨hi, (Real.concaveOn_rpow hr₀.le hr₁.le).le_map_integral (f := fun ω ↦ (N ω : ℝ))
    (Real.continuous_rpow_const hr₀.le).continuousOn isClosed_Ici
    (Eventually.of_forall fun ω ↦ show (0 : ℝ) ≤ (N ω : ℝ) from Nat.cast_nonneg _) hNI hi⟩

/-- A genuinely smaller original retained count obeys the same true fractional
moment bound; no integrability or moment estimate for the retained count is assumed. -/
theorem retainedCount_rpow_integrable_and_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (M : Measure Ω) [IsProbabilityMeasure M]
    (N K : Ω → ℕ) (hN : Measurable N) (hK : Measurable K)
    (hNI : Integrable (fun ω ↦ (N ω : ℝ)) M) (hle : ∀ ω, K ω ≤ N ω)
    {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    Integrable (fun ω ↦ (K ω : ℝ) ^ r) M ∧
      (∫ ω, (K ω : ℝ) ^ r ∂M) ≤ (∫ ω, (N ω : ℝ) ∂M) ^ r := by
  have h := count_rpow_integrable_and_integral_le M N hN hNI hr₀ hr₁
  have hm : Measurable (fun ω ↦ (K ω : ℝ) ^ r) :=
    (Real.continuous_rpow_const hr₀.le).measurable.comp (measurable_from_nat.comp hK)
  have hb (ω : Ω) : (K ω : ℝ) ^ r ≤ (N ω : ℝ) ^ r :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hle ω) hr₀.le
  have hi : Integrable (fun ω ↦ (K ω : ℝ) ^ r) M :=
    h.1.mono' hm.aestronglyMeasurable (Eventually.of_forall fun ω ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
      exact hb ω)
  exact ⟨hi, (integral_mono hi h.1 hb).trans h.2⟩

end OTSelector.Reconstruction
