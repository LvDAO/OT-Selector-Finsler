import Mathlib.MeasureTheory.Function.L2Space
import OTSelector.MeasureTheory.Lp.SummableSeries
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.TrafficSecondMomentLtwoNorm.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.TrafficSecondMomentLtwoNorm`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.SecondMomentNorm

## Lemma skeleton

* **Conditions:** Square-integrable real readouts with actual second-moment bounds; the countable version assumes summability of their square-root bounds.
* **Objects:** L2 norm bounds, good/bad L2 assembly and almost-everywhere absolutely convergent traffic sums.
* **Proof detail:** Use the L2 norm-square identity, split by the good/bad indicator and apply Minkowski; use summable L2 norms for the countable sum.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=233): Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=219): Section 7B, Theorem 7.20 and proof, pp. 204–205; Theorem 7.24, p. 205.

Source relation (composition): Second-moment adapters and series assembly, without independence between events or levels.
-/

/-! Converting the actual Campbell mean-square bounds into the L2 norms consumed
by countable traffic summation. No independence between the level events is used. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- A real traffic's actual mean-square bound gives its square-root L2 bound. -/
theorem eLpNorm_two_le_sqrt_of_integral_sq_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Ω → ℝ}
    (hT : MemLp T 2 P) {V : ℝ} (hbound : (∫ s, T s ^ 2 ∂P) ≤ V) :
    eLpNorm T 2 P ≤ ENNReal.ofReal (Real.sqrt V) := by
  calc
    _ = ENNReal.ofReal (Real.sqrt (∫ s, T s ^ 2 ∂P)) := by
      rw [hT.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs, sq_abs,
        Real.sqrt_eq_rpow, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hbound)

/-- Bounds on the actual good and bad contributions combine for the same traffic
and the same scene event. Arbitrary event/count dependence is retained. -/
theorem memLp_two_and_norm_le_of_good_bad_second_moments
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {T : Ω → ℝ}
    (hT : AEStronglyMeasurable T P) {A : Set Ω} (hA : MeasurableSet A)
    (hgood : Integrable (fun s ↦ (Aᶜ.indicator T s) ^ 2) P)
    (hbad : Integrable (fun s ↦ (A.indicator T s) ^ 2) P)
    {Vgood Vbad : ℝ}
    (hgoodBound : (∫ s, (Aᶜ.indicator T s) ^ 2 ∂P) ≤ Vgood)
    (hbadBound : (∫ s, (A.indicator T s) ^ 2 ∂P) ≤ Vbad) :
    MemLp T 2 P ∧ eLpNorm T 2 P ≤
      ENNReal.ofReal (Real.sqrt Vgood + Real.sqrt Vbad) := by
  have hg := (memLp_two_iff_integrable_sq (hT.indicator hA.compl)).mpr hgood
  have hb := (memLp_two_iff_integrable_sq (hT.indicator hA)).mpr hbad
  have heq : T = Aᶜ.indicator T + A.indicator T := by
    funext s
    by_cases hs : s ∈ A <;> simp [hs]
  refine ⟨by rw [heq]; exact hg.add hb, ?_⟩
  calc
    eLpNorm T 2 P = eLpNorm (Aᶜ.indicator T + A.indicator T) 2 P := congrArg (fun f ↦ eLpNorm f 2 P) heq
    _ ≤ eLpNorm (Aᶜ.indicator T) 2 P + eLpNorm (A.indicator T) 2 P :=
      eLpNorm_add_le hg.aestronglyMeasurable hb.aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (Real.sqrt Vgood) + ENNReal.ofReal (Real.sqrt Vbad) :=
      add_le_add (eLpNorm_two_le_sqrt_of_integral_sq_le hg hgoodBound)
        (eLpNorm_two_le_sqrt_of_integral_sq_le hb hbadBound)
    _ = _ := (ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).symm

/-- Summable square roots of the actual levelwise mean-square bounds produce
the literal traffic sum in L2 and almost-sure absolute convergence. -/
theorem memLp_tsum_of_summable_second_moment_bounds
    {Ω I : Type*} [MeasurableSpace Ω] [Countable I]
    (P : Measure Ω) (T : I → Ω → ℝ)
    (hT : ∀ i, AEStronglyMeasurable (T i) P)
    (hI : ∀ i, Integrable (fun s ↦ T i s ^ 2) P)
    (V : I → ℝ) (hsum : Summable (fun i ↦ Real.sqrt (V i)))
    (hbound : ∀ i, (∫ s, T i s ^ 2 ∂P) ≤ V i) :
    MemLp (fun s ↦ ∑' i, T i s) 2 P ∧
      (eLpNorm (fun s ↦ ∑' i, T i s) 2 P).toReal ≤ ∑' i, Real.sqrt (V i) ∧
      ∀ᵐ s ∂P, Summable (fun i ↦ ‖T i s‖) := by
  apply memLp_tsum_of_summable_level_bound P T
    (fun i ↦ (memLp_two_iff_integrable_sq (hT i)).mpr (hI i))
    (fun i ↦ Real.sqrt (V i)) hsum (fun _ ↦ Real.sqrt_nonneg _)
  intro i
  exact eLpNorm_two_le_sqrt_of_integral_sq_le
    ((memLp_two_iff_integrable_sq (hT i)).mpr (hI i)) (hbound i)

end OTSelector.Probability

end
end
