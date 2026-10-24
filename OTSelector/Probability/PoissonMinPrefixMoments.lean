import OTSelector.Probability.FractionalCountMoment
import OTSelector.Probability.PoissonCountDiscrepancy

/-!
Conditions: A natural q>4, finite nonnegative Poisson rate and natural prefix parameter K, under the genuine independent two-count product law.

Objects: Integrable fractional moment of the minimum count bounded by a^(1−2/q), square-root min-prefix moment≤sqrt(2aK), and pair discrepancy≤sqrt(2a).

Proof detail: Dominate the minimum by one Poisson count and apply concave-power/Jensen moment bounds; treat the zero-intensity case directly and combine the true pair discrepancy.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.2, p. 29.
Relation: A local combination of standard Poisson mean and concavity bounds, retaining the actual independent product law and the explicit dimensional exponent range.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonCounts.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalPressureOrientedShapeHolePoissonCounts`; the selected original proof blocks follow. -/
section

/-! True independent Poisson min-prefix moments, including zero intensity. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Independent actual counts have the fractional, square-root and discrepancy
bounds used after conditioning the two original cloud prefixes. -/
theorem originalShapeHolePoisson_count_moments {q : ℕ} (hq : 4 < q) (a : ℝ≥0) (K : ℕ) :
    let P := (poissonMeasure a).prod (poissonMeasure a)
    Integrable (fun z : ℕ × ℕ ↦ ((min z.1 z.2 : ℕ) : ℝ)^(1-2/(q : ℝ))) P ∧
    (∫ z : ℕ × ℕ, ((min z.1 z.2 : ℕ) : ℝ)^(1-2/(q : ℝ)) ∂P) ≤ (a : ℝ)^(1-2/(q : ℝ)) ∧
    Integrable (fun z : ℕ × ℕ ↦ Real.sqrt (2*((min z.1 z.2 : ℕ) : ℝ)*K)) P ∧
    (∫ z : ℕ × ℕ, Real.sqrt (2*((min z.1 z.2 : ℕ) : ℝ)*K) ∂P) ≤ Real.sqrt (2*(a : ℝ)*K) ∧
    Integrable (fun z : ℕ × ℕ ↦ |(z.1 : ℝ)-z.2|) P ∧
    (∫ z : ℕ × ℕ, |(z.1 : ℝ)-z.2| ∂P) ≤ Real.sqrt (2*(a : ℝ)) := by
  let P := (poissonMeasure a).prod (poissonMeasure a)
  have hN : Integrable (fun z : ℕ × ℕ ↦ (z.1 : ℝ)) P := (integrable_id_poissonMeasure a).comp_fst _
  have hmean : (∫ z : ℕ × ℕ, (z.1 : ℝ) ∂P) = (a : ℝ) := by
    simp only [P,integral_fun_fst,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul,integral_id_poissonMeasure]
  have hqR : (2 : ℝ) < q := by exact_mod_cast (lt_trans (by norm_num : (2 : ℕ) < 4) hq)
  have hp₀ : 0 < 1-2/(q : ℝ) := by rw [sub_pos,div_lt_one (by linarith : (0 : ℝ) < q)]; exact hqR
  have hp₁ : 1-2/(q : ℝ) < 1 := by
    have hh : 0 < 2/(q : ℝ) := by positivity
    linarith
  have hp := retainedCount_rpow_integrable_and_integral_le P Prod.fst (fun z ↦ min z.1 z.2)
    measurable_fst (measurable_fst.min measurable_snd) hN (fun z ↦ min_le_left _ _) hp₀ hp₁
  rw [hmean] at hp
  have hs := retainedCount_rpow_integrable_and_integral_le P Prod.fst (fun z ↦ min z.1 z.2)
    measurable_fst (measurable_fst.min measurable_snd) hN (fun z ↦ min_le_left _ _)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1:ℝ)/2 < 1)
  rw [hmean] at hs
  have hroot (x : ℝ) : Real.sqrt (2*x*K) = Real.sqrt (2*(K : ℝ))*x^((1:ℝ)/2) := by
    rw [← Real.sqrt_eq_rpow,← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2*(K : ℝ))]
    congr 1
    ring
  have hrootI : Integrable (fun z : ℕ × ℕ ↦ Real.sqrt (2*((min z.1 z.2 : ℕ) : ℝ)*K)) P := by
    simp_rw [hroot]
    exact hs.1.const_mul _
  have hrootB : (∫ z : ℕ × ℕ, Real.sqrt (2*((min z.1 z.2 : ℕ) : ℝ)*K) ∂P) ≤ Real.sqrt (2*(a : ℝ)*K) := by
    simp_rw [hroot]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left hs.2 (Real.sqrt_nonneg _)
  exact ⟨hp.1,hp.2,hrootI,hrootB,((integrable_id_poissonMeasure a).comp_fst _ |>.sub
    ((integrable_id_poissonMeasure a).comp_snd _)).abs,integral_abs_sub_poissonPair_le a⟩

end OTSelector.Reconstruction

end
end
