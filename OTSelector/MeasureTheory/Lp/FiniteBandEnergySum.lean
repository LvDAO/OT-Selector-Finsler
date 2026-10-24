import OTSelector.Analysis.FiniteEnergyPowers
import OTSelector.MeasureTheory.Lp.SecondMomentNorm
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.FiniteBandTrafficLtwo.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.FiniteBandTrafficLtwo`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.Lp.FiniteBandEnergySum

## Lemma skeleton

* **Conditions:** Finite L2 traffic family with second moments bounded by nonnegative local energy/volume contributions having one joint finite-sum budget.
* **Objects:** L2 norm bounds with sqrt(cardinality) or cardinality^(3/4) multiplying the actual total energy/volume powers.
* **Proof detail:** Use Minkowski and the square-root split, then finite Cauchy–Schwarz/Hölder to sum the local square roots or fourth roots before applying their joint budget.

## Mathematical sources

- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=214): Section 7A, Theorem 7.14, p. 199 (Minkowski).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=211): Section 7A, Theorem 7.9, pp. 196–197 (Hölder); Theorem 7.10, p. 197 (finite-measure Lq to Lp).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=233): Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).

Source relation (composition): Finite-band moment assembly; no independence or repeated full-energy budget for each band is used.
-/

/-! Minkowski over the actual finite birth bands spends only their joint
original energy budget. No independence of bands or exceptional events is used. -/
open Set MeasureTheory
open scoped ENNReal BigOperators
noncomputable section
namespace OTSelector.Probability

/-- The two nonnegative energy terms split their square-root L2 bound. -/
theorem sqrt_add_energy_le_sqrt_terms {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb,
    mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Actual per-band mean-square estimates and the common original energy budget
give L2 of their literal sum with the sharp square-root number-of-bands factor. -/
theorem finiteBand_traffic_memLp_two_of_quadratic_energy_budget
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ s, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {cE cV E V : ℝ} (hcE : 0 ≤ cE) (hcV : 0 ≤ cV)
    (hE : (∑ i ∈ s, e i) ≤ E) (hV : (∑ i ∈ s, v i) ≤ V)
    (hmean : ∀ i ∈ s, (∫ x, T i x ^ 2 ∂P) ≤ cE * e i + cV * v i) :
    MemLp (fun x ↦ ∑ i ∈ s, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ s, T i x) 2 P ≤
        ENNReal.ofReal (Real.sqrt (s.card : ℝ) *
          (Real.sqrt cE * Real.sqrt E + Real.sqrt cV * Real.sqrt V)) := by
  have hsumroot : (∑ i ∈ s, (Real.sqrt cE * Real.sqrt (e i) +
      Real.sqrt cV * Real.sqrt (v i))) ≤ Real.sqrt (s.card : ℝ) *
      (Real.sqrt cE * Real.sqrt E + Real.sqrt cV * Real.sqrt V) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ ≤ Real.sqrt cE * (Real.sqrt (s.card : ℝ) * Real.sqrt E) +
          Real.sqrt cV * (Real.sqrt (s.card : ℝ) * Real.sqrt V) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (sum_sqrt_energy_le_card_sqrt_mul s e he hE) (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left (sum_sqrt_energy_le_card_sqrt_mul s v hv hV)
            (Real.sqrt_nonneg _))
      _ = _ := by ring
  refine ⟨memLp_finsetSum s hT, ?_⟩
  calc
    _ = eLpNorm (∑ i ∈ s, T i) 2 P := by congr 1; funext x; simp
    _ ≤ ∑ i ∈ s, eLpNorm (T i) 2 P :=
      eLpNorm_sum_le (fun i hi ↦ (hT i hi).aestronglyMeasurable) (by norm_num)
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (Real.sqrt cE * Real.sqrt (e i) +
        Real.sqrt cV * Real.sqrt (v i)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (eLpNorm_two_le_sqrt_of_integral_sq_le (hT i hi) (hmean i hi)).trans
      apply ENNReal.ofReal_le_ofReal
      exact (sqrt_add_energy_le_sqrt_terms (mul_nonneg hcE (he i)) (mul_nonneg hcV (hv i))).trans_eq
        (by rw [Real.sqrt_mul hcE, Real.sqrt_mul hcV])
    _ = ENNReal.ofReal (∑ i ∈ s, (Real.sqrt cE * Real.sqrt (e i) +
        Real.sqrt cV * Real.sqrt (v i))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ by positivity)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsumroot

/-- The actual small-phase first estimates sum with only the fourth-root
energy budget and the `N^(3/4)` factor. Both original energy terms remain separate. -/
theorem finiteBand_traffic_memLp_two_of_sqrt_energy_budget
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s : Finset ι)
    (T : ι → Ω → ℝ) (hT : ∀ i ∈ s, MemLp (T i) 2 P)
    (e v : ι → ℝ) (he : ∀ i, 0 ≤ e i) (hv : ∀ i, 0 ≤ v i)
    {cE cV E V : ℝ} (hcE : 0 ≤ cE) (hcV : 0 ≤ cV)
    (hE : (∑ i ∈ s, e i) ≤ E) (hV : (∑ i ∈ s, v i) ≤ V)
    (hmean : ∀ i ∈ s, (∫ x, T i x ^ 2 ∂P) ≤ cE * Real.sqrt (e i) + cV * Real.sqrt (v i)) :
    MemLp (fun x ↦ ∑ i ∈ s, T i x) 2 P ∧
      eLpNorm (fun x ↦ ∑ i ∈ s, T i x) 2 P ≤
        ENNReal.ofReal ((s.card : ℝ) ^ (3 / 4 : ℝ) *
          (Real.sqrt cE * E ^ (1 / 4 : ℝ) + Real.sqrt cV * V ^ (1 / 4 : ℝ))) := by
  have hroot (x : ℝ) (hx : 0 ≤ x) : Real.sqrt (Real.sqrt x) = x ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
    norm_num
  have hsumroot : (∑ i ∈ s, (Real.sqrt cE * (e i) ^ (1 / 4 : ℝ) +
      Real.sqrt cV * (v i) ^ (1 / 4 : ℝ))) ≤ (s.card : ℝ) ^ (3 / 4 : ℝ) *
      (Real.sqrt cE * E ^ (1 / 4 : ℝ) + Real.sqrt cV * V ^ (1 / 4 : ℝ)) := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ ≤ Real.sqrt cE * ((s.card : ℝ) ^ (3 / 4 : ℝ) * E ^ (1 / 4 : ℝ)) +
          Real.sqrt cV * ((s.card : ℝ) ^ (3 / 4 : ℝ) * V ^ (1 / 4 : ℝ)) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (sum_fourthRoot_energy_le_card_rpow_mul s e he hE) (Real.sqrt_nonneg _))
          (mul_le_mul_of_nonneg_left (sum_fourthRoot_energy_le_card_rpow_mul s v hv hV)
            (Real.sqrt_nonneg _))
      _ = _ := by ring
  refine ⟨memLp_finsetSum s hT, ?_⟩
  calc
    _ = eLpNorm (∑ i ∈ s, T i) 2 P := by congr 1; funext x; simp
    _ ≤ ∑ i ∈ s, eLpNorm (T i) 2 P :=
      eLpNorm_sum_le (fun i hi ↦ (hT i hi).aestronglyMeasurable) (by norm_num)
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (Real.sqrt cE * (e i) ^ (1 / 4 : ℝ) +
        Real.sqrt cV * (v i) ^ (1 / 4 : ℝ)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply (eLpNorm_two_le_sqrt_of_integral_sq_le (hT i hi) (hmean i hi)).trans
      apply ENNReal.ofReal_le_ofReal
      exact (sqrt_add_energy_le_sqrt_terms (mul_nonneg hcE (Real.sqrt_nonneg _))
        (mul_nonneg hcV (Real.sqrt_nonneg _))).trans_eq
        (by rw [Real.sqrt_mul hcE, Real.sqrt_mul hcV, hroot _ (he i), hroot _ (hv i)])
    _ = ENNReal.ofReal (∑ i ∈ s, (Real.sqrt cE * (e i) ^ (1 / 4 : ℝ) +
        Real.sqrt cV * (v i) ^ (1 / 4 : ℝ))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ add_nonneg
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (he i) _))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg (hv i) _)))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hsumroot

end OTSelector.Probability

end
end
