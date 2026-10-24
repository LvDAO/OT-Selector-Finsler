import OTSelector.Reconstruction.MarkedStationaryValueLegalGridComparison
import OTSelector.Probability.GridRepairArithmetic
import OTSelector.Probability.GridRepairError

/-! The actual legal class repair has the same vanishing grid-error exponents,
with the finite original scalar and population type constants made explicit. -/
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability

/-- Explicit coefficient of actual legal grid repair. -/
def legalGridRepairConstant (q bins types : ℕ) : ℝ :=
  4 * ((bins : ℝ) + 1) * Real.sqrt (types : ℝ) * gridRepairConstant q

private theorem sum_range_succ_eq_Icc (f : ℕ → ℝ) (J : ℕ) :
    (∑ k ∈ Finset.range J, f (k + 1)) = ∑ k ∈ Finset.Icc 1 J, f k := by
  rw [← Finset.Ico_add_one_right_eq_Icc (a := 1) (b := J), Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm]

/-- The literal legal repair sum is bounded by the original high-dimensional
grid error, multiplied only by the finite original type constants. -/
theorem legal_grid_repair_sum_le (q depth bins types : ℕ) (hq : 4 < q)
    (m : ℕ) (hm : 0 < m) (hdepth2 : 2 ^ depth ≤ 2 * m)
    {r C G t : ℝ} (hr : 0 ≤ r) (hC : 0 ≤ C) (hG : 0 ≤ G) :
    0 ≤ legalGridRepairConstant q bins types ∧
    (∑ k ∈ Finset.range depth,
      Real.sqrt (2 * r * (((((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ)) * types)) *
        (2 * ((bins : ℝ) + 1) * legalGridEdgeBound q r C G t k)) ≤
      legalGridRepairConstant q bins types * (C + |t| * G) * r *
        (Real.rpow (r / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
          Real.rpow (r / (m : ℝ) ^ q) (-(1 / 2))) := by
  obtain ⟨hK, hsum⟩ := grid_repair_sum_le q depth hq m hm hdepth2 (t := t) hr hC hG
  have hfactor : 0 ≤ 4 * ((bins : ℝ) + 1) * Real.sqrt (types : ℝ) := by positivity
  refine ⟨mul_nonneg hfactor hK, ?_⟩
  let f : ℕ → ℝ := fun k ↦
    (16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) + 2 * |t| * G) *
      Real.sqrt (2 * r * (((2 ^ k + 1) ^ q : ℕ) : ℝ))
  have hterm (k : ℕ) :
      Real.sqrt (2 * r * (((((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ)) * types)) *
          (2 * ((bins : ℝ) + 1) * legalGridEdgeBound q r C G t k) ≤
        (4 * ((bins : ℝ) + 1) * Real.sqrt (types : ℝ)) * ((1 / 2 : ℝ) * f (k + 1)) := by
    have hsqrt : Real.sqrt (2 * r * (((((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ)) * types)) =
        Real.sqrt (2 * r * (((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ)) * Real.sqrt (types : ℝ) := by
      rw [← mul_assoc (2 * r) _ (types : ℝ), Real.sqrt_mul (by positivity : 0 ≤ 2 * r *
        (((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ))]
    rw [hsqrt]
    dsimp only [f, legalGridEdgeBound]
    rw [Nat.add_sub_cancel]
    have hs : 0 ≤ Real.sqrt (2 * r * (((2 ^ (k + 1) + 1) ^ q : ℕ) : ℝ)) := Real.sqrt_nonneg _
    have hT : 0 ≤ |t| * G := mul_nonneg (abs_nonneg _) hG
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg
      (by positivity : 0 ≤ 2 * ((bins : ℝ) + 1)) (Real.sqrt_nonneg (types : ℝ))) hs) hT]
  calc
    _ ≤ ∑ k ∈ Finset.range depth,
        (4 * ((bins : ℝ) + 1) * Real.sqrt (types : ℝ)) * ((1 / 2 : ℝ) * f (k + 1)) :=
      Finset.sum_le_sum (fun k _ ↦ hterm k)
    _ = (4 * ((bins : ℝ) + 1) * Real.sqrt (types : ℝ)) *
        ((1 / 2 : ℝ) * ∑ k ∈ Finset.Icc 1 depth, f k) := by
      rw [← Finset.mul_sum, ← Finset.mul_sum, sum_range_succ_eq_Icc]
    _ ≤ (4 * ((bins : ℝ) + 1) * Real.sqrt (types : ℝ)) *
        (gridRepairConstant q * (C + |t| * G) * r *
          (Real.rpow (r / (m : ℝ) ^ q) (2 / (q : ℝ) - 1 / 2) +
            Real.rpow (r / (m : ℝ) ^ q) (-(1 / 2)))) :=
      mul_le_mul_of_nonneg_left hsum hfactor
    _ = _ := by unfold legalGridRepairConstant; ring

end OTSelector.Reconstruction
