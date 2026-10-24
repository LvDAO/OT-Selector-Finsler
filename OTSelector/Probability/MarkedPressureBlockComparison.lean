import OTSelector.Probability.MarkedGridBlockComparison
import OTSelector.Probability.MarkedGridDiscrepancy

/-!
# Integrating the grid block comparison

The deterministic grid comparison is integrated against the two-cloud marked
Poisson law.  The leaf-block values integrate to the marked pressure at the
per-block intensity, and the repair term is bounded by the expected dyadic
discrepancies, which are controlled by `integral_markedGridDiscrepancy_le`.
-/

open scoped BigOperators NNReal
open MeasureTheory

noncomputable section
namespace OTSelector.Probability

variable {q : ℕ} {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- The integrated grid discrepancy bound. -/
theorem integral_markedGridDiscrepancy_bound (q m J k : ℕ) [NeZero m]
    (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (R : ℝ≥0) :
    ∫ ω, markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω
      ∂(twoMarkedCloudLaw (q := q) A B α β R)
    ≤ Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
  have hfun : markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ =
      gridDiscMarkedDiscrepancy (q := q) (m := m) (J := J) (k := k)
        (hm := hm) (hJ := hJ) (A := A) (B := B) := rfl
  rw [hfun]
  exact integral_markedGridDiscrepancy_le q m J k hm hJ (A := A) (B := B) α β R

/-- The expected hierarchical repair term is bounded by the sum of the sharp
level discrepancies. -/
theorem integral_gridRepair_le (q m J : ℕ) [NeZero m] (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β] (R : ℝ≥0) {r t C G : ℝ}
    (hr : 0 ≤ r) (hC0 : 0 ≤ C) (hG0 : 0 ≤ G) :
    ∫ ω, (∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
          (markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ ω -
            markedGridDiscrepancy (A := A) (B := B) q m J (k - 1) hm hJ ω))
      ∂(twoMarkedCloudLaw (q := q) A B α β R)
    ≤ ∑ k ∈ Finset.Icc 1 J,
        markedGridRepairBound q r C t G k * (1 / 2 : ℝ) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
  classical
  let D : ℕ → TwoMarkedCloudSpace q A B → ℝ :=
    fun k => markedGridDiscrepancy (A := A) (B := B) q m J k hm hJ
  let Bw : ℕ → ℝ := fun k => markedGridRepairBound q r C t G k
  have hDint : ∀ k, Integrable (D k) (twoMarkedCloudLaw (q := q) A B α β R) :=
    fun k => integrable_markedGridDiscrepancy q m J k hm hJ A B α β R
  have hDnonneg : ∀ k ω, 0 ≤ D k ω :=
    fun k ω => cellDiscrepancy_nonneg _ _ _
  have hBw : ∀ k ∈ Finset.Icc 1 J, 0 ≤ Bw k := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hpow : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (k - 1) := pow_nonneg (by norm_num) _
    have hrpow : 0 ≤ r ^ (2 / (q : ℝ)) := Real.rpow_nonneg hr _
    unfold Bw markedGridRepairBound
    rw [if_neg (by omega)]
    unfold markedGridRepairWeight
    have : 0 ≤ 16 * (r ^ (2 / (q : ℝ)) * (C * (q : ℝ))) * (1 / 4 : ℝ) ^ (k - 1) := by
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      positivity
    have : 0 ≤ 2 * |t| * G := by positivity
    linarith
  have hInt1 : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 J,
      Bw k * (1 / 2 : ℝ) * (D k ω - D (k - 1) ω))
      (twoMarkedCloudLaw (q := q) A B α β R) := by
    apply integrable_finsetSum
    intro k hk
    exact ((hDint k).sub (hDint (k - 1))).const_mul _
  have hInt2 : Integrable (fun ω => ∑ k ∈ Finset.Icc 1 J,
      Bw k * (1 / 2 : ℝ) * D k ω)
      (twoMarkedCloudLaw (q := q) A B α β R) := by
    apply integrable_finsetSum
    intro k hk
    exact (hDint k).const_mul _
  have hle : ∀ ω, (∑ k ∈ Finset.Icc 1 J,
        Bw k * (1 / 2 : ℝ) * (D k ω - D (k - 1) ω))
      ≤ ∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) * D k ω := by
    intro ω
    apply Finset.sum_le_sum
    intro k hk
    have hb := hBw k hk
    have hprev := hDnonneg (k - 1) ω
    nlinarith
  calc ∫ ω, (∑ k ∈ Finset.Icc 1 J,
        Bw k * (1 / 2 : ℝ) * (D k ω - D (k - 1) ω))
      ∂(twoMarkedCloudLaw (q := q) A B α β R)
      ≤ ∫ ω, (∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) * D k ω)
        ∂(twoMarkedCloudLaw (q := q) A B α β R) :=
        integral_mono hInt1 hInt2 hle
    _ = ∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) *
          ∫ ω, D k ω ∂(twoMarkedCloudLaw (q := q) A B α β R) := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k _
          rw [integral_const_mul]
        · intro k _
          exact (hDint k).const_mul _
    _ ≤ ∑ k ∈ Finset.Icc 1 J, Bw k * (1 / 2 : ℝ) *
          Real.sqrt (2 * (R : ℝ) * (((2 ^ k + 1) ^ q : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        apply mul_le_mul_of_nonneg_left
        · exact integral_markedGridDiscrepancy_bound q m J k hm hJ α β R
        · have hb := hBw k hk
          nlinarith

end OTSelector.Probability
