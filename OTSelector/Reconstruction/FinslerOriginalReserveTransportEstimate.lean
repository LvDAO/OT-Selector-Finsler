import OTSelector.Limit.DyadicSeriesBound

/-!
# Sharp reserve transport estimate

This module derives the sharp reserve cost of the paper,
`C rho^(1 - 2/q) L^q`, from the averaged displacement cost of the residual
ports and the pure dyadic series bound of `OTSelector.Limit.DyadicSeriesBound`.

The concrete dyadic repair budget of
`FinslerRelativeLawReserveEnergyDyadicOptimal` has the shape

`A * ((4 q) (1/4)^K) + (1/2) sum_{k<K} 8 q (1/4)^k sqrt (2 N 2^((k+1)q)) + D * sum_{k<K} 8 q (1/4)^k 2^k`

where A is the expected low-cardinality/mismatch coefficient, D is the
expected retained coordinate displacement (the averaged port displacement), N is
the number of original points and K the dyadic stopping depth.  This is the
crude per-edge majorant of the reserve construction before any estimate; the two
sums are the mesh term at successive dyadic levels and the retained displacement
coefficient.

1. **One-level factorization of the mesh term** (sqrt_two_pow_succ_eq): the
   level-k color discrepancy sqrt (2 N 2^((k+1)q)) equals 2^(q/2) times the
   level-k term sqrt (2 N 2^(k q)) of the paper's series bound.

2. **Retained displacement coefficient** (sum_dyadic_displacement_coeff_le):
   sum_{k<K} 8 q (1/4)^k 2^k is at most 16 q, uniformly in K.

3. **Sharp dyadic budget inequality** (dyadic_budget_le_sharp): with the
   stopping depth tied to the sample size (max 1 N at most 2^(K q) and
   2^((K-1) q) at most max 1 N) and the coefficient A at most N, the whole
   transport budget is bounded by C (max 1 N)^(1 - 2/q) + 16 q D.  The exponent
   1 - 2/q is exactly the paper's sharp exponent, and the displacement term is
   the averaged port transport cost with its uniform geometric coefficient.

## Remaining gap

The coefficient A of the actual reserve construction is
E[N - legalMaximumCard] + E[source mismatch count] + E[target mismatch count];
bounding it by N (the reserve construction's 1 + rho slack) and identifying the
normalized C (max 1 N)^(1-2/q) / L^q term with the reserve cost C rho^(1-2/q) at
N = L^q, rho = 2^(-K), are the remaining notation-level identifications, as is
the identification of the retained displacement term 16 q D with the dilated
weighted stationary value.
-/

open Set
open scoped BigOperators Topology

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

/-- **One-level factorization of the mesh term.**  The level-k color
discrepancy of the budget sqrt (2 N 2^((k+1)q)) is 2^(q/2) times the level-k
term sqrt (2 N 2^(k q)) of the paper's dyadic series bound. -/
theorem sqrt_two_pow_succ_eq (N k q : ℕ) :
    Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) =
      (2 : ℝ) ^ ((q : ℝ) / 2) * Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q)) := by
  have hpow : (2 : ℝ) ^ ((k + 1) * q) = (2 : ℝ) ^ (k * q) * (2 : ℝ) ^ q := by
    rw [← pow_add]
    congr 1
    ring
  have hsplit : 2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q) =
      (2 : ℝ) ^ q * (2 * (N : ℝ) * (2 : ℝ) ^ (k * q)) := by
    rw [hpow]; ring
  rw [hsplit]
  have hsqrt2q : Real.sqrt ((2 : ℝ) ^ q) = (2 : ℝ) ^ ((q : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((2 : ℝ)) q,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [Real.sqrt_mul (by positivity), hsqrt2q]

/-- **Retained displacement coefficient.**  The geometric coefficient of the
retained displacement in the dyadic repair budget is uniformly bounded by
16 q, independently of the stopping depth. -/
theorem sum_dyadic_displacement_coeff_le (q K : ℕ) :
    (∑ k ∈ Finset.range K,
        (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k / ((2 : ℝ) ^ k)⁻¹) ≤ 16 * (q : ℝ) := by
  have hstep : ∀ k : ℕ,
      (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k / ((2 : ℝ) ^ k)⁻¹ =
        (8 * (q : ℝ)) * (1 / 2 : ℝ) ^ k := by
    intro k
    have h2 : ((2 : ℝ) ^ k)⁻¹ = (1 / 2 : ℝ) ^ k := by
      rw [← inv_pow]
      congr 1
      norm_num
    rw [h2]
    have h4 : (1 / 4 : ℝ) ^ k = ((1 / 2 : ℝ) ^ k) ^ 2 := by
      have h24 : (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) := by norm_num
      rw [h24, mul_pow, ← pow_two]
    rw [h4]
    have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
    field_simp
  simp only [hstep]
  rw [← Finset.mul_sum]
  have hgeom_eq : ∀ K : ℕ, (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) =
      2 - 2 * (1 / 2 : ℝ) ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ K ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  have hgeom : (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k) ≤ 2 := by
    rw [hgeom_eq K]
    have hpow : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ K := by positivity
    linarith
  calc (8 * (q : ℝ)) * (∑ k ∈ Finset.range K, (1 / 2 : ℝ) ^ k)
      ≤ (8 * (q : ℝ)) * 2 := mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = 16 * (q : ℝ) := by ring

/-- **Sharp dyadic budget inequality (the sharp reserve transport estimate).**
For q > 4, if the dyadic stopping depth K is tied to the sample size N by
max 1 N <= 2^(K q) and 2^((K-1) q) <= max 1 N, and the low-cardinality
coefficient A is nonnegative and at most N, then the averaged repair transport
budget of the reserve construction is bounded by the paper's sharp reserve cost
C (max 1 N)^(1 - 2/q) plus the displacement term with its uniform geometric
coefficient 16 q D. -/
theorem dyadic_budget_le_sharp (q : ℕ) (hq : 4 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N K : ℕ) (A D : ℝ),
      max 1 (N : ℝ) ≤ (2 : ℝ) ^ (K * q) →
      (2 : ℝ) ^ ((K - 1) * q) ≤ max 1 (N : ℝ) →
      0 ≤ A → A ≤ (N : ℝ) → 0 ≤ D →
      A * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) +
        D * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k / ((2 : ℝ) ^ k)⁻¹
      ≤ C * (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ)) + D * (16 * (q : ℝ)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_dyadic_series_bound_of_depth q hq
  have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
  refine ⟨C₀ * max 1 ((2 : ℝ) ^ ((q : ℝ) / 2)), ?_, ?_⟩
  · have hmax : (0 : ℝ) ≤ max 1 ((2 : ℝ) ^ ((q : ℝ) / 2)) := by positivity
    exact mul_nonneg hC₀0 hmax
  · intro N K A D hlo hhi hA0 hAN hD0
    have hM1 : (1 : ℝ) ≤ max 1 (N : ℝ) := le_max_left _ _
    have hdist : (N : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q))
        ≤ C₀ * (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ)) := hC₀ N K hlo hhi
    have hcoarse : A * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) ≤
        (N : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) := by
      have hcoef : (0 : ℝ) ≤ (4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K := by positivity
      exact mul_le_mul_of_nonneg_right hAN hcoef
    have hflux_eq : (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) =
        (2 : ℝ) ^ ((q : ℝ) / 2) *
          ((1 / 2) * ∑ k ∈ Finset.range K,
            (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
              Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q))) := by
      have hterm : ∀ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
              Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) =
            (2 : ℝ) ^ ((q : ℝ) / 2) *
              ((8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q))) := by
        intro k _
        rw [sqrt_two_pow_succ_eq]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      ring
    have hmax_eq : max 1 ((2 : ℝ) ^ ((q : ℝ) / 2)) = (2 : ℝ) ^ ((q : ℝ) / 2) := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) := by
        have h0 : (0 : ℝ) ≤ (q : ℝ) / 2 := by positivity
        calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
          _ ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h0
      exact max_eq_right h1
    have hflux_le : (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q)) ≤
        C₀ * (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ)) := by
      have hcoef : (0 : ℝ) ≤ (N : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) := by
        positivity
      linarith [hdist, hcoef]
    have hdisp_le : D * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k / ((2 : ℝ) ^ k)⁻¹ ≤
        D * (16 * (q : ℝ)) :=
      mul_le_mul_of_nonneg_left (sum_dyadic_displacement_coeff_le q K) hD0
    have hbudget_le : A * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q))
        ≤ (2 : ℝ) ^ ((q : ℝ) / 2) *
            (C₀ * (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ))) := by
      rw [hflux_eq]
      have h2q : (0 : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
        Real.rpow_nonneg (by norm_num) _
      have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((q : ℝ) / 2) := by
        have h0 : (0 : ℝ) ≤ (q : ℝ) / 2 := by positivity
        calc (1 : ℝ) = (2 : ℝ) ^ (0 : ℝ) := by rw [Real.rpow_zero]
          _ ≤ (2 : ℝ) ^ ((q : ℝ) / 2) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) h0
      have hNc : (0 : ℝ) ≤ (N : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) := by
        positivity
      have hXle : (N : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
          (2 : ℝ) ^ ((q : ℝ) / 2) *
            ((1 / 2) * ∑ k ∈ Finset.range K,
              (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q))) ≤
          (2 : ℝ) ^ ((q : ℝ) / 2) *
            ((N : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
              (1 / 2) * ∑ k ∈ Finset.range K,
                (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                  Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q))) := by
        have hmul := mul_le_mul_of_nonneg_right hX1 hNc
        nlinarith [hmul]
      have hXmul : (2 : ℝ) ^ ((q : ℝ) / 2) *
            ((N : ℝ) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
              (1 / 2) * ∑ k ∈ Finset.range K,
                (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
                  Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ (k * q))) ≤
          (2 : ℝ) ^ ((q : ℝ) / 2) *
            (C₀ * (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hdist h2q
      linarith [hcoarse, hXle, hXmul]
    have hCeq : (2 : ℝ) ^ ((q : ℝ) / 2) *
        (C₀ * (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ))) =
        (C₀ * max 1 ((2 : ℝ) ^ ((q : ℝ) / 2))) *
          (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ)) := by
      rw [hmax_eq]
      ring
    linarith [hbudget_le, hdisp_le, hCeq]

end OTSelector.Reconstruction
