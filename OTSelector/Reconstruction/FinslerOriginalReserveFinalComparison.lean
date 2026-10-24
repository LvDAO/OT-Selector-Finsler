import OTSelector.Reconstruction.FinslerOriginalReserveTransportEstimate
import OTSelector.Probability.ProductCouplingTransfer

/-!
# Count slack and notation identifications for the finite value comparison

This module closes the two remaining sub-gaps of
FinslerOriginalReserveTransportEstimate.lean: the count slack of the reserve
construction and the normalization identifications that turn the sharp dyadic
transport estimate into the reserve cost of the paper's finite-value comparison.

1. **Count slack.**  The per-coordinate mismatch counter diffCount is at most the
   coordinate count (diffCount_le), so the actual reserve coefficient
   A = E[N - legalMaximumCard] + E[source mismatch] + E[target mismatch] is at
   most 3N pointwise (countSlack_le_three_mul).  This is the paper's 1 + rho
   count slack, in integrated form.

2. **Sharp budget with count slack.**  With A at most 3N, the sharp dyadic
   repair budget is still bounded by C (max 1 N)^(1 - 2/q) + 16 q D, with the
   constant absorbed by the factor 3 (sharpReserveBudget_of_countSlack).

3. **Reserve cost normalization.**  The paper's repair estimate
   C_q L_n^2 E[h^s], with L_n^2 = n^(2/q) the squared box side in dimension q
   and h the reserve count, has the explicit normalization
   n^(2/q) * (rho n)^(1 - 2/q) = rho^(1 - 2/q) * n
   (collapsedTransport_reserve_identity).  Hence the unnormalized repair cost is
   C_q rho^s n and its per-point (pressure) normalization is exactly the reserve
   term C_q rho^(1 - 2/q) of FiniteValueComparisonWithReserveCost.

4. **Depth to reserve density.**  Under the dyadic stopping-depth conditions at
   box side L with L^q = N, the reserve density (2^K)^(-1) is pinned to the
   inverse box side: (depth_reserveDensity_bounds)
   (2^K)^(-1) <= 1/L  and  1/(2L) <= (2^K)^(-1).
   So the dyadic truncation scale is the reserve density 1/L up to a factor two,
   which is exactly the identification needed when the reserve density rho is
   sent to zero in the box limit.

## Remaining gap

The finite-value comparison still needs the analytic identification of the
retained core expectation with the dilated weighted stationary value
(1-rho)^(1-2/q) I_w(t (1-rho)^(2/q)) up to boundary losses, and the application
of the count-scaled sharp budget at the actual marked-cloud pressure (the
dimension q count normalization N = L^q with the reserve count h = rho n).
The count slack, the sharp transport estimate with slack, the reserve cost
normalization and the reserve-density/box-scale identification are proved here.
-/

open Set MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Probability

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false

/-- The per-coordinate mismatch counter is at most the number of coordinates. -/
theorem diffCount_le {X : Type*} (n : ℕ) (z : Fin n → X × X) :
    diffCount n z ≤ (n : ℝ) := by
  classical
  have hle : ((Finset.univ.filter (fun i : Fin n => (z i).1 ≠ (z i).2)).card : ℝ) ≤ (n : ℝ) := by
    have h := Finset.card_filter_le (Finset.univ : Finset (Fin n))
      (fun i : Fin n => (z i).1 ≠ (z i).2)
    have hcard : (Finset.univ : Finset (Fin n)).card = n := by simp
    exact_mod_cast h.trans_eq hcard
  exact hle

/-- **Count slack of the reserve construction.**  The actual reserve coefficient
A = (N - legal rank) + source mismatch count + target mismatch count is at most
3N: the legal rank is at most N and each mismatch counter is at most N. -/
theorem countSlack_le_three_mul {N : ℕ} {X Y : Type*}
    (K : ℝ) (hK : 0 ≤ K) (hKN : K ≤ (N : ℝ))
    (z₁ : Fin N → X × X) (z₂ : Fin N → Y × Y) :
    ((N : ℝ) - K) + diffCount N z₁ + diffCount N z₂ ≤ 3 * (N : ℝ) := by
  have h1 : (N : ℝ) - K ≤ (N : ℝ) := by linarith
  have h2 : diffCount N z₁ ≤ (N : ℝ) := diffCount_le N z₁
  have h3 : diffCount N z₂ ≤ (N : ℝ) := diffCount_le N z₂
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  linarith

/-- **Sharp dyadic budget with count slack.**  If the low-cardinality
coefficient A is at most 3N (the reserve construction's 1 + rho slack, with the
two marked samples), then the sharp reserve transport estimate still holds with
the constant absorbed by the factor 3. -/
theorem sharpReserveBudget_of_countSlack (q : ℕ) (hq : 4 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N K : ℕ) (A D : ℝ),
      max 1 (N : ℝ) ≤ (2 : ℝ) ^ (K * q) →
      (2 : ℝ) ^ ((K - 1) * q) ≤ max 1 (N : ℝ) →
      0 ≤ A → A ≤ 3 * (N : ℝ) → 0 ≤ D →
      A * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) +
        D * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k / ((2 : ℝ) ^ k)⁻¹
      ≤ C * (max 1 (N : ℝ)) ^ (1 - 2 / (q : ℝ)) + D * (16 * (q : ℝ)) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := dyadic_budget_le_sharp q hq
  refine ⟨3 * C₀, by positivity, ?_⟩
  intro N K A D hlo hhi hA0 hA3 hD0
  have hA3' : A / 3 ≤ (N : ℝ) := by linarith
  have hD3' : (0 : ℝ) ≤ D / 3 := by linarith
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmain := hC₀ N K (A / 3) (D / 3) hlo hhi (by linarith) hA3' hD3'
  have hFlux0 : (0 : ℝ) ≤ (1 / 2) * ∑ k ∈ Finset.range K,
      (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
        Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) := by
    have hnonneg : ∀ k ∈ Finset.range K, (0 : ℝ) ≤
        (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
          Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) := by
      intro k _
      have hq0 : (0 : ℝ) ≤ (q : ℝ) := Nat.cast_nonneg q
      positivity
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg hnonneg)
  have hscale : A * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) +
        D * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k / ((2 : ℝ) ^ k)⁻¹ ≤
      3 * ((A / 3) * ((4 * (q : ℝ)) * (1 / 4 : ℝ) ^ K) +
        (1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) +
        (D / 3) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k / ((2 : ℝ) ^ k)⁻¹) := by
    have hflux : (1 / 2) * ∑ k ∈ Finset.range K,
        (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
          Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q)) ≤
        3 * ((1 / 2) * ∑ k ∈ Finset.range K,
          (8 * (q : ℝ)) * (1 / 4 : ℝ) ^ k *
            Real.sqrt (2 * (N : ℝ) * (2 : ℝ) ^ ((k + 1) * q))) := by
      linarith
    nlinarith [hflux]
  have hbound := mul_le_mul_of_nonneg_left hmain (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith [hbound, hscale]

/-- **Reserve cost normalization.**  The repair estimate C_q L_n^2 E[h^s] of the
paper, with L_n^2 = n^(2/q) the squared box side in dimension q and h = rho n
the reserve count, equals C_q rho^(1 - 2/q) n.  Dividing by the sample count n
gives exactly the reserve term C_q rho^(1 - 2/q) of
FiniteValueComparisonWithReserveCost. -/
theorem collapsedTransport_reserve_identity (q n : ℕ) (hq : 2 ≤ q) (hn : 0 < n)
    (rho : ℝ) (hrho : 0 ≤ rho) :
    (n : ℝ) ^ (2 / (q : ℝ)) * ((rho * n) ^ (1 - 2 / (q : ℝ))) =
      rho ^ (1 - 2 / (q : ℝ)) * (n : ℝ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hs : 1 - 2 / (q : ℝ) = ((q : ℝ) - 2) / (q : ℝ) := by
    field_simp
  rw [Real.mul_rpow hrho hn0.le]
  have hns : (n : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (1 - 2 / (q : ℝ)) =
      (n : ℝ) := by
    rw [← Real.rpow_add hn0]
    have hexp : 2 / (q : ℝ) + (1 - 2 / (q : ℝ)) = 1 := by ring
    rw [hexp, Real.rpow_one]
  calc (n : ℝ) ^ (2 / (q : ℝ)) * (rho ^ (1 - 2 / (q : ℝ)) *
        (n : ℝ) ^ (1 - 2 / (q : ℝ)))
      = rho ^ (1 - 2 / (q : ℝ)) *
          ((n : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (1 - 2 / (q : ℝ))) := by ring
    _ = rho ^ (1 - 2 / (q : ℝ)) * (n : ℝ) := by rw [hns]


/-- **Depth to reserve density.**  Under the dyadic stopping-depth conditions at
box side L with L^q = N, the reserve density (2^K)^(-1) is pinned to the inverse
box side: it is at most 1/L and at least 1/(2L).  So the dyadic truncation scale
of the sharp transport estimate is exactly the reserve density of the box limit,
up to a factor two. -/
theorem depth_reserveDensity_bounds (q N K : ℕ) (hq : 0 < q) (hK : 1 ≤ K) (hN : 1 ≤ N)
    {L : ℝ} (hL : 0 < L) (hNeq : (N : ℝ) = L ^ q)
    (hlo : max 1 (N : ℝ) ≤ (2 : ℝ) ^ (K * q))
    (hhi : (2 : ℝ) ^ ((K - 1) * q) ≤ max 1 (N : ℝ)) :
    ((2 : ℝ) ^ K)⁻¹ ≤ 1 / L ∧ 1 / (2 * L) ≤ ((2 : ℝ) ^ K)⁻¹ := by
  have hmaxN : max 1 (N : ℝ) = (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    exact max_eq_right this
  have hqne : q ≠ 0 := by omega
  have hNpow : (N : ℝ) = L ^ q := hNeq
  have hlo' : L ^ q ≤ ((2 : ℝ) ^ K) ^ q := by
    have h1 : L ^ q = (N : ℝ) := hNpow.symm
    rw [h1]
    rw [hmaxN] at hlo
    calc (N : ℝ) ≤ (2 : ℝ) ^ (K * q) := hlo
      _ = ((2 : ℝ) ^ K) ^ q := by rw [pow_mul]
  have hhi' : ((2 : ℝ) ^ (K - 1)) ^ q ≤ L ^ q := by
    have h1 : (N : ℝ) = L ^ q := hNpow
    rw [hmaxN] at hhi
    calc ((2 : ℝ) ^ (K - 1)) ^ q = (2 : ℝ) ^ ((K - 1) * q) := by rw [pow_mul]
      _ ≤ (N : ℝ) := hhi
      _ = L ^ q := h1
  have hLle : L ≤ (2 : ℝ) ^ K :=
    le_of_pow_le_pow_left₀ (a := L) (b := (2 : ℝ) ^ K) hqne
      (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ K) hlo'
  have hpowKle : (2 : ℝ) ^ (K - 1) ≤ L :=
    le_of_pow_le_pow_left₀ (a := (2 : ℝ) ^ (K - 1)) (b := L) hqne hL.le hhi'
  have h2K : (2 : ℝ) ^ K = 2 * (2 : ℝ) ^ (K - 1) := by
    conv_lhs => rw [show K = (K - 1) + 1 from (Nat.sub_add_cancel hK).symm]
    rw [pow_succ]
    ring
  constructor
  · have h := one_div_le_one_div_of_le hL hLle
    simpa [one_div] using h
  · have h2L : (2 : ℝ) ^ K ≤ 2 * L := by
      rw [h2K]
      linarith
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (2 : ℝ) ^ K) h2L
    simpa [one_div] using h

end OTSelector.Reconstruction
