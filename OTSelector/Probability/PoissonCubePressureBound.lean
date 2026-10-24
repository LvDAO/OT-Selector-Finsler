import OTSelector.Finite.PartitionCount
import OTSelector.Probability.PoissonDyadicUpperBound
import OTSelector.Probability.PoissonDyadicDiscrepancy
import OTSelector.Limit.DyadicSeriesBound

/-!
# A uniform-in-`r` bound for the Poissonized cube pressure

This module assembles the Poisson dyadic discrepancy estimates into a linear
bound for the Poissonized cube pressure, uniform in the intensity `r ≥ 1` and
depending on the tilt `t` and the probe bound `G` only through `1 + |t| G`.

The truncated cell discrepancy compares the dyadic histograms of the first
`sourceCount` and `targetCount` points after coordinatewise truncation to the
unit cube.  On the unit cube truncation is the identity, so this discrepancy
agrees almost surely with the Poisson cloud cell discrepancy of
`PoissonDyadicDiscrepancy`.  Its integral is therefore bounded both by `2 r`
and by the square-root histogram bound, and the minimum of the two is fed into
the integrated hierarchical matching estimate.

The remaining real-analytic estimate is the dyadic geometric series bound of
`DyadicSeriesBound`, which caps the depth at `K = ⌈r⌉` and produces the
constant `C`.  The depth term `4^{-K}` is absorbed into `r^{-2/q}`, and the
two series halves are bounded by the geometric sum `∑ 4^{-k} ≤ 4/3` and by
the cap `min (2K) (sqrt (2K 2^{kq}))`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open OTSelector
open OTSelector.Reconstruction

noncomputable section
namespace OTSelector.Probability

/-! ## Partition counts versus cloud cell counts -/

/-- The real partition count is the cardinality of the corresponding filter. -/
theorem partitionCount_eq_card_filter {I C : Type*} [Fintype I] [DecidableEq C]
    (x : I → C) (a : C) :
    partitionCount x a = ((Finset.univ.filter (fun i => x i = a)).card : ℝ) :=
  OTSelector.partitionCount_eq_card_filter x a

/-- The dyadic partition count of a Poisson cloud is its cloud cell count. -/
theorem partitionCount_dyadicCell_eq_cloudCellCount (q k : ℕ) (z : PoissonCloudSpace q)
    (c : Fin q → Fin (2 ^ k)) :
    partitionCount (fun i : Fin z.1 => dyadicCell q k (z.2 (i : ℕ))) c =
      (cloudCellCount q k z c : ℝ) := by
  rw [partitionCount_eq_card_filter]
  rfl

/-! ## The truncated cell discrepancy -/

/-- The level-`k` dyadic cell-count discrepancy of the truncated two-cloud
sample.  The cells are those of `Fin q → Fin (2 ^ k)`, and the points are
truncated coordinatewise to the unit cube. -/
noncomputable def truncCellDiscrepancy (q k : ℕ) (ω : TwoCloudSpace q) : ℝ :=
  ∑ c : Fin q → Fin (2 ^ k),
    |(partitionCount ((dyadicCell q k) ∘
        (fun i : Fin (sourceCount ω) => cubeTruncPoint (sourcePoint ω (i : ℕ)))) c : ℝ) -
      (partitionCount ((dyadicCell q k) ∘
        (fun j : Fin (targetCount ω) => cubeTruncPoint (targetPoint ω (j : ℕ)))) c : ℝ)|

/-- On the unit cube the truncated cell discrepancy is the cloud cell
discrepancy. -/
theorem truncCellDiscrepancy_eq_cloudCellDiscrepancy (q k : ℕ) (ω : TwoCloudSpace q)
    (hsrc : ∀ i, sourcePoint ω i ∈ unitCube q)
    (htgt : ∀ j, targetPoint ω j ∈ unitCube q) :
    truncCellDiscrepancy q k ω = cloudCellDiscrepancy q k ω := by
  unfold truncCellDiscrepancy cloudCellDiscrepancy
  apply Finset.sum_congr rfl
  intro c _
  have hsrc_count : partitionCount ((dyadicCell q k) ∘
      (fun i : Fin (sourceCount ω) => cubeTruncPoint (sourcePoint ω (i:ℕ)))) c =
      (cloudCellCount q k ω.1 c : ℝ) := by
    have hsrc'' : (fun i : Fin (sourceCount ω) => cubeTruncPoint (sourcePoint ω (i:ℕ))) =
        (fun i : Fin (sourceCount ω) => sourcePoint ω (i:ℕ)) := by
      funext i
      exact cubeTruncPoint_eq_of_mem (hsrc (i:ℕ))
    rw [hsrc'']
    change partitionCount (fun i : Fin (sourceCount ω) => dyadicCell q k (sourcePoint ω (i:ℕ))) c =
      (cloudCellCount q k ω.1 c : ℝ)
    rw [partitionCount_eq_card_filter]
    rfl
  have htgt_count : partitionCount ((dyadicCell q k) ∘
      (fun j : Fin (targetCount ω) => cubeTruncPoint (targetPoint ω (j:ℕ)))) c =
      (cloudCellCount q k ω.2 c : ℝ) := by
    have htgt'' : (fun j : Fin (targetCount ω) => cubeTruncPoint (targetPoint ω (j:ℕ))) =
        (fun j : Fin (targetCount ω) => targetPoint ω (j:ℕ)) := by
      funext j
      exact cubeTruncPoint_eq_of_mem (htgt (j:ℕ))
    rw [htgt'']
    change partitionCount (fun j : Fin (targetCount ω) => dyadicCell q k (targetPoint ω (j:ℕ))) c =
      (cloudCellCount q k ω.2 c : ℝ)
    rw [partitionCount_eq_card_filter]
    rfl
  rw [hsrc_count, htgt_count]

/-- The truncated cell discrepancy is integrable under the two-cloud law. -/
theorem integrable_truncCellDiscrepancy (q k : ℕ) (r : ℝ≥0) :
    Integrable (truncCellDiscrepancy q k) (twoCloudLaw q r) := by
  have hae : truncCellDiscrepancy q k =ᵐ[twoCloudLaw q r] cloudCellDiscrepancy q k := by
    filter_upwards [ae_points_mem_unitCube_twoCloudLaw q r] with ω hω
    exact truncCellDiscrepancy_eq_cloudCellDiscrepancy q k ω hω.1 hω.2
  exact (integrable_cloudCellDiscrepancy q k r).congr hae.symm

/-- The expected truncated cell discrepancy obeys both the trivial `2 r` bound
and the square-root histogram bound. -/
theorem integral_truncCellDiscrepancy_le (q k : ℕ) (r : ℝ≥0) :
    ∫ ω, truncCellDiscrepancy q k ω ∂(twoCloudLaw q r)
      ≤ min (2 * (r : ℝ)) (Real.sqrt (2 * (r : ℝ) * (2 : ℝ) ^ (k * q))) := by
  have hae : truncCellDiscrepancy q k =ᵐ[twoCloudLaw q r] cloudCellDiscrepancy q k := by
    filter_upwards [ae_points_mem_unitCube_twoCloudLaw q r] with ω hω
    exact truncCellDiscrepancy_eq_cloudCellDiscrepancy q k ω hω.1 hω.2
  rw [integral_congr_ae hae]
  exact le_min (integral_cloudCellDiscrepancy_le_trivial q k r)
    (integral_cloudCellDiscrepancy_le q k r)

/-! ## The real-analytic estimates -/

/-- The depth term is dominated by `r ^ (-2/q)` when the depth is the ceiling
of `r`. -/
theorem quarter_pow_ceil_le_rpow_neg (q K : ℕ) {r : ℝ} (hq : 0 < q)
    (hr1 : 1 ≤ r) (hrK : r ≤ (K:ℝ)) :
    (1/4:ℝ)^K ≤ r^(-(2/(q:ℝ))) := by
  have hqne : (q:ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hKq : K ≤ K * q := Nat.le_mul_of_pos_right K hq
  have hKpow : (K:ℝ) < (2:ℝ)^(K*q) := by
    have h1 : K < 2^K := Nat.lt_two_pow_self (n := K)
    have h1' : (K:ℝ) < (2:ℝ)^K := by
      calc (K:ℝ) < ((2^K : ℕ) : ℝ) := by exact_mod_cast h1
        _ = (2:ℝ)^K := by push_cast; ring
    have h2 : 2^K ≤ 2^(K*q) := Nat.pow_le_pow_right (by norm_num : 0 < 2) hKq
    have h2' : (2:ℝ)^K ≤ (2:ℝ)^(K*q) := by
      calc (2:ℝ)^K = ((2^K : ℕ) : ℝ) := by push_cast; ring
        _ ≤ ((2^(K*q) : ℕ) : ℝ) := by exact_mod_cast h2
        _ = (2:ℝ)^(K*q) := by push_cast; ring
    exact h1'.trans_le h2'
  have hrle : r ≤ (2:ℝ)^(K*q) := hrK.trans hKpow.le
  have h := Real.rpow_le_rpow_of_nonpos hrpos hrle (z := -(2/(q:ℝ)))
    (neg_nonpos.mpr (by positivity : (0:ℝ) ≤ 2/(q:ℝ)))
  rwa [two_pow_mul_rpow_neg_eq_quarter_pow K q hqne] at h

/-- The factor `r^(2/q)` times the capped sample-size power is at most `2 r`
when the sample size is at most `2 r`. -/
theorem rpow_mul_max_ceil_le (q K : ℕ) {r : ℝ} (hq : 4 < q) (hr1 : 1 ≤ r)
    (hK1 : 1 ≤ (K:ℝ)) (hK_2r : (K:ℝ) ≤ 2*r) :
    r^(2/(q:ℝ)) * (max 1 (K:ℝ))^(1 - 2/(q:ℝ)) ≤ 2*r := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hqpos : (0:ℝ) < (q:ℝ) := by positivity
  have hKpos : 0 < (K:ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hmax : max 1 (K:ℝ) = (K:ℝ) := max_eq_right hK1
  rw [hmax]
  have he0 : 0 ≤ (1:ℝ) - 2/(q:ℝ) := by
    rw [sub_nonneg, div_le_one hqpos]
    have hq4 : (4:ℝ) < (q:ℝ) := by exact_mod_cast hq
    linarith
  have he1 : (1:ℝ) - 2/(q:ℝ) ≤ 1 := by
    have : 0 ≤ 2/(q:ℝ) := by positivity
    linarith
  have hKpow : (K:ℝ)^(1-2/(q:ℝ)) ≤ (2*r)^(1-2/(q:ℝ)) :=
    Real.rpow_le_rpow hKpos.le hK_2r he0
  have h2rpow : (2*r)^(1-2/(q:ℝ)) = (2:ℝ)^(1-2/(q:ℝ)) * r^(1-2/(q:ℝ)) :=
    Real.mul_rpow (by norm_num) hr0
  have h2le : (2:ℝ)^(1-2/(q:ℝ)) ≤ 2 := by
    calc (2:ℝ)^(1-2/(q:ℝ)) ≤ (2:ℝ)^(1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) he1
      _ = 2 := Real.rpow_one 2
  have hpr : r^(2/(q:ℝ)) * r^(1-2/(q:ℝ)) = r := by
    rw [← Real.rpow_add (lt_of_lt_of_le zero_lt_one hr1)]
    rw [show 2/(q:ℝ) + (1 - 2/(q:ℝ)) = 1 by ring, Real.rpow_one]
  calc r^(2/(q:ℝ)) * (K:ℝ)^(1-2/(q:ℝ))
      ≤ r^(2/(q:ℝ)) * (2*r)^(1-2/(q:ℝ)) :=
        mul_le_mul_of_nonneg_left hKpow (Real.rpow_nonneg hr0 _)
    _ = r^(2/(q:ℝ)) * ((2:ℝ)^(1-2/(q:ℝ)) * r^(1-2/(q:ℝ))) := by rw [h2rpow]
    _ = (2:ℝ)^(1-2/(q:ℝ)) * (r^(2/(q:ℝ)) * r^(1-2/(q:ℝ))) := by ring
    _ = (2:ℝ)^(1-2/(q:ℝ)) * r := by rw [hpr]
    _ ≤ 2 * r := mul_le_mul_of_nonneg_right h2le hr0

/-- The base term of the hierarchical bound: the terminal depth term is
absorbed into `8 q r` and the shift produces `4 B r`. -/
theorem base_discrepancy_bound (q K : ℕ) {r B : ℝ} (hq : 0 < q) (hr1 : 1 ≤ r)
    (hrK : r ≤ (K:ℝ)) :
    (r^(2/(q:ℝ)) * (4*(q:ℝ) * (1/4:ℝ)^K) + 2*B) * (2*r) ≤ 8*(q:ℝ)*r + 4*B*r := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr1
  have hquarter := quarter_pow_ceil_le_rpow_neg q K hq hr1 hrK
  have hpquarter : r^(2/(q:ℝ)) * (1/4:ℝ)^K ≤ 1 := by
    have hmul : r^(2/(q:ℝ)) * r^(-(2/(q:ℝ))) = 1 := by
      rw [← Real.rpow_add hrpos]
      rw [show 2/(q:ℝ) + -(2/(q:ℝ)) = 0 by ring, Real.rpow_zero]
    calc r^(2/(q:ℝ)) * (1/4:ℝ)^K ≤ r^(2/(q:ℝ)) * r^(-(2/(q:ℝ))) :=
          mul_le_mul_of_nonneg_left hquarter (Real.rpow_nonneg hrpos.le _)
      _ = 1 := hmul
  have h1 : r^(2/(q:ℝ)) * (4*(q:ℝ) * (1/4:ℝ)^K) * (2*r) ≤ 8*(q:ℝ)*r := by
    have h8 : (0:ℝ) ≤ 8*(q:ℝ)*r := by positivity
    calc r^(2/(q:ℝ)) * (4*(q:ℝ) * (1/4:ℝ)^K) * (2*r)
        = (r^(2/(q:ℝ)) * (1/4:ℝ)^K) * (8*(q:ℝ)*r) := by ring
      _ ≤ 1 * (8*(q:ℝ)*r) := mul_le_mul_of_nonneg_right hpquarter h8
      _ = 8*(q:ℝ)*r := by ring
  calc (r^(2/(q:ℝ)) * (4*(q:ℝ) * (1/4:ℝ)^K) + 2*B) * (2*r)
      = r^(2/(q:ℝ)) * (4*(q:ℝ) * (1/4:ℝ)^K) * (2*r) + 4*B*r := by ring
    _ ≤ 8*(q:ℝ)*r + 4*B*r := by linarith

/-- The min-capped part of the dyadic series, bounded by `2 C₀ r` using the
series estimate at sample size `K = ⌈r⌉`. -/
theorem series_min_part_le (q K : ℕ) {r C₀ : ℝ} (hq : 4 < q) (hr1 : 1 ≤ r)
    (hK1 : 1 ≤ (K:ℝ)) (hrK : r ≤ (K:ℝ)) (hK_2r : (K:ℝ) ≤ 2*r)
    (hC₀ : ∀ (m N : ℕ), (1/2) * ∑ k ∈ Finset.range (N+1),
      (8*(q:ℝ)) * (1/4:ℝ)^k * min (2*(m:ℝ)) (Real.sqrt (2*(m:ℝ)*(2:ℝ)^(k*q))) ≤
        C₀ * (max 1 (m:ℝ))^(1 - 2/(q:ℝ)))
    (hC₀0 : 0 ≤ C₀) :
    (1/2) * ∑ k : Fin K, (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) *
        min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q)))
      ≤ 2 * C₀ * r := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hp0 : 0 ≤ r^(2/(q:ℝ)) := Real.rpow_nonneg hr0 _
  have hq0 : 0 ≤ (q:ℝ) := Nat.cast_nonneg q
  have hD_le_E : ∀ k : Fin K,
      min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q))) ≤
      min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^((k:ℕ)*q))) := by
    intro k
    apply le_min
    · exact (min_le_left _ _).trans (by linarith)
    · refine (min_le_right _ _).trans (Real.sqrt_le_sqrt ?_)
      have hp : (0:ℝ) ≤ (2:ℝ)^((k:ℕ)*q) := by positivity
      nlinarith [hrK, hp]
  have hnonneg_E : ∀ k : ℕ, 0 ≤ (8*(q:ℝ)) * (1/4:ℝ)^k *
      min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q))) := by
    intro k
    have h1 : (0:ℝ) ≤ 8*(q:ℝ) := by positivity
    have h2 : (0:ℝ) ≤ (1/4:ℝ)^k := by positivity
    have h3 : (0:ℝ) ≤ min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q))) :=
      le_min (by positivity) (Real.sqrt_nonneg _)
    exact mul_nonneg (mul_nonneg h1 h2) h3
  have hstep1 : ∑ k : Fin K, (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ)) *
        min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q)))
      ≤ ∑ k ∈ Finset.range K, (8*(q:ℝ)) * (1/4:ℝ)^k *
        min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q))) := by
    rw [Fin.sum_univ_eq_sum_range
      (fun k => (8*(q:ℝ)) * (1/4:ℝ)^k * min (2*r) (Real.sqrt (2*r * (2:ℝ)^(k*q)))) K]
    apply Finset.sum_le_sum
    intro k hk
    have hDE := hD_le_E ⟨k, Finset.mem_range.mp hk⟩
    have hc : 0 ≤ 8*(q:ℝ) * (1/4:ℝ)^k := by positivity
    calc (8*(q:ℝ)) * (1/4:ℝ)^k * min (2*r) (Real.sqrt (2*r * (2:ℝ)^(k*q)))
        = (8*(q:ℝ) * (1/4:ℝ)^k) * min (2*r) (Real.sqrt (2*r * (2:ℝ)^(k*q))) := by ring
      _ ≤ (8*(q:ℝ) * (1/4:ℝ)^k) *
            min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q))) :=
          mul_le_mul_of_nonneg_left hDE hc
      _ = (8*(q:ℝ)) * (1/4:ℝ)^k *
            min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q))) := by ring
  have hstep2 : ∑ k ∈ Finset.range K, (8*(q:ℝ)) * (1/4:ℝ)^k *
        min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q)))
      ≤ ∑ k ∈ Finset.range (K+1), (8*(q:ℝ)) * (1/4:ℝ)^k *
        min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q))) :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset_range.mpr (Nat.le_succ K)) (fun i _ _ => hnonneg_E i)
  have hS : ∑ k : Fin K, (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ)) *
        min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q)))
      ≤ ∑ k ∈ Finset.range (K+1), (8*(q:ℝ)) * (1/4:ℝ)^k *
        min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q))) := hstep1.trans hstep2
  have hfactor : ∑ k : Fin K, (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) *
        min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q)))
      = r^(2/(q:ℝ)) * ∑ k : Fin K, (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ)) *
        min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hseries := hC₀ K K
  calc (1/2) * ∑ k : Fin K, (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) *
        min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q)))
      = r^(2/(q:ℝ)) * ((1/2) * ∑ k : Fin K, (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ)) *
          min (2*r) (Real.sqrt (2*r * (2:ℝ)^((k:ℕ)*q)))) := by
        rw [hfactor]; ring
    _ ≤ r^(2/(q:ℝ)) * ((1/2) * ∑ k ∈ Finset.range (K+1), (8*(q:ℝ)) * (1/4:ℝ)^k *
          min (2*(K:ℝ)) (Real.sqrt (2*(K:ℝ)*(2:ℝ)^(k*q)))) := by
        apply mul_le_mul_of_nonneg_left _ hp0
        exact mul_le_mul_of_nonneg_left hS (by norm_num)
    _ ≤ r^(2/(q:ℝ)) * (C₀ * (max 1 (K:ℝ))^(1 - 2/(q:ℝ))) := by
        apply mul_le_mul_of_nonneg_left hseries hp0
    _ = C₀ * (r^(2/(q:ℝ)) * (max 1 (K:ℝ))^(1 - 2/(q:ℝ))) := by ring
    _ ≤ C₀ * (2*r) := by
        apply mul_le_mul_of_nonneg_left (rpow_mul_max_ceil_le q K hq hr1 hK1 hK_2r) hC₀0
    _ = 2 * C₀ * r := by ring

/-- `r^(2/q) * sqrt (2r) ≤ sqrt 2 * r` for `q > 4` and `r ≥ 1`. -/
theorem hp_sqrt_le (q : ℕ) {r : ℝ} (hq : 4 < q) (hr1 : 1 ≤ r) :
    r^(2/(q:ℝ)) * Real.sqrt (2*r) ≤ Real.sqrt 2 * r := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hqpos : (0:ℝ) < (q:ℝ) := by positivity
  have hexp : 2/(q:ℝ) ≤ (1:ℝ)/2 := by
    rw [div_le_div_iff₀ hqpos (by norm_num : (0:ℝ) < 2)]
    have hq4 : (4:ℝ) < (q:ℝ) := by exact_mod_cast hq
    linarith
  have hp_le : r^(2/(q:ℝ)) ≤ Real.sqrt r := by
    have h := Real.rpow_le_rpow_of_exponent_le hr1 hexp
    rw [Real.sqrt_eq_rpow]
    exact h
  calc r^(2/(q:ℝ)) * Real.sqrt (2*r) ≤ Real.sqrt r * Real.sqrt (2*r) :=
        mul_le_mul_of_nonneg_right hp_le (Real.sqrt_nonneg _)
    _ = Real.sqrt (r * (2*r)) := (Real.sqrt_mul hr0 (2*r)).symm
    _ = Real.sqrt (2 * r^2) := by ring_nf
    _ = Real.sqrt 2 * Real.sqrt (r^2) := Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2) (r^2)
    _ = Real.sqrt 2 * r := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hr0]

/-- The square-root part of the dyadic series, bounded by
`(16/3) q sqrt 2 r` using `∑ 4^{-k} ≤ 4/3` and `r^(2/q) ≤ sqrt r`. -/
theorem series_sqrt_part_le (q K : ℕ) {r : ℝ} (hq : 4 < q) (hr1 : 1 ≤ r) :
    (1/2) * ∑ k : Fin K, (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * Real.sqrt (2*r)
      ≤ (16/3) * (q:ℝ) * Real.sqrt 2 * r := by
  have hr0 : 0 ≤ r := zero_le_one.trans hr1
  have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
  have hp0 : 0 ≤ r^(2/(q:ℝ)) := Real.rpow_nonneg hr0 _
  have hs0 : 0 ≤ Real.sqrt (2*r) := Real.sqrt_nonneg _
  have hsum : ∑ k : Fin K, (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * Real.sqrt (2*r)
      = (8*(q:ℝ)) * (r^(2/(q:ℝ)) * Real.sqrt (2*r)) * ∑ k : Fin K, (1/4:ℝ)^(k:ℕ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hquarter_sum : ∑ k : Fin K, (1/4:ℝ)^(k:ℕ) ≤ 4/3 := by
    rw [Fin.sum_univ_eq_sum_range (fun k => (1/4:ℝ)^k) K]
    exact sum_range_quarter_le K
  have hquarter_nonneg : (0:ℝ) ≤ ∑ k : Fin K, (1/4:ℝ)^(k:ℕ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hps := hp_sqrt_le q hq hr1
  have hA : (0:ℝ) ≤ 4*(q:ℝ) := by positivity
  have hB : (0:ℝ) ≤ 4*(q:ℝ) * (Real.sqrt 2 * r) := by positivity
  have hstep : (4*(q:ℝ)) * (r^(2/(q:ℝ)) * Real.sqrt (2*r)) * ∑ k : Fin K, (1/4:ℝ)^(k:ℕ)
      ≤ (4*(q:ℝ)) * (Real.sqrt 2 * r) * (4/3) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hps hA
    · exact hquarter_sum
    · exact hquarter_nonneg
    · exact hB
  calc (1/2) * ∑ k : Fin K, (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * Real.sqrt (2*r)
      = (4*(q:ℝ)) * (r^(2/(q:ℝ)) * Real.sqrt (2*r)) * ∑ k : Fin K, (1/4:ℝ)^(k:ℕ) := by
        rw [hsum]; ring
    _ ≤ (4*(q:ℝ)) * (Real.sqrt 2 * r) * (4/3) := hstep
    _ = (16/3) * (q:ℝ) * Real.sqrt 2 * r := by ring

/-! ## The uniform pressure bound -/

set_option maxHeartbeats 0 in
/-- **Uniform-in-`r` Poisson cube pressure bound.**  For `q > 4` there is a
constant `C ≥ 0` such that for every probe bound `G ≥ 0`, every bounded
measurable probe `g`, every tilt `t`, and every intensity `r ≥ 1`, the
Poissonized cube pressure is at most `C (1 + |t| G) r`. -/
theorem exists_poissonCubePressure_bound (q : ℕ) (hq : 4 < q) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (G t : ℝ), 0 ≤ G →
      ∀ (g : (Fin q → ℝ) → (Fin q → ℝ) → ℝ),
        Measurable (Function.uncurry g) → (∀ x y, |g x y| ≤ G) →
        ∀ r : ℝ≥0, 1 ≤ r →
          poissonCubePressure q r g t ≤ C * (1 + |t| * G) * (r : ℝ) := by
  obtain ⟨C₀, hC₀0, hC₀⟩ := exists_dyadic_series_bound q hq
  refine ⟨8*(q:ℝ) + 4 + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2, ?_, ?_⟩
  · have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
    have h1 : (0:ℝ) ≤ 8*(q:ℝ) + 4 := by positivity
    have h2 : (0:ℝ) ≤ 2*C₀ := by linarith
    have h3 : (0:ℝ) ≤ (16/3)*(q:ℝ)*Real.sqrt 2 := by positivity
    linarith
  · intro G t hG0 g hg hgb r hr1
    have hr1' : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr1
    have hrpos : (0:ℝ) < (r:ℝ) := lt_of_lt_of_le zero_lt_one hr1'
    have hr0 : (0:ℝ) ≤ (r:ℝ) := hrpos.le
    have hqpos_nat : 0 < q := by omega
    have hKpos : 0 < Nat.ceil (r:ℝ) := Nat.ceil_pos.mpr hrpos
    have hrK : (r:ℝ) ≤ ((Nat.ceil (r:ℝ) : ℕ) : ℝ) := Nat.le_ceil _
    have hK_lt : ((Nat.ceil (r:ℝ) : ℕ) : ℝ) < (r:ℝ) + 1 :=
      Nat.ceil_lt_add_one hr0
    have hK1 : (1:ℝ) ≤ ((Nat.ceil (r:ℝ) : ℕ) : ℝ) := hr1'.trans hrK
    have hK_2r : ((Nat.ceil (r:ℝ) : ℕ) : ℝ) ≤ 2*(r:ℝ) := by linarith
    let D : Fin (Nat.ceil (r:ℝ)) → ℝ := fun k =>
      min (2*(r:ℝ)) (Real.sqrt (2*(r:ℝ) * (2:ℝ)^((k:ℕ)*q)))
    have hDint : ∀ k : Fin (Nat.ceil (r:ℝ)), Integrable (fun ω : TwoCloudSpace q =>
        ∑ c : Fin q → Fin (2 ^ (k:ℕ)),
          |(partitionCount ((dyadicCell q (k:ℕ)) ∘
              (fun i : Fin (sourceCount ω) => cubeTruncPoint (sourcePoint ω (i:ℕ)))) c : ℝ) -
            (partitionCount ((dyadicCell q (k:ℕ)) ∘
              (fun j : Fin (targetCount ω) => cubeTruncPoint (targetPoint ω (j:ℕ)))) c : ℝ)|)
        (twoCloudLaw q r) := by
      intro k
      exact integrable_truncCellDiscrepancy q (k:ℕ) r
    have hDbound : ∀ k : Fin (Nat.ceil (r:ℝ)),
        ∫ ω, (∑ c : Fin q → Fin (2 ^ (k:ℕ)),
          |(partitionCount ((dyadicCell q (k:ℕ)) ∘
              (fun i : Fin (sourceCount ω) => cubeTruncPoint (sourcePoint ω (i:ℕ)))) c : ℝ) -
            (partitionCount ((dyadicCell q (k:ℕ)) ∘
              (fun j : Fin (targetCount ω) => cubeTruncPoint (targetPoint ω (j:ℕ)))) c : ℝ)|)
          ∂(twoCloudLaw q r) ≤ D k := by
      intro k
      exact integral_truncCellDiscrepancy_le q (k:ℕ) r
    have hshift := integral_shiftedValue_le_hier q r hG0 hg hgb t hKpos D hDint hDbound
    have hle_ae : poissonCubeTilted q (r:ℝ) g t ≤ᵐ[twoCloudLaw q r]
        fun ω => cloudValueNat (fun ω i j => truncatedEdgeCost q (r:ℝ) g t ω i j + |t| * G)
          sourceCount targetCount ω := by
      filter_upwards [cloudValueNat_truncated_eq_tilted_ae q r g t] with ω hω
      rw [← hω, cloudValueNat_shifted_eq]
      have hnonneg : 0 ≤ ((min (sourceCount ω) (targetCount ω) : ℕ) : ℝ) * (|t| * G) :=
        mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (abs_nonneg _) hG0)
      linarith
    have hstep : poissonCubePressure q r g t ≤
        ∫ ω, cloudValueNat (fun ω i j => truncatedEdgeCost q (r:ℝ) g t ω i j + |t| * G)
          sourceCount targetCount ω ∂(twoCloudLaw q r) := by
      unfold poissonCubePressure
      exact integral_mono_ae (integrable_poissonCubeTilted q r hG0 hg hgb t)
        (integrable_shiftedValue q r hG0 hg hgb t) hle_ae
    set B : ℝ := |t| * G with hBdef
    have hB0 : 0 ≤ B := mul_nonneg (abs_nonneg _) hG0
    have hbase := base_discrepancy_bound q (Nat.ceil (r:ℝ)) hqpos_nat hr1' hrK
      (B := B)
    have hseries1 : (1/2) * ∑ k : Fin (Nat.ceil (r:ℝ)),
        (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * D k ≤ 2 * C₀ * (r:ℝ) := by
      have h := series_min_part_le q (Nat.ceil (r:ℝ)) hq hr1' hK1 hrK hK_2r hC₀ hC₀0
      simpa only [D] using h
    have hseries2 := series_sqrt_part_le q (Nat.ceil (r:ℝ)) hq hr1'
    have hsum_split : (1/2) * ∑ k : Fin (Nat.ceil (r:ℝ)),
        (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * (D k + Real.sqrt (2*(r:ℝ)))
        = (1/2) * ∑ k : Fin (Nat.ceil (r:ℝ)),
            (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * D k
          + (1/2) * ∑ k : Fin (Nat.ceil (r:ℝ)),
            (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * Real.sqrt (2*(r:ℝ)) := by
      have h1 : ∑ k : Fin (Nat.ceil (r:ℝ)),
          (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * (D k + Real.sqrt (2*(r:ℝ)))
          = ∑ k : Fin (Nat.ceil (r:ℝ)),
              (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * D k
            + ∑ k : Fin (Nat.ceil (r:ℝ)),
              (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * Real.sqrt (2*(r:ℝ)) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro k _
        ring
      rw [h1, mul_add]
    have hmiddle : poissonCubePressure q r g t ≤
        (8*(q:ℝ)*(r:ℝ) + 4*B*(r:ℝ)) + (2*C₀*(r:ℝ) + (16/3)*(q:ℝ)*Real.sqrt 2*(r:ℝ)) := by
      calc poissonCubePressure q r g t
          ≤ ∫ ω, cloudValueNat (fun ω i j => truncatedEdgeCost q (r:ℝ) g t ω i j + |t| * G)
              sourceCount targetCount ω ∂(twoCloudLaw q r) := hstep
        _ ≤ (r^(2/(q:ℝ)) * (4*(q:ℝ) * (1/4:ℝ)^(Nat.ceil (r:ℝ))) + 2*B) *
              (2*(r:ℝ)) +
            (1/2) * ∑ k : Fin (Nat.ceil (r:ℝ)),
              (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) *
                (D k + Real.sqrt (2*(r:ℝ))) := hshift
        _ = (r^(2/(q:ℝ)) * (4*(q:ℝ) * (1/4:ℝ)^(Nat.ceil (r:ℝ))) + 2*B) *
              (2*(r:ℝ)) +
            ((1/2) * ∑ k : Fin (Nat.ceil (r:ℝ)),
                (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * D k
              + (1/2) * ∑ k : Fin (Nat.ceil (r:ℝ)),
                (r^(2/(q:ℝ)) * (8*(q:ℝ) * (1/4:ℝ)^(k:ℕ))) * Real.sqrt (2*(r:ℝ))) := by
            rw [hsum_split]
        _ ≤ (8*(q:ℝ)*(r:ℝ) + 4*B*(r:ℝ)) + (2*C₀*(r:ℝ) + (16/3)*(q:ℝ)*Real.sqrt 2*(r:ℝ)) := by
            linarith [hbase, hseries1, hseries2]
    have hcoef0 : (0:ℝ) ≤ 8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2 := by
      have hq0 : (0:ℝ) ≤ (q:ℝ) := Nat.cast_nonneg q
      have h1 : (0:ℝ) ≤ 8*(q:ℝ) := by positivity
      have h2 : (0:ℝ) ≤ 2*C₀ := by linarith
      have h3 : (0:ℝ) ≤ (16/3)*(q:ℝ)*Real.sqrt 2 := by positivity
      linarith
    have hAB : (8*(q:ℝ)*(r:ℝ) + 4*B*(r:ℝ)) +
          (2*C₀*(r:ℝ) + (16/3)*(q:ℝ)*Real.sqrt 2*(r:ℝ))
        = (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (r:ℝ) + 4*B*(r:ℝ) := by ring
    have hfin : (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (r:ℝ) + 4*B*(r:ℝ)
        ≤ (8*(q:ℝ) + 4 + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) * (r:ℝ) := by
      have h1B : (1:ℝ) ≤ 1 + B := by linarith
      have hAr : (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (r:ℝ)
          ≤ (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) * (r:ℝ) := by
        have hle : (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2)
            ≤ (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) := by
          calc (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2)
              = (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * 1 := by ring
            _ ≤ (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) :=
                mul_le_mul_of_nonneg_left h1B hcoef0
        exact mul_le_mul_of_nonneg_right hle hr0
      have hBr : 4*B*(r:ℝ) ≤ 4*(1 + B)*(r:ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hr0
        linarith
      have hsum : (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (r:ℝ) + 4*B*(r:ℝ)
          ≤ (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) * (r:ℝ)
            + 4*(1 + B)*(r:ℝ) := add_le_add hAr hBr
      calc (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (r:ℝ) + 4*B*(r:ℝ)
          ≤ (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) * (r:ℝ)
            + 4*(1 + B)*(r:ℝ) := hsum
        _ = (8*(q:ℝ) + 4 + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) * (r:ℝ) := by ring
    calc poissonCubePressure q r g t
        ≤ (8*(q:ℝ)*(r:ℝ) + 4*B*(r:ℝ)) +
            (2*C₀*(r:ℝ) + (16/3)*(q:ℝ)*Real.sqrt 2*(r:ℝ)) := hmiddle
      _ = (8*(q:ℝ) + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (r:ℝ) + 4*B*(r:ℝ) := hAB
      _ ≤ (8*(q:ℝ) + 4 + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + B) * (r:ℝ) := hfin
      _ = (8*(q:ℝ) + 4 + 2*C₀ + (16/3)*(q:ℝ)*Real.sqrt 2) * (1 + |t| * G) * (r:ℝ) := by
          rw [hBdef]

end OTSelector.Probability
