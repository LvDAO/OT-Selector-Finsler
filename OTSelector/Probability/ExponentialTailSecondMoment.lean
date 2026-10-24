import OTSelector.MeasureTheory.Lp.SecondMomentNorm
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CountTailTrafficSecondMoment.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CountTailTrafficSecondMoment`; the selected original proof blocks follow. -/
section

/-!
# Probability.ExponentialTailSecondMoment

## Lemma skeleton

* **Conditions:** A measurable nonnegative count-like real observable with integrable exponential, and traffic bounded by B times that observable on its upper tail.
* **Objects:** Tail traffic L2, exponential second-moment decay and the corresponding norm decay.
* **Proof detail:** Use x²<=8 exp(x/2), absorb the tail threshold into exp(-K/2), dominate the tail square by the actual count exponential and take its L2 square root.

## Mathematical sources

- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=37): Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=233): Section 8A, Theorem 8.11, p. 218; Example 8.14, p. 219 (L2 Cauchy–Schwarz).
- [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=99): Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.

Source relation (composition): Direct exponential-envelope moment comparison; no law is assigned to adaptively selected edges and the numeric constant eight is proved locally.
-/

/-! A genuine original count exponential moment controls bounded-phase bad
traffic directly, without assigning any law to adaptively selected matching edges. -/
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

/-- The nonnegative count square is controlled by its own half-exponential. -/
theorem sq_le_eight_mul_exp_half {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 ≤ 8 * Real.exp (x / 2) := by
  have h := Real.pow_div_factorial_le_exp (x / 2) (show 0 ≤ x / 2 by positivity) 2
  norm_num at h
  nlinarith

/-- Above a count threshold, its square has an explicit exponential saving
against the same full original input count exponential moment. -/
theorem count_sq_le_exp_on_tail {x K : ℝ} (hx : 0 ≤ x) (hK : K < x) :
    x ^ 2 ≤ 8 * Real.exp (-K / 2) * Real.exp x := by
  have he : Real.exp (x / 2) ≤ Real.exp (-K / 2) * Real.exp x := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  exact (sq_le_eight_mul_exp_half hx).trans (by nlinarith)

/-- Actual traffic dominated by a multiple of the same original input count
on its large-count event is L2 there, with an explicit exponential mean-square
bound from the true original count exponential moment. -/
theorem countTail_traffic_memLp_two_and_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N : Ω → ℝ} (hN : Measurable N) (hN0 : ∀ s, 0 ≤ N s)
    (hExp : Integrable (fun s ↦ Real.exp (N s)) P)
    {T : Ω → ℝ} (hT : AEStronglyMeasurable T P) {B K : ℝ} (_hB : 0 ≤ B)
    (hbound : ∀ᵐ s ∂P, K < N s → |T s| ≤ B * N s) :
    MemLp ({s | K < N s}.indicator T) 2 P ∧
      (∫ s, ({z | K < N z}.indicator T s) ^ 2 ∂P) ≤
        (8 * B ^ 2 * Real.exp (-K / 2)) * ∫ s, Real.exp (N s) ∂P := by
  have hA : MeasurableSet {s | K < N s} := measurableSet_lt measurable_const hN
  have hmeas : AEStronglyMeasurable (fun s ↦ ({z | K < N z}.indicator T s) ^ 2) P :=
    (hT.indicator hA).pow 2
  have hdom : ∀ᵐ s ∂P, ({z | K < N z}.indicator T s) ^ 2 ≤
      (8 * B ^ 2 * Real.exp (-K / 2)) * Real.exp (N s) := by
    filter_upwards [hbound] with s hs
    by_cases hKs : K < N s
    · rw [indicator_of_mem (show s ∈ {z | K < N z} from hKs)]
      calc
        _ = |T s| ^ 2 := (sq_abs _).symm
        _ ≤ (B * N s) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hs hKs) 2
        _ = B ^ 2 * N s ^ 2 := mul_pow _ _ _
        _ ≤ B ^ 2 * (8 * Real.exp (-K / 2) * Real.exp (N s)) :=
          mul_le_mul_of_nonneg_left (count_sq_le_exp_on_tail (hN0 s) hKs) (sq_nonneg _)
        _ = _ := by ring
    · rw [indicator_of_notMem (show s ∉ {z | K < N z} from hKs), zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
      positivity
  have hI : Integrable (fun s ↦ ({z | K < N z}.indicator T s) ^ 2) P := by
    apply (hExp.const_mul (8 * B ^ 2 * Real.exp (-K / 2))).mono' hmeas
    filter_upwards [hdom] with s hs
    change |({z | K < N z}.indicator T s) ^ 2| ≤ _
    rw [abs_of_nonneg (sq_nonneg ({z | K < N z}.indicator T s))]
    exact hs
  refine ⟨(memLp_two_iff_integrable_sq (hT.indicator hA)).mpr hI, ?_⟩
  calc
    _ ≤ ∫ s, (8 * B ^ 2 * Real.exp (-K / 2)) * Real.exp (N s) ∂P :=
      integral_mono_ae hI (hExp.const_mul _) hdom
    _ = _ := integral_const_mul _ _

/-- The actual count tail has an explicit L2 exponential rate from a genuine
count exponential-moment upper bound. -/
theorem countTail_traffic_memLp_two_and_exponential_norm
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {N : Ω → ℝ} (hN : Measurable N) (hN0 : ∀ s, 0 ≤ N s)
    (hExp : Integrable (fun s ↦ Real.exp (N s)) P)
    {L : ℝ} (hExpBound : (∫ s, Real.exp (N s) ∂P) ≤ Real.exp L)
    {T : Ω → ℝ} (hT : AEStronglyMeasurable T P) {B K : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ s ∂P, K < N s → |T s| ≤ B * N s) :
    MemLp ({s | K < N s}.indicator T) 2 P ∧
      (∫ s, ({z | K < N z}.indicator T s) ^ 2 ∂P) ≤
        8 * B ^ 2 * Real.exp L * Real.exp (-K / 2) ∧
      eLpNorm ({s | K < N s}.indicator T) 2 P ≤
        ENNReal.ofReal (Real.sqrt 8 * B * Real.exp (L / 2) * Real.exp (-K / 4)) := by
  obtain ⟨hLp, hmean⟩ := countTail_traffic_memLp_two_and_second_moment P hN hN0 hExp hT hB hbound
  have hmean' : (∫ s, ({z | K < N z}.indicator T s) ^ 2 ∂P) ≤
      (8 * B ^ 2 * Real.exp (-K / 2)) * Real.exp L :=
    hmean.trans (mul_le_mul_of_nonneg_left hExpBound (by positivity))
  have hnorm := eLpNorm_two_le_sqrt_of_integral_sq_le hLp hmean'
  have hexp₁ : (Real.exp (L / 2)) ^ 2 = Real.exp L := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hexp₂ : (Real.exp (-K / 4)) ^ 2 = Real.exp (-K / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsq : (Real.sqrt 8 * B * Real.exp (L / 2) * Real.exp (-K / 4)) ^ 2 =
      (8 * B ^ 2 * Real.exp (-K / 2)) * Real.exp L := by
    simp only [mul_pow]
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8), hexp₁, hexp₂]
    ring
  have hroot : Real.sqrt ((8 * B ^ 2 * Real.exp (-K / 2)) * Real.exp L) =
      Real.sqrt 8 * B * Real.exp (L / 2) * Real.exp (-K / 4) := by
    apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).mpr
    simpa only [pow_two] using hsq.symm
  refine ⟨hLp, ?_, ?_⟩
  · convert hmean' using 1; ring
  · simpa only [hroot] using hnorm

end OTSelector.Probability

end
end
