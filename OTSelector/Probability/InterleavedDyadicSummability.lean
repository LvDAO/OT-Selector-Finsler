import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Two-scale summation of the complete interleaved birth-traffic estimate. -/
open Real
noncomputable section
namespace OTSelector.Probability

/-- The literal increasing exceptional-event threshold at the two dyadic levels. -/
def interleavedLevelThreshold (K₀ C : ℝ) (n j : ℕ) : ℝ :=
  K₀ + C * ((n : ℝ) + (j : ℝ) + 1)

/-- A square-root affine threshold cannot defeat positive geometric decay
in either level. The two levels are summed jointly, without independence. -/
theorem summable_sqrt_levelThreshold_geometric
    {K₀ C E ρ σ : ℝ} (hK₀ : 0 ≤ K₀) (hC : 0 ≤ C)
    (hE : 0 ≤ E) (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hσ : 0 ≤ σ) (hσ1 : σ < 1) :
    Summable (fun z : ℕ × ℕ ↦
      Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) * ρ ^ z.1 * σ ^ z.2) := by
  have hseq {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
      Summable (fun n : ℕ ↦ ((n : ℝ) + 1) * r ^ n) := by
    have hn : ‖r‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hr] using hr1
    simpa only [pow_one, add_mul, one_mul] using
      (summable_pow_mul_geometric_of_norm_lt_one 1 hn).add
        (summable_geometric_of_norm_lt_one hn)
  have hsum := ((hseq hρ hρ1).mul_of_nonneg (hseq hσ hσ1)
    (fun _ ↦ by positivity) (fun _ ↦ by positivity)).mul_left
      (Real.sqrt E * (K₀ + C + 1))
  apply hsum.of_nonneg_of_le (fun z ↦ by positivity)
  intro z
  have hn : 0 ≤ (z.1 : ℝ) := by positivity
  have hj : 0 ≤ (z.2 : ℝ) := by positivity
  have hK : 0 ≤ interleavedLevelThreshold K₀ C z.1 z.2 := by
    dsimp [interleavedLevelThreshold]
    positivity
  have hs : Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2) ≤
      interleavedLevelThreshold K₀ C z.1 z.2 + 1 := by
    nlinarith [Real.sq_sqrt hK,
      sq_nonneg (Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2) - 1 / 2)]
  have hlin : interleavedLevelThreshold K₀ C z.1 z.2 + 1 ≤
      (K₀ + C + 1) * ((z.1 : ℝ) + (z.2 : ℝ) + 1) := by
    dsimp [interleavedLevelThreshold]
    nlinarith [mul_nonneg hK₀ (add_nonneg hn hj)]
  have hprod : (z.1 : ℝ) + (z.2 : ℝ) + 1 ≤
      ((z.1 : ℝ) + 1) * ((z.2 : ℝ) + 1) := by nlinarith [mul_nonneg hn hj]
  have hbound := hs.trans (hlin.trans (mul_le_mul_of_nonneg_left hprod (by positivity)))
  rw [Real.sqrt_mul hK]
  have hfull := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbound (Real.sqrt_nonneg E))
    (mul_nonneg (pow_nonneg hρ z.1) (pow_nonneg hσ z.2))
  nlinarith only [hfull]

/-- The entire exceptional-event term, including the number of birth bands,
is summable for a sufficiently steep threshold. -/
theorem summable_interleaved_exceptional
    {K₀ C c : ℝ} (hdecay : Real.log 2 < c * C) :
    Summable (fun z : ℕ × ℕ ↦
      (2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2)) := by
  have hcc : 0 < c * C := lt_trans (Real.log_pos (by norm_num)) hdecay
  have hρ1 : Real.exp (-c * C) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hσ1 : 2 * Real.exp (-c * C) < 1 := by
    have heq : 2 * Real.exp (-c * C) = Real.exp (Real.log 2 - c * C) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num)]
      congr 1
      ring
    rw [heq]
    exact Real.exp_lt_one_iff.mpr (sub_neg.mpr hdecay)
  have hρ : Summable (fun n : ℕ ↦ Real.exp (-c * C) ^ n) :=
    summable_geometric_of_norm_lt_one (by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hρ1)
  have hσ : Summable (fun j : ℕ ↦ (2 * Real.exp (-c * C)) ^ j) :=
    summable_geometric_of_norm_lt_one (by
      simpa only [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 2 * Real.exp (-c * C))]
        using hσ1)
  have hs := (hρ.mul_of_nonneg hσ (fun _ ↦ by positivity) (fun _ ↦ by positivity)).mul_left
    (Real.exp (-c * (K₀ + C)))
  apply hs.congr
  intro z
  have heq : -c * interleavedLevelThreshold K₀ C z.1 z.2 =
      -c * (K₀ + C) + (z.1 : ℝ) * (-c * C) + (z.2 : ℝ) * (-c * C) := by
    dsimp [interleavedLevelThreshold]
    ring
  rw [heq, Real.exp_add, Real.exp_add, Real.exp_nat_mul, Real.exp_nat_mul, mul_pow]
  ring

/-- A positive dyadic power is exactly a constant times a geometric sequence. -/
theorem dyadicScale_rpow_eq_geometric {t : ℝ} (ht : 0 ≤ t) (a : ℝ) (n : ℕ) :
    (t / (2 : ℝ) ^ n) ^ a = t ^ a * ((2 : ℝ) ^ (-a)) ^ n := by
  rw [Real.div_rpow ht (by positivity),
    ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2), div_eq_mul_inv,
    ← inv_pow, ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]

/-- The two full birth-traffic terms and the complete exceptional term are
jointly summable in the literal physical endpoint and birth-distance scales. -/
theorem summable_interleaved_dyadic_birth_bound
    {K₀ C E t a b d c : ℝ} (hK₀ : 0 ≤ K₀) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (ht : 0 ≤ t) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hdecay : Real.log 2 < c * C) :
    Summable (fun z : ℕ × ℕ ↦
      Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) *
        ((t / (2 : ℝ) ^ z.1) ^ a * (1 / (2 : ℝ) ^ z.2) ^ (1 / 2 : ℝ) +
          (t / (2 : ℝ) ^ z.1) ^ b * (1 / (2 : ℝ) ^ z.2) ^ d) +
        (2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2)) := by
  have hgeo (v : ℝ) (hv : 0 < v) : (2 : ℝ) ^ (-v) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hv)
  have hfirst := (summable_sqrt_levelThreshold_geometric hK₀ hC hE
    (Real.rpow_nonneg (by norm_num) _) (hgeo a ha)
    (Real.rpow_nonneg (by norm_num) _) (hgeo (1 / 2) (by norm_num))).mul_left (t ^ a)
  have hsecond := (summable_sqrt_levelThreshold_geometric hK₀ hC hE
    (Real.rpow_nonneg (by norm_num) _) (hgeo b hb)
    (Real.rpow_nonneg (by norm_num) _) (hgeo d hd)).mul_left (t ^ b)
  have hall := (hfirst.add hsecond).add (summable_interleaved_exceptional (K₀ := K₀) hdecay)
  apply hall.congr
  intro z
  rw [dyadicScale_rpow_eq_geometric ht, dyadicScale_rpow_eq_geometric ht,
    dyadicScale_rpow_eq_geometric (by norm_num : (0 : ℝ) ≤ 1),
    dyadicScale_rpow_eq_geometric (by norm_num : (0 : ℝ) ≤ 1)]
  simp only [Real.one_rpow]
  ring

/-- A positive exponential-tail rate produces its own threshold slope. -/
theorem exists_summable_interleaved_dyadic_birth_bound
    {K₀ E t a b d c : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E)
    (ht : 0 ≤ t) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hc : 0 < c) :
    ∃ C > 0, Summable (fun z : ℕ × ℕ ↦
      Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) *
        ((t / (2 : ℝ) ^ z.1) ^ a * (1 / (2 : ℝ) ^ z.2) ^ (1 / 2 : ℝ) +
          (t / (2 : ℝ) ^ z.1) ^ b * (1 / (2 : ℝ) ^ z.2) ^ d) +
        (2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2)) := by
  let C := (Real.log 2 + 1) / c
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC : 0 < C := div_pos (by linarith) hc
  have hcc : c * C = Real.log 2 + 1 := by dsimp [C]; field_simp
  exact ⟨C, hC, summable_interleaved_dyadic_birth_bound hK₀ hC.le hE ht ha hb hd
    (by linarith)⟩

/-- The literal positive powers in the interleaved focal-birth argument all
sum, including the full exceptional band count. No selected-band independence
enters this analytic statement. -/
theorem exists_summable_original_interleaved_birth_levels
    {K₀ E t q k c : ℝ} (hK₀ : 0 ≤ K₀) (hE : 0 ≤ E) (ht : 0 ≤ t)
    (hq : 0 < q) (hk : 0 < k) (hc : 0 < c) :
    ∃ C > 0, Summable (fun z : ℕ × ℕ ↦
      Real.sqrt (interleavedLevelThreshold K₀ C z.1 z.2 * E) *
        ((t / (2 : ℝ) ^ z.1) ^ (1 / (2 * q)) * (1 / (2 : ℝ) ^ z.2) ^ (1 / 2 : ℝ) +
          (t / (2 : ℝ) ^ z.1) ^ (k / 8) *
            (1 / (2 : ℝ) ^ z.2) ^ (k / (4 * (3 * k + 4)))) +
        (2 : ℝ) ^ z.2 * Real.exp (-c * interleavedLevelThreshold K₀ C z.1 z.2)) :=
  exists_summable_interleaved_dyadic_birth_bound hK₀ hE ht
    (div_pos (by norm_num) (mul_pos (by norm_num) hq))
    (div_pos hk (by norm_num)) (div_pos hk (by positivity)) hc

end OTSelector.Probability
