import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Binomial
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance
import OTSelector.Probability.BinomialDeviation
import OTSelector.Probability.BinomialPoissonExpectation

/-!
Conditions: Actual independent equal-parameter binomial counts, finite cell weights summing to one, and q>4 for the deterministic repair-scale limit.

Objects: Mean pair discrepancy≤sqrt(2nw), its finite-cell square-root sum bound and vanishing normalized repair error.

Proof detail: Evaluate the true difference second moment and apply weighted Cauchy-Schwarz. Apply finite Cauchy-Schwarz over cell weights and compute the resulting positive-power asymptotic for q>4.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.1)–(1.3), p. 1, and descending factorial definition (1.6), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.3, p. 29.
Relation: A finite binomial discrepancy calculation plus a separate deterministic scaling limit. It makes no Poisson-law approximation or random selected-cell independence claim.
-/


/-!
# Binomial count discrepancy

For two independent `Bin(n, w)` counts, the mean absolute difference is at most
`sqrt (2 n w)`.  The proof applies Cauchy--Schwarz to the two-dimensional mass
sum and evaluates the second difference moment from the binomial variance.  This
is the count-repair input for the finite-tile comparison at fixed sample size:
the expected discrepancy in a tile of mass `w` is `O(sqrt (n w))`, hence
`o(n)` after the kinetic scaling for `q > 4`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal unitInterval Topology

noncomputable section
namespace OTSelector.Probability

/-- **Mean absolute difference of two independent binomial counts.** -/
theorem binomialMass_double_sum_abs_sub_le (n : ℕ) (w : I) :
    (∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n w m * binomialMass n w k *
          |((m : ℝ) - (k : ℝ))|) ≤
      Real.sqrt (2 * (n : ℝ) * (w : ℝ)) := by
  classical
  set s : Finset ℕ := Finset.range (n + 1) with hs
  set b : ℕ → ℝ := binomialMass n w with hb
  set μ : ℝ := (n : ℝ) * (w : ℝ) with hμ
  have hb0 : ∀ k, 0 ≤ b k := fun k => binomialMass_nonneg n w k
  have hb0' : ∀ p : ℕ × ℕ, 0 ≤ b p.1 * b p.2 := fun p =>
    mul_nonneg (hb0 p.1) (hb0 p.2)
  have hsum1 : (∑ k ∈ s, b k) = 1 := by
    simpa only [hs, hb] using binomialMass_sum_one n w
  have hvar : (∑ k ∈ s, b k * ((k : ℝ) - μ) ^ 2) = μ * (1 - (w : ℝ)) := by
    simpa only [hs, hb, hμ] using binomialMass_sum_variance n w
  have hmean : (∑ k ∈ s, b k * (k : ℝ)) = μ := by
    simpa only [hs, hb, hμ] using binomialMass_sum_mul n w
  have hcenter : (∑ k ∈ s, b k * ((k : ℝ) - μ)) = 0 := by
    have hsplit : (∑ k ∈ s, b k * ((k : ℝ) - μ)) =
        (∑ k ∈ s, b k * (k : ℝ)) - μ * (∑ k ∈ s, b k) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hsplit, hmean, hsum1, mul_one, sub_self]
  -- The second difference moment.
  have hA : (∑ m ∈ s, ∑ k ∈ s, b m * b k * ((m : ℝ) - μ) ^ 2) = μ * (1 - (w : ℝ)) := by
    have hfac : (∑ m ∈ s, ∑ k ∈ s, b m * b k * ((m : ℝ) - μ) ^ 2) =
        (∑ m ∈ s, b m * ((m : ℝ) - μ) ^ 2) * (∑ k ∈ s, b k) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hfac, hvar, hsum1, mul_one]
  have hB : (∑ m ∈ s, ∑ k ∈ s, b m * b k * ((k : ℝ) - μ) ^ 2) = μ * (1 - (w : ℝ)) := by
    have hfac : (∑ m ∈ s, ∑ k ∈ s, b m * b k * ((k : ℝ) - μ) ^ 2) =
        (∑ m ∈ s, b m) * (∑ k ∈ s, b k * ((k : ℝ) - μ) ^ 2) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hfac, hsum1, one_mul, hvar]
  have hC : (∑ m ∈ s, ∑ k ∈ s, b m * b k * (((m : ℝ) - μ) * ((k : ℝ) - μ))) = 0 := by
    have hfac : (∑ m ∈ s, ∑ k ∈ s, b m * b k * (((m : ℝ) - μ) * ((k : ℝ) - μ))) =
        (∑ m ∈ s, b m * ((m : ℝ) - μ)) * (∑ k ∈ s, b k * ((k : ℝ) - μ)) := by
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [hfac, hcenter, mul_zero]
  have hquad : (∑ m ∈ s, ∑ k ∈ s, b m * b k * ((m : ℝ) - (k : ℝ)) ^ 2) =
      2 * (μ * (1 - (w : ℝ))) := by
    have hpt : ∀ m k : ℕ, b m * b k * ((m : ℝ) - (k : ℝ)) ^ 2 =
        b m * b k * ((m : ℝ) - μ) ^ 2 + b m * b k * ((k : ℝ) - μ) ^ 2 -
          2 * (b m * b k * (((m : ℝ) - μ) * ((k : ℝ) - μ))) := by
      intro m k
      have hd : ((m : ℝ) - (k : ℝ)) = ((m : ℝ) - μ) - ((k : ℝ) - μ) := by ring
      rw [hd]
      ring
    have hC2 : (∑ m ∈ s, ∑ k ∈ s,
        2 * (b m * b k * (((m : ℝ) - μ) * ((k : ℝ) - μ)))) = 0 := by
      have hfac : (∑ m ∈ s, ∑ k ∈ s,
          2 * (b m * b k * (((m : ℝ) - μ) * ((k : ℝ) - μ)))) =
          2 * (∑ m ∈ s, ∑ k ∈ s,
            b m * b k * (((m : ℝ) - μ) * ((k : ℝ) - μ))) := by
        simp only [Finset.mul_sum]
      rw [hfac, hC, mul_zero]
    simp_rw [hpt]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, hA, hB, hC2]
    ring
  -- Cauchy--Schwarz on the pair index.
  have hprod : (∑ m ∈ s, ∑ k ∈ s, b m * b k * |((m : ℝ) - (k : ℝ))|) =
      ∑ p ∈ s.product s, b p.1 * b p.2 * |((p.1 : ℝ) - (p.2 : ℝ))| :=
    (Finset.sum_product s s
      (fun p : ℕ × ℕ => b p.1 * b p.2 * |((p.1 : ℝ) - (p.2 : ℝ))|)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := s.product s)
    (f := fun p : ℕ × ℕ => Real.sqrt (b p.1 * b p.2))
    (g := fun p : ℕ × ℕ => Real.sqrt (b p.1 * b p.2) * |((p.1 : ℝ) - (p.2 : ℝ))|)
  have hleft : (∑ p ∈ s.product s, Real.sqrt (b p.1 * b p.2) *
      (Real.sqrt (b p.1 * b p.2) * |((p.1 : ℝ) - (p.2 : ℝ))|)) =
      ∑ p ∈ s.product s, b p.1 * b p.2 * |((p.1 : ℝ) - (p.2 : ℝ))| := by
    apply Finset.sum_congr rfl
    intro p _
    rw [← mul_assoc, Real.mul_self_sqrt (hb0' p)]
  have hf2 : (∑ p ∈ s.product s, (Real.sqrt (b p.1 * b p.2)) ^ 2) = 1 := by
    have : (∑ p ∈ s.product s, (Real.sqrt (b p.1 * b p.2)) ^ 2) =
        ∑ p ∈ s.product s, b p.1 * b p.2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Real.sq_sqrt (hb0' p)]
    rw [this]
    have hprod2 : (∑ p ∈ s.product s, b p.1 * b p.2) = ∑ m ∈ s, ∑ k ∈ s, b m * b k :=
      Finset.sum_product s s (fun p : ℕ × ℕ => b p.1 * b p.2)
    rw [hprod2]
    have hfac : (∑ m ∈ s, ∑ k ∈ s, b m * b k) = (∑ m ∈ s, b m) * (∑ k ∈ s, b k) := by
      rw [Finset.sum_mul_sum]
    rw [hfac, hsum1, mul_one]
  have hg2 : (∑ p ∈ s.product s,
      (Real.sqrt (b p.1 * b p.2) * |((p.1 : ℝ) - (p.2 : ℝ))|) ^ 2) =
      2 * (μ * (1 - (w : ℝ))) := by
    have : (∑ p ∈ s.product s,
        (Real.sqrt (b p.1 * b p.2) * |((p.1 : ℝ) - (p.2 : ℝ))|) ^ 2) =
        ∑ p ∈ s.product s, b p.1 * b p.2 * ((p.1 : ℝ) - (p.2 : ℝ)) ^ 2 := by
      apply Finset.sum_congr rfl
      intro p _
      rw [mul_pow, Real.sq_sqrt (hb0' p), sq_abs]
    rw [this]
    have hprod3 : (∑ p ∈ s.product s, b p.1 * b p.2 * ((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) =
        ∑ m ∈ s, ∑ k ∈ s, b m * b k * ((m : ℝ) - (k : ℝ)) ^ 2 :=
      Finset.sum_product s s
        (fun p : ℕ × ℕ => b p.1 * b p.2 * ((p.1 : ℝ) - (p.2 : ℝ)) ^ 2)
    rw [hprod3]
    exact hquad
  have hS0 : 0 ≤ ∑ m ∈ s, ∑ k ∈ s, b m * b k * |((m : ℝ) - (k : ℝ))| :=
    Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (hb0 m) (hb0 k)) (abs_nonneg _)
  have hsq : ((∑ m ∈ s, ∑ k ∈ s, b m * b k * |((m : ℝ) - (k : ℝ))|)) ^ 2 ≤
      2 * (n : ℝ) * (w : ℝ) := by
    calc ((∑ m ∈ s, ∑ k ∈ s, b m * b k * |((m : ℝ) - (k : ℝ))|)) ^ 2
        = ((∑ p ∈ s.product s,
            Real.sqrt (b p.1 * b p.2) *
              (Real.sqrt (b p.1 * b p.2) * |((p.1 : ℝ) - (p.2 : ℝ))|))) ^ 2 := by
          rw [hleft, hprod]
      _ ≤ (∑ p ∈ s.product s, (Real.sqrt (b p.1 * b p.2)) ^ 2) *
            (∑ p ∈ s.product s,
              (Real.sqrt (b p.1 * b p.2) * |((p.1 : ℝ) - (p.2 : ℝ))|) ^ 2) := hcs
      _ = 2 * (μ * (1 - (w : ℝ))) := by rw [hf2, hg2, one_mul]
      _ ≤ 2 * (n : ℝ) * (w : ℝ) := by
          rw [hμ]
          have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have hw0 : (0 : ℝ) ≤ (w : ℝ) := w.2.1
          have h1 : (1 : ℝ) - (w : ℝ) ≤ 1 := by linarith [w.2.2]
          have h2 : (n : ℝ) * (w : ℝ) * (1 - (w : ℝ)) ≤ (n : ℝ) * (w : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hn hw0)
          calc 2 * ((n : ℝ) * (w : ℝ) * (1 - (w : ℝ)))
              ≤ 2 * ((n : ℝ) * (w : ℝ) * 1) := by linarith
            _ = 2 * (n : ℝ) * (w : ℝ) := by ring
  calc (∑ m ∈ s, ∑ k ∈ s, b m * b k * |((m : ℝ) - (k : ℝ))|)
      = Real.sqrt (((∑ m ∈ s, ∑ k ∈ s, b m * b k * |((m : ℝ) - (k : ℝ))|)) ^ 2) :=
        (Real.sqrt_sq hS0).symm
    _ ≤ Real.sqrt (2 * (n : ℝ) * (w : ℝ)) := Real.sqrt_le_sqrt hsq


/-- **Multi-cell binomial discrepancy.**  For a finite family of cells whose
weights sum to one, the total expected count discrepancy of the independent
`Bin(n, w c)` pairs is at most `sqrt (2 n #C)`. -/
theorem sum_binomialMass_double_sum_abs_sub_le
    {C : Type*} [Fintype C] (w : C → I) (hw : ∑ c, (w c : ℝ) = 1) (n : ℕ) :
    (∑ c : C, ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n (w c) m * binomialMass n (w c) k *
          |((m : ℝ) - (k : ℝ))|) ≤
      Real.sqrt (2 * (n : ℝ) * (Fintype.card C : ℝ)) := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hw0 : ∀ c, (0 : ℝ) ≤ (w c : ℝ) := fun c => (w c).2.1
  -- Per-cell bound, then factor the square root.
  have hstep : (∑ c : C, ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n (w c) m * binomialMass n (w c) k *
          |((m : ℝ) - (k : ℝ))|) ≤
      ∑ c : C, Real.sqrt (2 * (n : ℝ) * (w c : ℝ)) :=
    Finset.sum_le_sum fun c _ => binomialMass_double_sum_abs_sub_le n (w c)
  have hfac : (∑ c : C, Real.sqrt (2 * (n : ℝ) * (w c : ℝ))) =
      Real.sqrt (2 * (n : ℝ)) * ∑ c : C, Real.sqrt ((w c : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))]
  -- Cauchy--Schwarz on the weights.
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun _ : C => (1 : ℝ)) (g := fun c : C => Real.sqrt ((w c : ℝ)))
  have hsq : ((∑ c : C, Real.sqrt ((w c : ℝ)))) ^ 2 ≤ (Fintype.card C : ℝ) := by
    calc ((∑ c : C, Real.sqrt ((w c : ℝ)))) ^ 2
        = (∑ c ∈ Finset.univ, (1 : ℝ) * Real.sqrt ((w c : ℝ))) ^ 2 := by simp
      _ ≤ (∑ _c ∈ Finset.univ, (1 : ℝ) ^ 2) *
            ∑ c ∈ Finset.univ, (Real.sqrt ((w c : ℝ))) ^ 2 := hcs
      _ = (Fintype.card C : ℝ) * 1 := by
          have h1 : (∑ _c ∈ (Finset.univ : Finset C), (1 : ℝ) ^ 2) = (Fintype.card C : ℝ) := by
            simp
          have h2 : (∑ c ∈ Finset.univ, (Real.sqrt ((w c : ℝ))) ^ 2) = 1 := by
            calc (∑ c ∈ Finset.univ, (Real.sqrt ((w c : ℝ))) ^ 2)
                = ∑ c : C, (w c : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro c _
                  rw [Real.sq_sqrt (hw0 c)]
              _ = 1 := by simpa using hw
          rw [h1, h2, mul_one]
      _ = (Fintype.card C : ℝ) := mul_one _
  have hsum0 : 0 ≤ ∑ c : C, Real.sqrt ((w c : ℝ)) :=
    Finset.sum_nonneg fun c _ => Real.sqrt_nonneg _
  have hsum_le : (∑ c : C, Real.sqrt ((w c : ℝ))) ≤
      Real.sqrt (Fintype.card C : ℝ) := by
    calc (∑ c : C, Real.sqrt ((w c : ℝ)))
        = Real.sqrt (((∑ c : C, Real.sqrt ((w c : ℝ)))) ^ 2) :=
          (Real.sqrt_sq hsum0).symm
      _ ≤ Real.sqrt (Fintype.card C : ℝ) := Real.sqrt_le_sqrt hsq
  calc (∑ c : C, ∑ m ∈ Finset.range (n + 1), ∑ k ∈ Finset.range (n + 1),
        binomialMass n (w c) m * binomialMass n (w c) k *
          |((m : ℝ) - (k : ℝ))|)
      ≤ ∑ c : C, Real.sqrt (2 * (n : ℝ) * (w c : ℝ)) := hstep
    _ = Real.sqrt (2 * (n : ℝ)) * ∑ c : C, Real.sqrt ((w c : ℝ)) := hfac
    _ ≤ Real.sqrt (2 * (n : ℝ)) * Real.sqrt (Fintype.card C : ℝ) := by
        exact mul_le_mul_of_nonneg_left hsum_le (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * (n : ℝ) * (Fintype.card C : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))]


/-- **Vanishing normalized repair error at fixed sample size.**  The tile-count
discrepancy, multiplied by the kinetic edge bound and divided by the sample
size, vanishes for `q > 4`. -/
theorem tendsto_binomial_repairError_zero {q : ℕ} (hq : 4 < q)
    (A G t : ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ =>
      (((n : ℝ) ^ (2 / (q : ℝ)) * A + |t| * G) / (n : ℝ)) *
        (Real.sqrt (2 * (n : ℝ) * (k : ℝ)) / 2)) atTop (𝓝 0) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : 0 < q := by omega
    exact_mod_cast this
  have hq4 : (4 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hexp : (2 : ℝ) / (q : ℝ) - 1 / 2 < 0 := by
    have hlt : 2 / (q : ℝ) < 1 / 2 := by
      rw [div_lt_iff₀ hq0]
      nlinarith
    linarith
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := -(2 / (q : ℝ) - 1 / 2)) (by linarith)
    have h' := h.comp tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, neg_neg] using h'
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop
  have hlim : Tendsto (fun n : ℕ =>
      A * (Real.sqrt (2 * (k : ℝ)) / 2) * (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) +
        |t| * G * (Real.sqrt (2 * (k : ℝ)) / 2) * (n : ℝ) ^ (-(1 / 2 : ℝ)))
      atTop (𝓝 0) := by
    have h := (h1.const_mul (A * (Real.sqrt (2 * (k : ℝ)) / 2))).add
      (h2.const_mul (|t| * G * (Real.sqrt (2 * (k : ℝ)) / 2)))
    simpa only [mul_zero, add_zero] using h
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := hnpos.le
  have hsqrt : Real.sqrt (2 * (n : ℝ) * (k : ℝ)) =
      Real.sqrt (2 * (k : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) := by
    rw [show (2 * (n : ℝ) * (k : ℝ)) = (2 * (k : ℝ)) * (n : ℝ) by ring]
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (k : ℝ)),
      Real.sqrt_eq_rpow (x := (n : ℝ))]
  have hinv : (n : ℝ)⁻¹ = (n : ℝ) ^ (-1 : ℝ) := by
    rw [Real.rpow_neg hn0, Real.rpow_one]
  have hpow1 : (n : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) =
      (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) := by
    rw [← Real.rpow_add hnpos, div_eq_mul_inv, hinv, ← Real.rpow_add hnpos]
    congr 1
    ring
  have hpow2 : (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [div_eq_mul_inv, hinv, ← Real.rpow_add hnpos]
    congr 1
    ring
  rw [hsqrt]
  have hgoal : ((n : ℝ) ^ (2 / (q : ℝ)) * A + |t| * G) / (n : ℝ) *
        (Real.sqrt (2 * (k : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) / 2) =
      A * (Real.sqrt (2 * (k : ℝ)) / 2) *
          ((n : ℝ) ^ (2 / (q : ℝ)) * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ)) +
        |t| * G * (Real.sqrt (2 * (k : ℝ)) / 2) *
          ((n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ)) := by
    field_simp [hnpos.ne']
  rw [hgoal, hpow1, hpow2]


/-- The sum of the per-cell square-root discrepancies is at most the square
root of the total discrepancy. -/
theorem sum_sqrt_two_mul_weight_le {C : Type*} [Fintype C]
    (w : C → I) (hw : ∑ c, (w c : ℝ) = 1) (n : ℕ) :
    (∑ c : C, Real.sqrt (2 * (n : ℝ) * (w c : ℝ))) ≤
      Real.sqrt (2 * (n : ℝ) * (Fintype.card C : ℝ)) := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hw0 : ∀ c, (0 : ℝ) ≤ (w c : ℝ) := fun c => (w c).2.1
  have hfac : (∑ c : C, Real.sqrt (2 * (n : ℝ) * (w c : ℝ))) =
      Real.sqrt (2 * (n : ℝ)) * ∑ c : C, Real.sqrt ((w c : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro c _
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ)
    (f := fun _ : C => (1 : ℝ)) (g := fun c : C => Real.sqrt ((w c : ℝ)))
  have hsq : ((∑ c : C, Real.sqrt ((w c : ℝ)))) ^ 2 ≤ (Fintype.card C : ℝ) := by
    calc ((∑ c : C, Real.sqrt ((w c : ℝ)))) ^ 2
        = (∑ c ∈ Finset.univ, (1 : ℝ) * Real.sqrt ((w c : ℝ))) ^ 2 := by simp
      _ ≤ (∑ _c ∈ (Finset.univ : Finset C), (1 : ℝ) ^ 2) *
            ∑ c ∈ Finset.univ, (Real.sqrt ((w c : ℝ))) ^ 2 := hcs
      _ = (Fintype.card C : ℝ) * 1 := by
          have h1 : (∑ _c ∈ (Finset.univ : Finset C), (1 : ℝ) ^ 2) =
              (Fintype.card C : ℝ) := by simp
          have h2 : (∑ c ∈ Finset.univ, (Real.sqrt ((w c : ℝ))) ^ 2) = 1 := by
            calc (∑ c ∈ Finset.univ, (Real.sqrt ((w c : ℝ))) ^ 2)
                = ∑ c : C, (w c : ℝ) := by
                  apply Finset.sum_congr rfl
                  intro c _
                  rw [Real.sq_sqrt (hw0 c)]
              _ = 1 := by simpa using hw
          rw [h1, h2, mul_one]
      _ = (Fintype.card C : ℝ) := mul_one _
  have hsum0 : 0 ≤ ∑ c : C, Real.sqrt ((w c : ℝ)) :=
    Finset.sum_nonneg fun c _ => Real.sqrt_nonneg _
  have hsum_le : (∑ c : C, Real.sqrt ((w c : ℝ))) ≤ Real.sqrt (Fintype.card C : ℝ) := by
    calc (∑ c : C, Real.sqrt ((w c : ℝ)))
        = Real.sqrt (((∑ c : C, Real.sqrt ((w c : ℝ)))) ^ 2) :=
          (Real.sqrt_sq hsum0).symm
      _ ≤ Real.sqrt (Fintype.card C : ℝ) := Real.sqrt_le_sqrt hsq
  rw [hfac]
  calc Real.sqrt (2 * (n : ℝ)) * (∑ c : C, Real.sqrt ((w c : ℝ)))
      ≤ Real.sqrt (2 * (n : ℝ)) * Real.sqrt (Fintype.card C : ℝ) :=
        mul_le_mul_of_nonneg_left hsum_le (Real.sqrt_nonneg _)
    _ = Real.sqrt (2 * (n : ℝ) * (Fintype.card C : ℝ)) := by
        rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * (n : ℝ))]

end OTSelector.Probability
