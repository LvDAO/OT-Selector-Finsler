import LeanLevy.RandomMeasure.PoissonRandomMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Poisson.PoissonLimitThm
import Mathlib.Probability.Moments.Variance

/-!
Conditions: Natural binomial counts with np_n tending to a finite rate and functionals bounded in absolute value by a constant times count, or minimum of two counts; general helpers retain their explicit summable weighted majorants.

Objects: Pointwise binomial-to-Poisson masses, exact finite mass integrals and one/two-count expectation convergence for unbounded linearly growing readouts.

Proof detail: Bound binomial masses by (np)^k/k!, obtain a common summable count-weighted exponential-series majorant and truncate the finite sums. Pass each fixed mass to its Poisson limit, then remove the uniformly bounded tails.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.1)–(1.3), p. 1, and descending factorial definition (1.6), p. 2; Gunter Last; Mathew Penrose: Section 1.3, Proposition 1.4, pp. 4–5; Section 3.3, Theorem 3.9, pp. 23–24.
Relation: A bounded-intensity Poissonization theorem with explicit tail control. Weak convergence alone is not used to justify expectations of the unbounded count-linear functionals.
-/


/-!
# Binomial-to-Poisson transfer for linearly bounded functionals

A deterministic number of iid points in a small cell has a binomial count whose
mean tends to a fixed intensity while the cell shrinks.  Replacing the count by
a Poisson variable changes the expected value of any functional bounded by a
constant times the count by a vanishing amount.

The result is the bounded-intensity Poissonization step used to identify the
local frozen tile pressure with the marked Poisson pressure, in contrast with
the scale normalization used by the homogeneous pressure limit.

The proof compares binomial and Poisson masses pointwise (Mathlib's Poisson
limit theorem), then uses the elementary bound
`C(n,k) p^k (1-p)^(n-k) <= (n p)^k / k!` to control the weighted tails
uniformly in `n`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal NNReal Topology unitInterval

noncomputable section
namespace OTSelector.Probability

/-- The Poisson mass function in real form. -/
def poissonMass (r : ℝ≥0) (k : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ) ^ k / k.factorial

/-- The binomial mass function in real form. -/
def binomialMass (n : ℕ) (p : I) (k : ℕ) : ℝ :=
  (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)

/-- Integral of a real functional against the binomial law, as a finite sum. -/
theorem integral_binomial_real (n : ℕ) (p : I) (E : ℕ → ℝ) :
    ∫ m, E m ∂(ProbabilityTheory.binomial n p) =
      ∑ k ∈ Finset.range (n + 1), binomialMass n p k * E k := by
  rw [ProbabilityTheory.integral_binomial]
  rw [← Nat.range_succ_eq_Iic]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [binomialMass, smul_eq_mul]

/-- Pointwise convergence of binomial masses to Poisson masses. -/
theorem tendsto_binomialMass_poissonMass (p : ℕ → I) {r : ℝ}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 r)) (k : ℕ) :
    Tendsto (fun n : ℕ => binomialMass n (p n) k) atTop (𝓝 (Real.exp (-r) * r ^ k / k.factorial)) :=
  tendsto_choose_mul_pow_of_tendsto_mul_atTop (p := fun n => (p n : ℝ)) (r := r) k hr

/-- Nonnegativity of the binomial mass. -/
theorem binomialMass_nonneg (n : ℕ) (p : I) (k : ℕ) :
    0 ≤ binomialMass n p k := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  unfold binomialMass
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp0 k))
    (pow_nonneg (sub_nonneg.mpr hp1) _)

/-- The binomial mass is bounded by the corresponding Poisson-type term with
mean `n p`. -/
theorem binomialMass_le (n : ℕ) (p : I) (k : ℕ) :
    binomialMass n p k ≤ ((n : ℝ) * (p : ℝ)) ^ k / k.factorial := by
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.2.1
  have hp1 : (p : ℝ) ≤ 1 := p.2.2
  have hq0 : (0 : ℝ) ≤ 1 - (p : ℝ) := sub_nonneg.mpr hp1
  have hq1 : (1 - (p : ℝ)) ^ (n - k) ≤ 1 := by
    simpa using pow_le_one₀ hq0 (by linarith : (1 : ℝ) - (p : ℝ) ≤ 1)
  have hchoose : (n.choose k : ℝ) ≤ (n : ℝ) ^ k / k.factorial :=
    Nat.choose_le_pow_div k n
  have hpk : (0 : ℝ) ≤ (p : ℝ) ^ k := pow_nonneg hp0 k
  unfold binomialMass
  calc (n.choose k : ℝ) * (p : ℝ) ^ k * (1 - (p : ℝ)) ^ (n - k)
      ≤ ((n : ℝ) ^ k / k.factorial) * (p : ℝ) ^ k * 1 := by
        apply mul_le_mul
        · exact mul_le_mul hchoose le_rfl hpk (by positivity)
        · exact hq1
        · exact pow_nonneg hq0 _
        · exact mul_nonneg (by positivity) hpk
    _ = ((n : ℝ) * (p : ℝ)) ^ k / k.factorial := by
        rw [mul_pow]
        ring

/-- Poisson masses are nonnegative. -/
theorem poissonMass_nonneg (r : ℝ≥0) (k : ℕ) : 0 ≤ poissonMass r k := by
  unfold poissonMass
  positivity

/-- The Poisson mass is summable. -/
theorem summable_poissonMass (r : ℝ≥0) : Summable (poissonMass r) := by
  have h' : Summable (fun k : ℕ => (r : ℝ) ^ k / k.factorial) :=
    Real.summable_pow_div_factorial (r : ℝ)
  refine (h'.mul_left (Real.exp (-(r : ℝ)))).congr fun k => ?_
  unfold poissonMass
  rw [mul_div_assoc]

/-- The first moment of the Poisson mass is finite. -/
theorem summable_poissonMass_mul (r : ℝ≥0) :
    Summable (fun k : ℕ => poissonMass r k * k) := by
  have h := (integrable_poissonMeasure_iff.mp (integrable_id_poissonMeasure r) :
    Summable (fun n : ℕ => Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial * ‖(n : ℝ)‖))
  refine h.congr fun k => ?_
  rw [poissonMass, Real.norm_eq_abs, Nat.abs_cast]


/-- **Finite-mass comparison.**  If a sequence of nonnegative masses `qn n` is
eventually dominated by a summable majorant `g`, has first moments controlled by
`g`, and converges pointwise to a mass `q` with finite first moment, then for
any functional bounded by a constant times the index the finite sums converge to
the `tsum` against `q`. -/
private theorem tendsto_finset_sum_tsum_of_masses
    (q : ℕ → ℝ) (qn : ℕ → ℕ → ℝ) (E : ℕ → ℝ) (B : ℝ) (g : ℕ → ℝ)
    (hB : 0 ≤ B) (hE : ∀ k, |E k| ≤ B * (k : ℝ))
    (hg0 : ∀ k, 0 ≤ g k) (hgk : Summable (fun k => g k * (k : ℝ)))
    (hbound : ∀ᶠ n in atTop, ∀ k, qn n k ≤ g k)
    (hqn0 : ∀ n k, 0 ≤ qn n k)
    (hq0 : ∀ k, 0 ≤ q k) (hqk : Summable (fun k => q k * (k : ℝ)))
    (hconv : ∀ k, Tendsto (fun n => qn n k) atTop (𝓝 (q k)))
    (hqE : Summable (fun k => q k * E k)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), qn n k * E k) atTop
      (𝓝 (∑' k, q k * E k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (2 * B + 2) with hδdef
  have hδ : 0 < δ := by positivity
  -- Tails of the two majorant first moments.
  have htail_g : Tendsto (fun M : ℕ => ∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun k : ℕ => g k * (k : ℝ))
  have htail_q : Tendsto (fun M : ℕ => ∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun k : ℕ => q k * (k : ℝ))
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((htail_g.eventually (Iio_mem_nhds hδ)).and
      (htail_q.eventually (Iio_mem_nhds hδ)))
  have hMg : (∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ))) < δ :=
    (hM M le_rfl).1
  have hMq : (∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ))) < δ :=
    (hM M le_rfl).2
  -- Eventually the majorant holds and the finite part is small.
  have hfin : Tendsto (fun n =>
      ∑ k ∈ Finset.range M, (qn n k - q k) * E k) atTop (𝓝 0) := by
    have hterm : ∀ k ∈ Finset.range M,
        Tendsto (fun n => (qn n k - q k) * E k) atTop (𝓝 0) := by
      intro k _
      have hqk : Tendsto (fun n : ℕ => qn n k - q k) atTop (𝓝 (q k - q k)) :=
        (hconv k).sub tendsto_const_nhds
      have hEk : Tendsto (fun _ : ℕ => E k) atTop (𝓝 (E k)) := tendsto_const_nhds
      have h := hqk.mul hEk
      simpa using h
    simpa using tendsto_finsetSum (Finset.range M) hterm
  have hfin_ev : ∀ᶠ n in atTop,
      |∑ k ∈ Finset.range M, (qn n k - q k) * E k| < δ := by
    have hmem : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) hδ
    have h := hfin.eventually hmem
    filter_upwards [h] with n hn
    rw [abs_lt]
    exact hn
  -- The shifted tails.
  have hqE_shift : Summable (fun j : ℕ => q (j + M) * E (j + M)) :=
    (summable_nat_add_iff M).mpr hqE
  have hqk_shift : Summable (fun j : ℕ => q (j + M) * (((j + M : ℕ) : ℝ))) :=
    (summable_nat_add_iff M).mpr hqk
  have hgk_shift : Summable (fun j : ℕ => g (j + M) * (((j + M : ℕ) : ℝ))) :=
    (summable_nat_add_iff M).mpr hgk
  -- Bound on the shifted Poisson tail.
  have htail3 : |∑' j : ℕ, q (j + M) * E (j + M)| ≤
      B * (∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ))) := by
    have hnorm : Summable (fun j : ℕ => ‖q (j + M) * E (j + M)‖) := hqE_shift.norm
    have hmaj : Summable (fun j : ℕ => B * (q (j + M) * (((j + M : ℕ) : ℝ)))) :=
      hqk_shift.mul_left B
    calc |∑' j : ℕ, q (j + M) * E (j + M)|
        = ‖∑' j : ℕ, q (j + M) * E (j + M)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' j : ℕ, ‖q (j + M) * E (j + M)‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' j : ℕ, |q (j + M) * E (j + M)| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑' j : ℕ, B * (q (j + M) * (((j + M : ℕ) : ℝ))) := by
          apply Summable.tsum_le_tsum
          · intro j
            rw [abs_mul, abs_of_nonneg (hq0 _)]
            calc q (j + M) * |E (j + M)|
                ≤ q (j + M) * (B * (((j + M : ℕ) : ℝ))) :=
                  mul_le_mul_of_nonneg_left (hE (j + M)) (hq0 _)
              _ = B * (q (j + M) * (((j + M : ℕ) : ℝ))) := by ring
          · exact hqE_shift.abs
          · exact hmaj
      _ = B * ∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ)) := by
          rw [tsum_mul_left]
  obtain ⟨Nb, hNb⟩ := eventually_atTop.1 hbound
  obtain ⟨Nf, hNf⟩ := eventually_atTop.1 hfin_ev
  refine ⟨max M (max Nb Nf), fun n hn => ?_⟩
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hnb : Nb ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnf : Nf ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hboundn : ∀ k, qn n k ≤ g k := hNb n hnb
  have hfinn : |∑ k ∈ Finset.range M, (qn n k - q k) * E k| < δ := hNf n hnf
  have hn := hnM
  have hn1 : M ≤ n + 1 := by omega
  -- Split the finite sum and the tsum.
  have hsplit : ∑ k ∈ Finset.range (n + 1), qn n k * E k =
      ∑ k ∈ Finset.range M, qn n k * E k +
        ∑ k ∈ Finset.Ico M (n + 1), qn n k * E k := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive (fun k => qn n k * E k)
      (Nat.zero_le M) hn1).symm
  have hpois : ∑' k, q k * E k =
      ∑ k ∈ Finset.range M, q k * E k +
        ∑' j : ℕ, q (j + M) * E (j + M) :=
    (hqE.sum_add_tsum_nat_add M).symm
  have hsub : (∑ k ∈ Finset.range M, qn n k * E k) -
      (∑ k ∈ Finset.range M, q k * E k) =
      ∑ k ∈ Finset.range M, (qn n k - q k) * E k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  -- Middle bound.
  have hmid : |∑ k ∈ Finset.Ico M (n + 1), qn n k * E k| ≤
      B * (∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ))) := by
    calc |∑ k ∈ Finset.Ico M (n + 1), qn n k * E k|
        ≤ ∑ k ∈ Finset.Ico M (n + 1), |qn n k * E k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico M (n + 1), B * (g k * (k : ℝ)) := by
          apply Finset.sum_le_sum
          intro k _
          have hqnk : 0 ≤ qn n k := hqn0 n k
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          calc |qn n k * E k| = qn n k * |E k| := by
                rw [abs_mul, abs_of_nonneg hqnk]
            _ ≤ qn n k * (B * (k : ℝ)) :=
                mul_le_mul_of_nonneg_left (hE k) hqnk
            _ ≤ g k * (B * (k : ℝ)) :=
                mul_le_mul_of_nonneg_right (hboundn k) (mul_nonneg hB hk0)
            _ = B * (g k * (k : ℝ)) := by ring
      _ = B * ∑ k ∈ Finset.Ico M (n + 1), g k * (k : ℝ) := by
          rw [Finset.mul_sum]
      _ = B * ∑ j ∈ Finset.range (n + 1 - M),
            g (j + M) * (((j + M : ℕ) : ℝ)) := by
          rw [Finset.sum_Ico_eq_sum_range (fun k => g k * (k : ℝ)) M (n + 1)]
          simp only [Nat.add_comm M]
      _ ≤ B * ∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hB
          exact Summable.sum_le_tsum (Finset.range (n + 1 - M))
            (fun i _ => mul_nonneg (hg0 (i + M)) (Nat.cast_nonneg _)) hgk_shift
  -- Assemble the three pieces.
  have hX : (∑ k ∈ Finset.range (n + 1), qn n k * E k) -
      (∑' k, q k * E k) =
      (∑ k ∈ Finset.range M, (qn n k - q k) * E k) +
        (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k) -
        (∑' j : ℕ, q (j + M) * E (j + M)) := by
    rw [hsplit, hpois]
    rw [show (∑ k ∈ Finset.range M, qn n k * E k +
        ∑ k ∈ Finset.Ico M (n + 1), qn n k * E k) -
        (∑ k ∈ Finset.range M, q k * E k +
          ∑' j : ℕ, q (j + M) * E (j + M)) =
        ((∑ k ∈ Finset.range M, qn n k * E k) -
          (∑ k ∈ Finset.range M, q k * E k)) +
        (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k) -
        (∑' j : ℕ, q (j + M) * E (j + M)) from by ring]
    rw [hsub]
  rw [Real.dist_eq, hX]
  have htri : |(∑ k ∈ Finset.range M, (qn n k - q k) * E k) +
      (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k) -
      (∑' j : ℕ, q (j + M) * E (j + M))| ≤
      |∑ k ∈ Finset.range M, (qn n k - q k) * E k| +
      |∑ k ∈ Finset.Ico M (n + 1), qn n k * E k| +
      |∑' j : ℕ, q (j + M) * E (j + M)| := by
    have h1 : |(∑ k ∈ Finset.range M, (qn n k - q k) * E k) +
        (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k) -
        (∑' j : ℕ, q (j + M) * E (j + M))| =
        |((∑ k ∈ Finset.range M, (qn n k - q k) * E k) +
          (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k)) +
          (-(∑' j : ℕ, q (j + M) * E (j + M)))| := by rw [sub_eq_add_neg]
    rw [h1]
    calc |((∑ k ∈ Finset.range M, (qn n k - q k) * E k) +
          (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k)) +
          (-(∑' j : ℕ, q (j + M) * E (j + M)))|
        ≤ |(∑ k ∈ Finset.range M, (qn n k - q k) * E k) +
            (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k)| +
          |-(∑' j : ℕ, q (j + M) * E (j + M))| := abs_add_le _ _
      _ = |(∑ k ∈ Finset.range M, (qn n k - q k) * E k) +
            (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k)| +
          |∑' j : ℕ, q (j + M) * E (j + M)| := by rw [abs_neg]
      _ ≤ (|∑ k ∈ Finset.range M, (qn n k - q k) * E k| +
            |∑ k ∈ Finset.Ico M (n + 1), qn n k * E k|) +
          |∑' j : ℕ, q (j + M) * E (j + M)| := by
          linarith [abs_add_le (∑ k ∈ Finset.range M, (qn n k - q k) * E k)
            (∑ k ∈ Finset.Ico M (n + 1), qn n k * E k)]
      _ = |∑ k ∈ Finset.range M, (qn n k - q k) * E k| +
            |∑ k ∈ Finset.Ico M (n + 1), qn n k * E k| +
          |∑' j : ℕ, q (j + M) * E (j + M)| := by ring
  have h2 := hmid
  have h3 := htail3
  have h4 : B * (∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ))) ≤ B * δ :=
    mul_le_mul_of_nonneg_left hMq.le hB
  have hδε : (2 * B + 1) * δ < ε := by
    have h1 : 2 * B + 1 < 2 * B + 2 := by linarith
    calc (2 * B + 1) * δ < (2 * B + 2) * δ :=
          mul_lt_mul_of_pos_right h1 hδ
      _ = ε := by
          rw [hδdef]
          field_simp
  have hmidδ : B * (∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ))) ≤ B * δ :=
    mul_le_mul_of_nonneg_left hMg.le hB
  have hsum_bound : |∑ k ∈ Finset.range M, (qn n k - q k) * E k| +
      |∑ k ∈ Finset.Ico M (n + 1), qn n k * E k| +
      |∑' j : ℕ, q (j + M) * E (j + M)| < δ + B * δ + B * δ := by
    linarith [hfinn, h2, h3, hmidδ, h4]
  have hfin_bound : δ + B * δ + B * δ ≤ ε := by
    have heq : δ + B * δ + B * δ = (2 * B + 1) * δ := by ring
    rw [heq]
    exact le_of_lt hδε
  linarith [htri, hsum_bound, hfin_bound]

/-- **Finite-mass comparison.**  If a sequence of nonnegative masses `qn n` is
eventually dominated by a summable majorant `g`, has first moments controlled by
`g`, and converges pointwise to a mass `q` with finite first moment, then for
any functional bounded by a constant times the index the finite sums converge to
the `tsum` against `q`. -/
private theorem tendsto_finset_sum_tsum_of_masses_gen
    (q : ℕ → ℝ) (qn : ℕ → ℕ → ℝ) (H : ℕ → ℕ → ℝ) (Hlim : ℕ → ℝ)
    (B : ℝ) (g : ℕ → ℝ)
    (hB : 0 ≤ B) (hH : ∀ n k, |H n k| ≤ B * (k : ℝ))
    (hHlim : ∀ k, |Hlim k| ≤ B * (k : ℝ))
    (hHconv : ∀ k, Tendsto (fun n => H n k) atTop (𝓝 (Hlim k)))
    (hg0 : ∀ k, 0 ≤ g k) (hgk : Summable (fun k => g k * (k : ℝ)))
    (hbound : ∀ᶠ n in atTop, ∀ k, qn n k ≤ g k)
    (hqn0 : ∀ n k, 0 ≤ qn n k)
    (hq0 : ∀ k, 0 ≤ q k) (hqk : Summable (fun k => q k * (k : ℝ)))
    (hconv : ∀ k, Tendsto (fun n => qn n k) atTop (𝓝 (q k)))
    (hHsum : Summable (fun k => q k * Hlim k)) :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), qn n k * H n k) atTop
      (𝓝 (∑' k, q k * Hlim k)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set δ : ℝ := ε / (2 * B + 2) with hδdef
  have hδ : 0 < δ := by positivity
  -- Tails of the two majorant first moments.
  have htail_g : Tendsto (fun M : ℕ => ∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun k : ℕ => g k * (k : ℝ))
  have htail_q : Tendsto (fun M : ℕ => ∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ)))
      atTop (𝓝 0) :=
    tendsto_sum_nat_add (fun k : ℕ => q k * (k : ℝ))
  obtain ⟨M, hM⟩ := eventually_atTop.1
    ((htail_g.eventually (Iio_mem_nhds hδ)).and
      (htail_q.eventually (Iio_mem_nhds hδ)))
  have hMg : (∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ))) < δ :=
    (hM M le_rfl).1
  have hMq : (∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ))) < δ :=
    (hM M le_rfl).2
  -- Eventually the majorant holds and the finite part is small.
  have hfin : Tendsto (fun n =>
      ∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) atTop (𝓝 0) := by
    have hterm : ∀ k ∈ Finset.range M,
        Tendsto (fun n => qn n k * H n k - q k * Hlim k) atTop (𝓝 0) := by
      intro k _
      have hqk : Tendsto (fun n : ℕ => qn n k - q k) atTop (𝓝 (q k - q k)) :=
        (hconv k).sub tendsto_const_nhds
      have hHk : Tendsto (fun n : ℕ => H n k) atTop (𝓝 (Hlim k)) := hHconv k
      have hHdiff : Tendsto (fun n : ℕ => H n k - Hlim k) atTop (𝓝 (Hlim k - Hlim k)) :=
        hHk.sub tendsto_const_nhds
      have h1 : Tendsto (fun n : ℕ => (qn n k - q k) * H n k) atTop (𝓝 0) := by
        have := hqk.mul hHk
        simpa using this
      have h2 : Tendsto (fun n : ℕ => q k * (H n k - Hlim k)) atTop (𝓝 0) := by
        have hc : Tendsto (fun _ : ℕ => q k) atTop (𝓝 (q k)) := tendsto_const_nhds
        have := hc.mul hHdiff
        simpa using this
      have h := h1.add h2
      have heq : (fun n : ℕ => (qn n k - q k) * H n k + q k * (H n k - Hlim k)) =
          fun n : ℕ => qn n k * H n k - q k * Hlim k := by
        funext n; ring
      rw [heq] at h
      simpa using h
    simpa using tendsto_finsetSum (Finset.range M) hterm
  have hfin_ev : ∀ᶠ n in atTop,
      |∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)| < δ := by
    have hmem : Set.Ioo (-δ) δ ∈ 𝓝 (0 : ℝ) :=
      Ioo_mem_nhds (by linarith) hδ
    have h := hfin.eventually hmem
    filter_upwards [h] with n hn
    rw [abs_lt]
    exact hn
  -- The shifted tails.
  have hHsum_shift : Summable (fun j : ℕ => q (j + M) * Hlim (j + M)) :=
    (summable_nat_add_iff M).mpr hHsum
  have hqk_shift : Summable (fun j : ℕ => q (j + M) * (((j + M : ℕ) : ℝ))) :=
    (summable_nat_add_iff M).mpr hqk
  have hgk_shift : Summable (fun j : ℕ => g (j + M) * (((j + M : ℕ) : ℝ))) :=
    (summable_nat_add_iff M).mpr hgk
  -- Bound on the shifted Poisson tail.
  have htail3 : |∑' j : ℕ, q (j + M) * Hlim (j + M)| ≤
      B * (∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ))) := by
    have hnorm : Summable (fun j : ℕ => ‖q (j + M) * Hlim (j + M)‖) := hHsum_shift.norm
    have hmaj : Summable (fun j : ℕ => B * (q (j + M) * (((j + M : ℕ) : ℝ)))) :=
      hqk_shift.mul_left B
    calc |∑' j : ℕ, q (j + M) * Hlim (j + M)|
        = ‖∑' j : ℕ, q (j + M) * Hlim (j + M)‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' j : ℕ, ‖q (j + M) * Hlim (j + M)‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' j : ℕ, |q (j + M) * Hlim (j + M)| := by simp only [Real.norm_eq_abs]
      _ ≤ ∑' j : ℕ, B * (q (j + M) * (((j + M : ℕ) : ℝ))) := by
          apply Summable.tsum_le_tsum
          · intro j
            rw [abs_mul, abs_of_nonneg (hq0 _)]
            calc q (j + M) * |Hlim (j + M)|
                ≤ q (j + M) * (B * (((j + M : ℕ) : ℝ))) :=
                  mul_le_mul_of_nonneg_left (hHlim (j + M)) (hq0 _)
              _ = B * (q (j + M) * (((j + M : ℕ) : ℝ))) := by ring
          · exact hHsum_shift.abs
          · exact hmaj
      _ = B * ∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ)) := by
          rw [tsum_mul_left]
  obtain ⟨Nb, hNb⟩ := eventually_atTop.1 hbound
  obtain ⟨Nf, hNf⟩ := eventually_atTop.1 hfin_ev
  refine ⟨max M (max Nb Nf), fun n hn => ?_⟩
  have hnM : M ≤ n := le_trans (le_max_left _ _) hn
  have hnb : Nb ≤ n :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hnf : Nf ≤ n :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  have hboundn : ∀ k, qn n k ≤ g k := hNb n hnb
  have hfinn : |∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)| < δ := hNf n hnf
  have hn := hnM
  have hn1 : M ≤ n + 1 := by omega
  -- Split the finite sum and the tsum.
  have hsplit : ∑ k ∈ Finset.range (n + 1), qn n k * H n k =
      ∑ k ∈ Finset.range M, qn n k * H n k +
        ∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive (fun k => qn n k * H n k)
      (Nat.zero_le M) hn1).symm
  have hpois : ∑' k, q k * Hlim k =
      ∑ k ∈ Finset.range M, q k * Hlim k +
        ∑' j : ℕ, q (j + M) * Hlim (j + M) :=
    (hHsum.sum_add_tsum_nat_add M).symm
  have hsub : (∑ k ∈ Finset.range M, qn n k * H n k) -
      (∑ k ∈ Finset.range M, q k * Hlim k) =
      ∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k) := by
    rw [← Finset.sum_sub_distrib]
  -- Middle bound.
  have hmid : |∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k| ≤
      B * (∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ))) := by
    calc |∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k|
        ≤ ∑ k ∈ Finset.Ico M (n + 1), |qn n k * H n k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Ico M (n + 1), B * (g k * (k : ℝ)) := by
          apply Finset.sum_le_sum
          intro k _
          have hqnk : 0 ≤ qn n k := hqn0 n k
          have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          calc |qn n k * H n k| = qn n k * |H n k| := by
                rw [abs_mul, abs_of_nonneg hqnk]
            _ ≤ qn n k * (B * (k : ℝ)) :=
                mul_le_mul_of_nonneg_left (hH n k) hqnk
            _ ≤ g k * (B * (k : ℝ)) :=
                mul_le_mul_of_nonneg_right (hboundn k) (mul_nonneg hB hk0)
            _ = B * (g k * (k : ℝ)) := by ring
      _ = B * ∑ k ∈ Finset.Ico M (n + 1), g k * (k : ℝ) := by
          rw [Finset.mul_sum]
      _ = B * ∑ j ∈ Finset.range (n + 1 - M),
            g (j + M) * (((j + M : ℕ) : ℝ)) := by
          rw [Finset.sum_Ico_eq_sum_range (fun k => g k * (k : ℝ)) M (n + 1)]
          simp only [Nat.add_comm M]
      _ ≤ B * ∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hB
          exact Summable.sum_le_tsum (Finset.range (n + 1 - M))
            (fun i _ => mul_nonneg (hg0 (i + M)) (Nat.cast_nonneg _)) hgk_shift
  -- Assemble the three pieces.
  have hX : (∑ k ∈ Finset.range (n + 1), qn n k * H n k) -
      (∑' k, q k * Hlim k) =
      (∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) +
        (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k) -
        (∑' j : ℕ, q (j + M) * Hlim (j + M)) := by
    rw [hsplit, hpois]
    rw [show (∑ k ∈ Finset.range M, qn n k * H n k +
        ∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k) -
        (∑ k ∈ Finset.range M, q k * Hlim k +
          ∑' j : ℕ, q (j + M) * Hlim (j + M)) =
        ((∑ k ∈ Finset.range M, qn n k * H n k) -
          (∑ k ∈ Finset.range M, q k * Hlim k)) +
        (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k) -
        (∑' j : ℕ, q (j + M) * Hlim (j + M)) from by ring]
    rw [hsub]
  rw [Real.dist_eq, hX]
  have htri : |(∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) +
      (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k) -
      (∑' j : ℕ, q (j + M) * Hlim (j + M))| ≤
      |∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)| +
      |∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k| +
      |∑' j : ℕ, q (j + M) * Hlim (j + M)| := by
    have h1 : |(∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) +
        (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k) -
        (∑' j : ℕ, q (j + M) * Hlim (j + M))| =
        |((∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) +
          (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k)) +
          (-(∑' j : ℕ, q (j + M) * Hlim (j + M)))| := by rw [sub_eq_add_neg]
    rw [h1]
    calc |((∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) +
          (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k)) +
          (-(∑' j : ℕ, q (j + M) * Hlim (j + M)))|
        ≤ |(∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) +
            (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k)| +
          |-(∑' j : ℕ, q (j + M) * Hlim (j + M))| := abs_add_le _ _
      _ = |(∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)) +
            (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k)| +
          |∑' j : ℕ, q (j + M) * Hlim (j + M)| := by rw [abs_neg]
      _ ≤ (|∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)| +
            |∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k|) +
          |∑' j : ℕ, q (j + M) * Hlim (j + M)| := by
          linarith [abs_add_le (∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k))
            (∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k)]
      _ = |∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)| +
            |∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k| +
          |∑' j : ℕ, q (j + M) * Hlim (j + M)| := by ring
  have h2 := hmid
  have h3 := htail3
  have h4 : B * (∑' j : ℕ, q (j + M) * (((j + M : ℕ) : ℝ))) ≤ B * δ :=
    mul_le_mul_of_nonneg_left hMq.le hB
  have hδε : (2 * B + 1) * δ < ε := by
    have h1 : 2 * B + 1 < 2 * B + 2 := by linarith
    calc (2 * B + 1) * δ < (2 * B + 2) * δ :=
          mul_lt_mul_of_pos_right h1 hδ
      _ = ε := by
          rw [hδdef]
          field_simp
  have hmidδ : B * (∑' j : ℕ, g (j + M) * (((j + M : ℕ) : ℝ))) ≤ B * δ :=
    mul_le_mul_of_nonneg_left hMg.le hB
  have hsum_bound : |∑ k ∈ Finset.range M, (qn n k * H n k - q k * Hlim k)| +
      |∑ k ∈ Finset.Ico M (n + 1), qn n k * H n k| +
      |∑' j : ℕ, q (j + M) * Hlim (j + M)| < δ + B * δ + B * δ := by
    linarith [hfinn, h2, h3, hmidδ, h4]
  have hfin_bound : δ + B * δ + B * δ ≤ ε := by
    have heq : δ + B * δ + B * δ = (2 * B + 1) * δ := by ring
    rw [heq]
    exact le_of_lt hδε
  linarith [htri, hsum_bound, hfin_bound]


/-- **Bounded-intensity Poissonization.**  If `n * p n → r`, then the expectation
of any functional bounded by a constant times the number of points under the
binomial count `Bin(n, p n)` converges to its expectation under `Poisson r`. -/
theorem tendsto_binomial_integral_poisson
    (E : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hE : ∀ m, E m ≤ B * (m : ℝ)) (hEabs : ∀ m, -E m ≤ B * (m : ℝ))
    (p : ℕ → I) (r : ℝ≥0)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ))) :
    Tendsto (fun n : ℕ => ∫ m, E m ∂(ProbabilityTheory.binomial n (p n))) atTop
      (𝓝 (∫ m, E m ∂poissonMeasure r)) := by
  classical
  set R : ℝ≥0 := r + 1 with hRdef
  have hRco : ((R : ℝ)) = (r : ℝ) + 1 := by
    rw [hRdef, NNReal.coe_add, NNReal.coe_one]
  have hRpos : (0 : ℝ) < (R : ℝ) := by rw [hRco]; positivity
  -- The summable majorant of the binomial masses.
  set g : ℕ → ℝ := fun k => (R : ℝ) ^ k / k.factorial with hgdef
  have hg0 : ∀ k, 0 ≤ g k := by
    intro k; exact div_nonneg (pow_nonneg hRpos.le k) (by positivity)
  have hgk : Summable (fun k => g k * (k : ℝ)) := by
    have h := (summable_poissonMass_mul R).mul_left (Real.exp (R : ℝ))
    refine h.congr fun k => ?_
    unfold poissonMass g
    have hexp : Real.exp (R : ℝ) * Real.exp (-(R : ℝ)) = 1 := by
      rw [← Real.exp_add]
      simp
    calc Real.exp (R : ℝ) *
          (Real.exp (-(R : ℝ)) * (R : ℝ) ^ k / k.factorial * (k : ℝ))
        = (Real.exp (R : ℝ) * Real.exp (-(R : ℝ))) *
            ((R : ℝ) ^ k / k.factorial * (k : ℝ)) := by ring
      _ = 1 * ((R : ℝ) ^ k / k.factorial * (k : ℝ)) := by rw [hexp]
      _ = (R : ℝ) ^ k / k.factorial * (k : ℝ) := one_mul _
  -- Eventual domination of the binomial masses.
  have hbound : ∀ᶠ n in atTop, ∀ k, binomialMass n (p n) k ≤ g k := by
    have hle : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (p n : ℝ) ≤ (R : ℝ) := by
      have := hr.eventually (Iio_mem_nhds (by linarith : (r : ℝ) < (r : ℝ) + 1))
      filter_upwards [this] with n hn
      rw [hRco]
      linarith
    filter_upwards [hle] with n hn k
    calc binomialMass n (p n) k
        ≤ ((n : ℝ) * (p n : ℝ)) ^ k / k.factorial := binomialMass_le n (p n) k
      _ ≤ (R : ℝ) ^ k / k.factorial := by
          have hk0 : (0 : ℝ) ≤ (n : ℝ) * (p n : ℝ) :=
            mul_nonneg (Nat.cast_nonneg n) (p n).2.1
          have hfac : (0 : ℝ) < k.factorial := by positivity
          gcongr
  -- The Poisson first moment is summable.
  have hqk : Summable (fun k => poissonMass r k * (k : ℝ)) :=
    summable_poissonMass_mul r
  -- The tilted series is absolutely summable.
  have hqE : Summable (fun k => poissonMass r k * E k) := by
    refine Summable.of_norm_bounded
      (g := fun k => B * (poissonMass r k * (k : ℝ))) ?_ ?_
    · exact hqk.mul_left B
    · intro k
      rw [Real.norm_eq_abs]
      have hq0 : 0 ≤ poissonMass r k := poissonMass_nonneg r k
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have habs : |E k| ≤ B * (k : ℝ) := by
        rw [abs_le]
        exact ⟨by linarith [hEabs k], hE k⟩
      rw [abs_mul, abs_of_nonneg hq0]
      calc poissonMass r k * |E k| ≤ poissonMass r k * (B * (k : ℝ)) :=
            mul_le_mul_of_nonneg_left habs hq0
        _ = B * (poissonMass r k * (k : ℝ)) := by ring
  have hcmp := tendsto_finset_sum_tsum_of_masses
    (q := poissonMass r) (qn := fun n k => binomialMass n (p n) k)
    (E := E) (B := B) (g := g) hB (fun k => by
      rw [abs_le]; exact ⟨by linarith [hEabs k], hE k⟩) hg0 hgk hbound
    (fun n k => binomialMass_nonneg n (p n) k)
    (fun k => poissonMass_nonneg r k) hqk
    (fun k => tendsto_binomialMass_poissonMass p hr k) hqE
  -- Identify the two sides with the actual integrals.
  have hPoi : ∫ m, E m ∂poissonMeasure r = ∑' k, poissonMass r k * E k := by
    rw [integral_poissonMeasure r E]
    apply tsum_congr
    intro k
    unfold poissonMass
    rw [smul_eq_mul]
  rw [hPoi]
  refine hcmp.congr' (Eventually.of_forall fun n => ?_)
  exact (integral_binomial_real n (p n) E).symm


/-- **Bounded-intensity Poissonization, absolute form.** -/
theorem tendsto_binomial_integral_poisson_abs
    (E : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B) (hE : ∀ m, |E m| ≤ B * (m : ℝ))
    (p : ℕ → I) (r : ℝ≥0)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ))) :
    Tendsto (fun n : ℕ => ∫ m, E m ∂(ProbabilityTheory.binomial n (p n))) atTop
      (𝓝 (∫ m, E m ∂poissonMeasure r)) :=
  tendsto_binomial_integral_poisson E hB
    (fun m => (abs_le.mp (hE m)).2) (fun m => by
      have := (abs_le.mp (hE m)).1
      linarith) p r hr


/-- The binomial masses sum to one. -/
theorem binomialMass_sum_one (n : ℕ) (p : I) :
    ∑ k ∈ Finset.range (n + 1), binomialMass n p k = 1 := by
  have h : (∫ _x : ℕ, (1 : ℝ) ∂(ProbabilityTheory.binomial n p)) = 1 := by
    rw [integral_const]
    simp
  rw [integral_binomial_real] at h
  simpa only [mul_one] using h

/-- The Poisson masses sum to one. -/
theorem poissonMass_sum_one (r : ℝ≥0) : ∑' k : ℕ, poissonMass r k = 1 := by
  have h : (∫ _x : ℕ, (1 : ℝ) ∂poissonMeasure r) = 1 := by
    rw [integral_const]
    simp
  rw [integral_poissonMeasure r (fun _ => (1 : ℝ))] at h
  simpa only [poissonMass, smul_eq_mul, mul_one] using h

/-- **Two-count bounded-intensity Poissonization.**  Two independent binomial
counts with common parameter, applied to a functional bounded by a constant
times the minimum of the two counts, converge to the two independent Poisson
counts. -/
theorem tendsto_two_count_binomial_poisson
    (F : ℕ → ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ m k, |F m k| ≤ B * ((min m k : ℕ) : ℝ))
    (p : ℕ → I) (r : ℝ≥0)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ)) atTop (𝓝 (r : ℝ))) :
    Tendsto (fun n : ℕ =>
        ∑ m ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1),
            binomialMass n (p n) m * binomialMass n (p n) k * F m k) atTop
      (𝓝 (∑' m, poissonMass r m * ∑' k, poissonMass r k * F m k)) := by
  classical
  set R : ℝ≥0 := r + 1 with hRdef
  have hRco : ((R : ℝ)) = (r : ℝ) + 1 := by
    rw [hRdef, NNReal.coe_add, NNReal.coe_one]
  have hRpos : (0 : ℝ) < (R : ℝ) := by rw [hRco]; positivity
  set g : ℕ → ℝ := fun k => (R : ℝ) ^ k / k.factorial with hgdef
  have hg0 : ∀ k, 0 ≤ g k := fun k =>
    div_nonneg (pow_nonneg hRpos.le k) (by positivity)
  have hgk : Summable (fun k => g k * (k : ℝ)) := by
    have h := (summable_poissonMass_mul R).mul_left (Real.exp (R : ℝ))
    refine h.congr fun k => ?_
    unfold poissonMass g
    have hexp : Real.exp (R : ℝ) * Real.exp (-(R : ℝ)) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (R : ℝ) *
          (Real.exp (-(R : ℝ)) * (R : ℝ) ^ k / k.factorial * (k : ℝ))
        = (Real.exp (R : ℝ) * Real.exp (-(R : ℝ))) *
            ((R : ℝ) ^ k / k.factorial * (k : ℝ)) := by ring
      _ = 1 * ((R : ℝ) ^ k / k.factorial * (k : ℝ)) := by rw [hexp]
      _ = (R : ℝ) ^ k / k.factorial * (k : ℝ) := one_mul _
  have hbound : ∀ᶠ n in atTop, ∀ k, binomialMass n (p n) k ≤ g k := by
    have hle : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (p n : ℝ) ≤ (R : ℝ) := by
      have := hr.eventually (Iio_mem_nhds (by linarith : (r : ℝ) < (r : ℝ) + 1))
      filter_upwards [this] with n hn
      rw [hRco]; linarith
    filter_upwards [hle] with n hn k
    calc binomialMass n (p n) k
        ≤ ((n : ℝ) * (p n : ℝ)) ^ k / k.factorial := binomialMass_le n (p n) k
      _ ≤ (R : ℝ) ^ k / k.factorial := by
          have hk0 : (0 : ℝ) ≤ (n : ℝ) * (p n : ℝ) :=
            mul_nonneg (Nat.cast_nonneg n) (p n).2.1
          gcongr
  have hqk : Summable (fun k => poissonMass r k * (k : ℝ)) :=
    summable_poissonMass_mul r
  have hq0 : ∀ k, 0 ≤ poissonMass r k := poissonMass_nonneg r
  have hq1 : ∑' k : ℕ, poissonMass r k = 1 := poissonMass_sum_one r
  -- The inner finite expectations.
  set H : ℕ → ℕ → ℝ := fun n m =>
    ∑ k ∈ Finset.range (n + 1), binomialMass n (p n) k * F m k with hHdef
  set Hlim : ℕ → ℝ := fun m => ∑' k, poissonMass r k * F m k with hHlimdef
  -- Each inner series is summable.
  have hFsum : ∀ m, Summable (fun k => poissonMass r k * F m k) := by
    intro m
    refine Summable.of_norm_bounded
      (g := fun k => B * (m : ℝ) * poissonMass r k) ?_ ?_
    · exact (summable_poissonMass r).mul_left (B * (m : ℝ))
    · intro k
      rw [Real.norm_eq_abs]
      have hq0' : 0 ≤ poissonMass r k := poissonMass_nonneg r k
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [abs_mul, abs_of_nonneg hq0']
      calc poissonMass r k * |F m k|
          ≤ poissonMass r k * (B * ((min m k : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hF m k) hq0'
        _ ≤ poissonMass r k * (B * (m : ℝ)) := by
            apply mul_le_mul_of_nonneg_left _ hq0'
            apply mul_le_mul_of_nonneg_left _ hB
            exact_mod_cast min_le_left m k
        _ = B * (m : ℝ) * poissonMass r k := by ring
  -- Uniform bound on the inner finite expectations.
  have hHbound : ∀ n m, |H n m| ≤ B * (m : ℝ) := by
    intro n m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hsum1 : ∑ k ∈ Finset.range (n + 1), binomialMass n (p n) k = 1 :=
      binomialMass_sum_one n (p n)
    calc |H n m|
        = |∑ k ∈ Finset.range (n + 1), binomialMass n (p n) k * F m k| := rfl
      _ ≤ ∑ k ∈ Finset.range (n + 1), |binomialMass n (p n) k * F m k| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range (n + 1), B * (m : ℝ) * binomialMass n (p n) k := by
          apply Finset.sum_le_sum
          intro k _
          have hqnk : 0 ≤ binomialMass n (p n) k := binomialMass_nonneg n (p n) k
          rw [abs_mul, abs_of_nonneg hqnk]
          calc binomialMass n (p n) k * |F m k|
              ≤ binomialMass n (p n) k * (B * ((min m k : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (hF m k) hqnk
            _ ≤ binomialMass n (p n) k * (B * (m : ℝ)) := by
                apply mul_le_mul_of_nonneg_left _ hqnk
                apply mul_le_mul_of_nonneg_left _ hB
                exact_mod_cast min_le_left m k
            _ = B * (m : ℝ) * binomialMass n (p n) k := by ring
      _ = B * (m : ℝ) * ∑ k ∈ Finset.range (n + 1), binomialMass n (p n) k := by
          rw [Finset.mul_sum]
      _ = B * (m : ℝ) := by rw [hsum1, mul_one]
  -- Uniform bound on the inner Poisson expectations.
  have hHlim_bound : ∀ m, |Hlim m| ≤ B * (m : ℝ) := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hnorm : Summable (fun k : ℕ => ‖poissonMass r k * F m k‖) :=
      (hFsum m).norm
    have hmaj : Summable (fun k : ℕ => B * (m : ℝ) * poissonMass r k) :=
      (summable_poissonMass r).mul_left (B * (m : ℝ))
    have hnorm' : Summable (fun k : ℕ => poissonMass r k * |F m k|) := by
      refine hnorm.congr fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonMass_nonneg r k)]
    calc |Hlim m|
        = ‖∑' k, poissonMass r k * F m k‖ := by rw [Real.norm_eq_abs]
      _ ≤ ∑' k, ‖poissonMass r k * F m k‖ := norm_tsum_le_tsum_norm hnorm
      _ = ∑' k, poissonMass r k * |F m k| := by
          apply tsum_congr; intro k
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonMass_nonneg r k)]
      _ ≤ ∑' k, B * (m : ℝ) * poissonMass r k := by
          apply Summable.tsum_le_tsum
          · intro k
            have hq0' : 0 ≤ poissonMass r k := poissonMass_nonneg r k
            calc poissonMass r k * |F m k|
                ≤ poissonMass r k * (B * ((min m k : ℕ) : ℝ)) :=
                  mul_le_mul_of_nonneg_left (hF m k) hq0'
              _ ≤ poissonMass r k * (B * (m : ℝ)) := by
                  apply mul_le_mul_of_nonneg_left _ hq0'
                  apply mul_le_mul_of_nonneg_left _ hB
                  exact_mod_cast min_le_left m k
              _ = B * (m : ℝ) * poissonMass r k := by ring
          · exact hnorm'
          · exact hmaj
      _ = B * (m : ℝ) * ∑' k, poissonMass r k := by rw [tsum_mul_left]
      _ = B * (m : ℝ) := by rw [hq1, mul_one]
  -- Pointwise convergence of the inner finite expectations.
  have hHconv : ∀ m, Tendsto (fun n => H n m) atTop (𝓝 (Hlim m)) := by
    intro m
    have hFk : ∀ k, |F m k| ≤ B * (k : ℝ) := by
      intro k
      have h1 : ((min m k : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast min_le_right m k
      calc |F m k| ≤ B * ((min m k : ℕ) : ℝ) := hF m k
        _ ≤ B * (k : ℝ) := by
            apply mul_le_mul_of_nonneg_left h1 hB
    exact tendsto_finset_sum_tsum_of_masses
      (q := poissonMass r) (qn := fun n k => binomialMass n (p n) k)
      (E := fun k => F m k) (B := B) (g := g) hB hFk hg0 hgk hbound
      (fun n k => binomialMass_nonneg n (p n) k) hq0 hqk
      (fun k => tendsto_binomialMass_poissonMass p hr k) (hFsum m)
  -- Summability of the outer series.
  have hHsum : Summable (fun m => poissonMass r m * Hlim m) := by
    refine Summable.of_norm_bounded (g := fun m => B * (poissonMass r m * (m : ℝ))) ?_ ?_
    · exact hqk.mul_left B
    · intro m
      rw [Real.norm_eq_abs]
      have hq0' : 0 ≤ poissonMass r m := poissonMass_nonneg r m
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [abs_mul, abs_of_nonneg hq0']
      calc poissonMass r m * |Hlim m| ≤ poissonMass r m * (B * (m : ℝ)) :=
            mul_le_mul_of_nonneg_left (hHlim_bound m) hq0'
        _ = B * (poissonMass r m * (m : ℝ)) := by ring
  have hmain := tendsto_finset_sum_tsum_of_masses_gen
    (q := poissonMass r) (qn := fun n k => binomialMass n (p n) k)
    (H := H) (Hlim := Hlim) (B := B) (g := g) hB hHbound hHlim_bound
    hHconv hg0 hgk hbound (fun n k => binomialMass_nonneg n (p n) k) hq0 hqk
    (fun k => tendsto_binomialMass_poissonMass p hr k) hHsum
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  -- The double sum factors into the outer mass times the inner sum.
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

end OTSelector.Probability
