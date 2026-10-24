import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.Moments.Basic
import OTSelector.Probability.PoissonExponentialMoment

/-!
Conditions: A deterministic finite candidate family, an explicit Poisson law for every candidate count, a cardinality bound exp(am) and rate bounds bm.

Objects: One original-law outer probability bound for a high count somewhere in the whole candidate family, with exponent −(K−a−b(e−1))m.

Proof detail: Apply exponential Markov at tilt one to each supplied Poisson count, use the common rate bound and sum over the deterministic candidate family before applying its cardinality bound.

References: Gunter Last; Mathew Penrose: Section 1.1, equations (1.8)–(1.10), p. 2; Rick Durrett: Section 1.6.1, Theorem 1.6.4 and equation (1.6.1), pp. 29–30.
Relation: A deterministic-candidate Chernoff union bound valid before adaptive selection. It assumes no independence between candidate counts and does not apply a fixed-candidate law to a subsequently selected count.
-/


/-!
# Uniform original Poisson count bounds before adaptive phase selection

A deterministic finite candidate family may have exponentially many members.
Each member is measured in the immutable original input. A union bound controls
all of them at once, with no independence between candidates or selected edges.
-/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Probability
set_option maxHeartbeats 1200000

/-- Exponentially many deterministic original-input candidates retain an
exponential count bound. Later adaptive choices among them use this one
original event and require no Poisson law for the chosen subconfiguration. -/
theorem measure_biUnion_poisson_count_le_exp
    {Ω I : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (S : Finset I) (N : I → Ω → ℕ) (rate : I → ℝ≥0)
    (hlaw : ∀ i ∈ S, ProbabilityTheory.HasLaw (N i) (poissonMeasure (rate i)) P)
    {a b m K : ℝ} (hcard : (S.card : ℝ) ≤ Real.exp (a * m))
    (hrate : ∀ i ∈ S, (rate i : ℝ) ≤ b * m) :
    P.real (⋃ i ∈ S, {ω | K * m ≤ (N i ω : ℝ)}) ≤
      Real.exp (-(K - a - b * (Real.exp 1 - 1)) * m) := by
  have he : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr
    (by simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show (0 : ℝ) ≤ 1 by norm_num))
  have hsingle (i : I) (hi : i ∈ S) :
      P.real {ω | K * m ≤ (N i ω : ℝ)} ≤
        Real.exp (b * m * (Real.exp 1 - 1) - K * m) := by
    have h := measure_ge_poisson_count_le_exp_of_hasLaw (hlaw i hi) (K * m)
      (show (0 : ℝ) ≤ 1 by norm_num)
    apply h.trans
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (hrate i hi) he]
  calc
    _ ≤ ∑ i ∈ S, P.real {ω | K * m ≤ (N i ω : ℝ)} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i ∈ S, Real.exp (b * m * (Real.exp 1 - 1) - K * m) :=
      Finset.sum_le_sum hsingle
    _ = (S.card : ℝ) * Real.exp (b * m * (Real.exp 1 - 1) - K * m) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Real.exp (a * m) * Real.exp (b * m * (Real.exp 1 - 1) - K * m) :=
      mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
    _ = Real.exp (-(K - a - b * (Real.exp 1 - 1)) * m) := by
      rw [← Real.exp_add]
      congr 1
      ring

end OTSelector.Probability
