import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import OTSelector.Probability.EmpiricalMeasure
import OTSelector.Probability.RowProbabilityFilter

/-!
Conditions: Each finite row contains n+1 measurable independent observations with the same given population probability law; tests are integrable or bounded continuous as displayed.

Objects: Scalar empirical-average convergence in row probability, weak convergence of the actual empirical marginal law under the row filter and vanishing neighborhood-escape outer mass.

Proof detail: Use the scalar strong law on the canonical infinite product, then transfer each finite prefix event to its original row by equality of the joint product law. Bounded-test convergence gives the weak row-filter conclusion.

References: Rick Durrett: Section 2.4, Theorem 2.4.1, p. 76; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: An independent finite-row LLN/empirical-marginal result. Different rows are not coupled and nothing about selected transport-plan laws follows solely from this file.
-/


/-!
# Weak convergence of empirical marginal probabilities on independent finite rows

Each original row consists of independent samples with the same population law. Scalar strong
laws on the canonical infinite product transfer to each original finite row by equality of its
joint sample law. The resulting scalar probability limits give weak convergence through the
existing row probability filter. No relation between different row spaces is assumed.

These results concern empirical marginals; they make no claim about selected transport plans.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology BigOperators BoundedContinuousFunction

namespace OTSelector.Probability

variable {E : Type*} [MeasurableSpace E]

private theorem tendsto_measureReal_prefix_average
    (μ : ProbabilityMeasure E) (f : E → ℝ) (hf : Measurable f)
    (hfi : Integrable f (μ : Measure E)) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure E))).real
      {w : ℕ → E | ε ≤ |((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i : Fin (n + 1), f (w i) - ∫ x, f x ∂(μ : Measure E)|}) atTop (𝓝 0) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure E))
  have hmap (i : ℕ) : P.map (fun w : ℕ → E ↦ w i) = (μ : Measure E) :=
    Measure.infinitePi_map_eval _ i
  have hi : Integrable (fun w : ℕ → E ↦ f (w 0)) P := by
    apply (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pi_apply 0).aemeasurable).mp
    rwa [hmap]
  have hindep : iIndepFun (fun i (w : ℕ → E) ↦ f (w i)) P :=
    iIndepFun_infinitePi (fun _ ↦ hf)
  have hident (i : ℕ) : IdentDistrib (fun w : ℕ → E ↦ w i)
      (fun w : ℕ → E ↦ w 0) P P :=
    ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable,
      (hmap i).trans (hmap 0).symm⟩
  have hmean : ∫ w : ℕ → E, f (w 0) ∂P = ∫ x, f x ∂(μ : Measure E) := by
    rw [← hmap 0]
    exact (integral_map (measurable_pi_apply 0).aemeasurable hf.aestronglyMeasurable).symm
  have hstrong := strong_law_ae_real (fun i (w : ℕ → E) ↦ f (w i)) hi
    (fun _ _ hij ↦ hindep.indepFun hij) (fun i ↦ (hident i).comp hf)
  rw [hmean] at hstrong
  have hstrong' : ∀ᵐ w ∂P, Tendsto (fun n ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ i : Fin (n + 1), f (w i)) atTop (𝓝 (∫ x, f x ∂(μ : Measure E))) := by
    filter_upwards [hstrong] with w hw
    convert hw.comp (tendsto_add_atTop_nat 1) using 1
    funext n
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ f (w i))]
    simp only [Function.comp_apply, div_eq_mul_inv, mul_comm]
  have hm (n : ℕ) : Measurable (fun w : ℕ → E ↦ ((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ i : Fin (n + 1), f (w i)) := by
    apply Measurable.const_mul
    exact Finset.measurable_sum _ fun i _ ↦ hf.comp (measurable_pi_apply (i : ℕ))
  simpa only [Real.dist_eq] using
    (tendstoInMeasure_iff_measureReal_dist.mp
      (tendstoInMeasure_of_tendsto_ae (fun n ↦ (hm n).aestronglyMeasurable) hstrong')) ε hε

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- A measurable integrable test average converges in probability under the original finite
row laws. Only independence within each row is used. -/
theorem tendsto_measureReal_average_of_row_iid
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Fin (n + 1) → Ω n → E) (μ : ProbabilityMeasure E)
    (hX : ∀ n i, Measurable (X n i)) (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, (P n).map (X n i) = (μ : Measure E))
    (f : E → ℝ) (hf : Measurable f) (hfi : Integrable f (μ : Measure E))
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {ω | ε ≤ |((n + 1 : ℕ) : ℝ)⁻¹ *
      ∑ i, f (X n i ω) - ∫ x, f x ∂(μ : Measure E)|}) atTop (𝓝 0) := by
  let R := Measure.infinitePi (fun _ : ℕ ↦ (μ : Measure E))
  have hiid : iIndepFun (fun i (w : ℕ → E) ↦ w i) R :=
    iIndepFun_infinitePi (fun _ ↦ measurable_id)
  have heq (n : ℕ) : (P n).real {ω | ε ≤ |((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i, f (X n i ω) - ∫ x, f x ∂(μ : Measure E)|} =
      R.real {w : ℕ → E | ε ≤ |((n + 1 : ℕ) : ℝ)⁻¹ *
        ∑ i : Fin (n + 1), f (w i) - ∫ x, f x ∂(μ : Measure E)|} := by
    have hrow : (P n).map (fun ω i ↦ X n i ω) =
        Measure.pi (fun _ : Fin (n + 1) ↦ (μ : Measure E)) := by
      rw [iIndepFun.map_fun_eq_pi_map (fun i ↦ (hX n i).aemeasurable) (hindep n)]
      simp_rw [hlaw n]
    have hpref : R.map (fun w : ℕ → E ↦ fun i : Fin (n + 1) ↦ w i) =
        Measure.pi (fun _ : Fin (n + 1) ↦ (μ : Measure E)) := by
      rw [iIndepFun.map_fun_eq_pi_map
        (fun i : Fin (n + 1) ↦ (measurable_pi_apply (i : ℕ)).aemeasurable)
        (hiid.precomp Fin.val_injective)]
      simp only [R, Measure.infinitePi_map_eval]
    have hvec : IdentDistrib (fun ω i ↦ X n i ω)
        (fun w : ℕ → E ↦ fun i : Fin (n + 1) ↦ w i) (P n) R :=
      ⟨(measurable_pi_lambda _ (hX n)).aemeasurable,
        (measurable_pi_lambda (fun w : ℕ → E ↦ fun i : Fin (n + 1) ↦ w i)
          fun i ↦ measurable_pi_apply (i : ℕ)).aemeasurable,
        hrow.trans hpref.symm⟩
    have hmean : Measurable (fun x : Fin (n + 1) → E ↦
        ((n + 1 : ℕ) : ℝ)⁻¹ * ∑ i, f (x i)) := by
      apply Measurable.const_mul
      exact Finset.measurable_sum _ fun i _ ↦ hf.comp (measurable_pi_apply i)
    exact congrArg ENNReal.toReal ((hvec.comp hmean).measure_mem_eq
      (measurableSet_le measurable_const
        (continuous_abs.measurable.comp
          ((measurable_id : Measurable (fun r : ℝ ↦ r)).sub measurable_const))))
  exact (tendsto_measureReal_prefix_average μ f hf hfi ε hε).congr
    (fun n ↦ (heq n).symm)

variable [TopologicalSpace E] [OpensMeasurableSpace E]

/-- Every bounded continuous empirical marginal test has vanishing error probability under the
original row laws. There is no independence assumption across rows. -/
theorem tendsto_measureReal_integral_empirical_of_row_iid
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Fin (n + 1) → Ω n → E) (μ : ProbabilityMeasure E)
    (hX : ∀ n i, Measurable (X n i)) (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, (P n).map (X n i) = (μ : Measure E))
    (f : E →ᵇ ℝ) (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {ω | ε ≤
      |(∫ x, f x ∂(empiricalProbabilityMeasure (fun i ↦ X n i ω) : Measure E)) -
        ∫ x, f x ∂(μ : Measure E)|}) atTop (𝓝 0) := by
  simpa only [empiricalProbabilityMeasure_toMeasure,
    integral_empiricalMeasure _ f.continuous.measurable.stronglyMeasurable] using
    tendsto_measureReal_average_of_row_iid P X μ hX hindep hlaw f f.continuous.measurable
      (f.integrable _) ε hε

/-- Independent finite rows with common coordinate law have empirical probabilities converging
weakly in probability. This includes compact metric Borel spaces and needs no row coupling. -/
theorem tendsto_empiricalProbabilityMeasure_row
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Fin (n + 1) → Ω n → E) (μ : ProbabilityMeasure E)
    (hX : ∀ n i, Measurable (X n i)) (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, (P n).map (X n i) = (μ : Measure E)) :
    Tendsto (fun z : Σ n, Ω n ↦ empiricalProbabilityMeasure (fun i ↦ X z.1 i z.2))
      (rowProbabilityFilter P) (𝓝 μ) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  exact (tendsto_rowProbabilityFilter_real_iff P _ _).mpr
    (tendsto_measureReal_integral_empirical_of_row_iid P X μ hX hindep hlaw f)

/-- The outer probability of leaving any prescribed weak neighborhood tends to zero under the
original finite row laws. The neighborhood need not be measurable. -/
theorem tendsto_measureReal_empirical_notMem_of_row_iid
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Fin (n + 1) → Ω n → E) (μ : ProbabilityMeasure E)
    (hX : ∀ n i, Measurable (X n i)) (hindep : ∀ n, iIndepFun (X n) (P n))
    (hlaw : ∀ n i, (P n).map (X n i) = (μ : Measure E))
    (U : Set (ProbabilityMeasure E)) (hU : U ∈ 𝓝 μ) :
    Tendsto (fun n ↦ (P n).real
      {ω | empiricalProbabilityMeasure (fun i ↦ X n i ω) ∉ U}) atTop (𝓝 0) := by
  exact (eventually_rowProbabilityFilter_iff P
    (fun z ↦ empiricalProbabilityMeasure (fun i ↦ X z.1 i z.2) ∈ U)).mp
      ((tendsto_empiricalProbabilityMeasure_row P X μ hX hindep hlaw).eventually hU)

end OTSelector.Probability
