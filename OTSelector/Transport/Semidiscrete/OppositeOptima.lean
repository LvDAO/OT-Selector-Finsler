import LeanPool.Vlasov.OT.Coupling
import Mathlib.Probability.Distributions.Exponential
import OTSelector.Finite.FractionalOptimal
import OTSelector.Probability.DirichletReference
import OTSelector.Probability.ParameterizedAffineTilts
import OTSelector.Transport.Semidiscrete.Calibration
import OTSelector.Transport.Semidiscrete.DirichletReadout
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavitySemidiscreteOptima.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavitySemidiscreteOptima`; the selected original proof blocks follow. -/
section

/-!
# Probability.CavitySemidiscreteOptima

**Conditions:** Probability source, integrable measurable finite target costs and atomless pairwise cost differences; opposite-tilt results have the stated measurable random environment and bounded probe.

**Objects:** Actual semidiscrete optimal allocations at zero and opposite deterministic good tilts, with a common full-probability event.

**Proof detail:** Use the proved Dirichlet cavity calibration to construct each optimizer; discard the countable collision tilts and choose a positive decreasing sequence outside them, then combine the countably many full events.

**Sources:** [OTSelector project, IID cavity Dirichlet disintegration](main.tex#thm:iid-cavity-dirichlet), main.tex label thm:iid-cavity-dirichlet, line 4290; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=31), Section 2.5, Proposition 2.4, p. 27, equations (2.19)–(2.20); [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal.pdf#page=42), Section 1.4, Theorem 1.4.2 (Cantor), p. 42; Section 1.5, Theorem 1.5.2, p. 46; [Günter Last; Mathew Penrose, Lectures on the Poisson Process (author version, 21 August 2017)](https://stoch.math.kit.edu/img/Last/lastpenrose2017.pdf#page=175), Section 15.5, Exercise 15.1, p. 163 (PDF page 175).

Source relation (composition): The actual Dirichlet calibration and its finite target-cell construction are invoked from the project theorem at the cited label; finite duality supports optimality and countable avoidance supplies deterministic common tilts. This consumer does not derive a new Dirichlet law from finite duality.
-/

/-!
# Actual common-environment semidiscrete optima at opposite good tilts

Cavity calibration constructs the optimizers. Parameterized collision countability
provides deterministic tilt parameters working almost surely in the random environment.
The same source and weight vector support all three optima and their quantitative excess.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal

noncomputable section
namespace OTSelector.Probability

variable {m : ℕ} {S V : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [MeasurableSpace V]

/-- The full optimal face of the actual fractional semidiscrete primal. -/
def IsOptimalSemidiscreteAllocation (μ : Measure S) (p : Fin (m + 1) → ℝ)
    (c a : S → Fin (m + 1) → ℝ) : Prop :=
  IsSemidiscreteAllocation μ p a ∧ ∀ b, IsSemidiscreteAllocation μ p b →
    semidiscreteAllocationCost μ c a ≤ semidiscreteAllocationCost μ c b

/-- The actual cavity construction attains the primal for almost every Dirichlet mass vector. -/
theorem ae_exists_optimalSemidiscreteAllocation
    (μ : Measure S) [IsProbabilityMeasure μ]
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hci : ∀ j, Integrable (c j) μ)
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s))) :
    ∀ᵐ p ∂dirichletOne m, ∃ a, IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j s) a := by
  obtain ⟨_, _, hrep, _⟩ := exists_dirichlet_semidiscrete_mean_readout μ c hc hci hatom
    (fun _ _ ↦ 0) (fun _ ↦ measurable_const) (fun _ ↦ integrable_const (0 : ℝ))
  filter_upwards [hrep] with p hp
  obtain ⟨a, ha, hopt, _⟩ := hp
  exact ⟨a, ha, fun b hb ↦ (hopt b hb).1⟩

/-- There is one deterministic countable exceptional set outside which the actual three
optima exist on the same random environment and Dirichlet mass vector. -/
theorem exists_countable_exceptional_opposite_semidiscrete_optima
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : Fin (m + 1) → V → S → ℝ)
    (hc : ∀ j, Measurable (Function.uncurry (c j)))
    (hci : ∀ᵐ v ∂ρ, ∀ j, Integrable (c j v) μ)
    (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c j v s - c l v s)))
    (G : ℝ≥0) (hbound : ∀ v s j, |g j v s| ≤ G) :
    ∃ N : Set ℝ, N.Countable ∧ ∀ t : ℝ, t ∉ N →
      ∀ᵐ v ∂ρ, ∀ᵐ p ∂dirichletOne m, ∃ a₀ aplus aminus : S → Fin (m + 1) → ℝ,
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j v s) a₀ ∧
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j v s + t * g j v s) aplus ∧
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j v s + (-t) * g j v s) aminus := by
  let B : Set ℝ := {t | ¬∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
    (μ.map (fun s ↦ (c j v s + t * g j v s) - (c l v s + t * g l v s)))}
  have hB : B.Countable := countable_bad_parameterized_cavity_tilts μ ρ c g hc hg hatom
  refine ⟨B ∪ Neg.neg '' B, hB.union (hB.image Neg.neg), ?_⟩
  intro t ht
  have hp : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
      (μ.map (fun s ↦ (c j v s + t * g j v s) - (c l v s + t * g l v s))) := by
    by_contra h
    exact ht (Or.inl h)
  have hm : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l → NullSingletonClass
      (μ.map (fun s ↦ (c j v s + (-t) * g j v s) - (c l v s + (-t) * g l v s))) := by
    by_contra h
    exact ht (Or.inr ⟨-t, h, neg_neg t⟩)
  filter_upwards [hci, hatom, hp, hm] with v hcv hav hpv hmv
  have hgv j : Integrable (g j v) μ :=
    (integrable_const (G : ℝ)).mono'
      ((hg j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ by simpa only [Real.norm_eq_abs] using hbound v s j)
  have h0 := ae_exists_optimalSemidiscreteAllocation μ (fun j ↦ c j v)
    (fun j ↦ (hc j).comp (measurable_const.prodMk measurable_id)) hcv hav
  have hplus := ae_exists_optimalSemidiscreteAllocation μ
    (fun j s ↦ c j v s + t * g j v s)
    (fun j ↦ ((hc j).comp (measurable_const.prodMk measurable_id)).add
      (((hg j).comp (measurable_const.prodMk measurable_id)).const_mul t))
    (fun j ↦ (hcv j).add ((hgv j).const_mul t)) hpv
  have hminus := ae_exists_optimalSemidiscreteAllocation μ
    (fun j s ↦ c j v s + (-t) * g j v s)
    (fun j ↦ ((hc j).comp (measurable_const.prodMk measurable_id)).add
      (((hg j).comp (measurable_const.prodMk measurable_id)).const_mul (-t)))
    (fun j ↦ (hcv j).add ((hgv j).const_mul (-t))) hmv
  filter_upwards [h0, hplus, hminus] with p h0p hpp hmp
  obtain ⟨a₀, ha₀⟩ := h0p
  obtain ⟨aplus, hap⟩ := hpp
  obtain ⟨aminus, ham⟩ := hmp
  exact ⟨a₀, aplus, aminus, ha₀, hap, ham⟩

/-- Deterministic positive tilts decrease to zero and construct all three actual optimizers
on one common full-measure environment event and one common full-measure weight event. -/
theorem exists_opposite_semidiscrete_optima_sequence
    (μ : Measure S) [IsProbabilityMeasure μ]
    (ρ : Measure V) [IsProbabilityMeasure ρ]
    (c g : Fin (m + 1) → V → S → ℝ)
    (hc : ∀ j, Measurable (Function.uncurry (c j)))
    (hci : ∀ᵐ v ∂ρ, ∀ j, Integrable (c j v) μ)
    (hg : ∀ j, Measurable (Function.uncurry (g j)))
    (hatom : ∀ᵐ v ∂ρ, ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ c j v s - c l v s)))
    (G : ℝ≥0) (hbound : ∀ v s j, |g j v s| ≤ G) :
    ∃ t : ℕ → ℝ, StrictAnti t ∧ (∀ n, 0 < t n) ∧ Tendsto t atTop (nhds 0) ∧
      ∀ᵐ v ∂ρ, ∀ᵐ p ∂dirichletOne m, ∀ n, ∃ a₀ aplus aminus : S → Fin (m + 1) → ℝ,
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j v s) a₀ ∧
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j v s + t n * g j v s) aplus ∧
        IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c j v s + (-t n) * g j v s) aminus := by
  obtain ⟨N, hN, hgood⟩ := exists_countable_exceptional_opposite_semidiscrete_optima
    μ ρ c g hc hci hg hatom G hbound
  obtain ⟨t, ht, hmem, hlim⟩ := (hN.dense_compl ℝ).exists_seq_strictAnti_tendsto (0 : ℝ)
  refine ⟨t, ht, fun n ↦ (hmem n).1, hlim, ?_⟩
  have hall := ae_all_iff.mpr (fun n ↦ hgood (t n) (hmem n).2)
  filter_upwards [hall] with v hv
  exact ae_all_iff.mpr hv

end OTSelector.Probability

end
end
