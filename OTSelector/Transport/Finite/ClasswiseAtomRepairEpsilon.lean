import OTSelector.Probability.AtomicSmoothingClassLaws
import OTSelector.Transport.Finite.ClasswiseAtomRepairEnergy
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairEpsilonStages.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairEpsilonStages`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.OriginalClasswiseOriginalAtomRepairEpsilonStages

**Conditions:** Every finite stage admits genuine transport within its prescribed budget plus arbitrary δ>0, and original endpoint deviations are integrable.

**Objects:** One exact strict-class original-label bijection satisfying the unslackened total energy budget.

**Proof detail:** Choose simultaneous ε-small stage plans and apply the actual-stage repair theorem; the finite set of legal bijections has an attained minimum, so approximate feasibility for every ε forces that minimum below the exact budget.

**Sources:** [Sheldon Axler, Supplement for Measure, Integration & Real Analysis](https://measure.axler.net/SupplementMIRA.pdf#page=18), Section C, Definitions 0.32 and 0.35, pp. 18–19; [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=21), Section 2.3, Proposition 2.1 and its proof, pp. 17–18 (PDF pages 21–22); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=185), Section 10.1, Remark 10.2, p. 181, gluing lemma preceding (10.4); [Terence Tao, Analysis I](https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean), Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test); [OTSelector project, Original classwise stage Neumann construction](main.tex#eq:interleaved-path-stage-neumann), main.tex label eq:interleaved-path-stage-neumann, line 10809.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-! Genuine epsilon stage transports yield an exact finite original-label repair.
Finiteness removes the approximation slack while retaining the same legal labels. -/
open Set MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

private theorem exists_le_of_finite_epsilon {A : Type*} [Finite A]
    (P : A → Prop) (f : A → ℝ) (B : ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ a, P a ∧ f a ≤ B+ε) :
    ∃ a, P a ∧ f a ≤ B := by
  obtain ⟨a₀, ha₀, -⟩ := h 1 zero_lt_one
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image {a | P a} f (Set.toFinite _) ⟨a₀, ha₀⟩
  refine ⟨a, ha, le_of_forall_pos_le_add (fun ε hε ↦ ?_)⟩
  obtain ⟨b, hb, hbf⟩ := h ε hε
  exact (hmin b hb).trans hbf

variable {E I J : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E] [Fintype I] [Fintype J]

/-- The true finite-stage epsilon producers need no measurable choice or exact
optimal continuous plan. Their actual marginal identities and arbitrary epsilon
budgets produce one exact strict bijection of the unchanged original labels,
including zero stages and empty input types. -/
theorem exists_originalAtoms_strictClassRepair_of_epsilonStages_deviationEnergy
    (κ : I → Measure E) (τ : J → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (τ j)]
    (c : I → ℕ) (d : J → ℕ) (x : I → E) (y : J → E)
    (hκI : ∀ i, Integrable (fun u ↦ dist (x i) u ^ 2) (κ i))
    (hτI : ∀ j, Integrable (fun v ↦ dist v (y j) ^ 2) (τ j))
    (N : ℕ) (hc : ∀ i, c i < N) (hd : ∀ j, d j < N)
    (ν : ℕ → Measure E) [∀ k, IsFiniteMeasure (ν k)]
    (hν₀ : ν 0 = 0) (hνN : ν N = 0) (B : ℕ → ℝ)
    (hstage : ∀ k < N, ∀ δ : ℝ, 0 < δ → ∃ π : Measure (E × E),
      IsFiniteMeasure π ∧
      π.fst = ν k + originalAtomSmoothingClassLaw κ c k ∧
      π.snd = ν (k+1) + originalAtomSmoothingClassLaw τ d k ∧
      Integrable (fun p ↦ dist p.1 p.2^2) π ∧
      (∫ p, dist p.1 p.2^2 ∂π) ≤ B k+δ)
    (hcolours : ∀ k < N, (∀ i, c i ≠ k) ∨ (∀ j, d j ≠ k)) :
    ∃ σ : I ≃ J, (∀ i, c i < d (σ i)) ∧
      (∑ i, dist (x i) (y (σ i))^2) ≤
        3*(N : ℝ)*(∑ k ∈ Finset.range N, B k) +
          3*(∑ i, ∫ u, dist (x i) u^2 ∂κ i) +
          3*(∑ j, ∫ v, dist v (y j)^2 ∂τ j) := by
  classical
  apply exists_le_of_finite_epsilon (fun σ : I ≃ J ↦ ∀ i, c i < d (σ i))
    (fun σ ↦ ∑ i, dist (x i) (y (σ i))^2)
  intro ε hε
  let δ := ε/(1+3*(N : ℝ)^2)
  have hδ : 0 < δ := div_pos hε (by positivity)
  let π : ℕ → Measure (E × E) := fun k ↦
    if hk : k < N then (hstage k hk δ hδ).choose else 0
  have hp (k : ℕ) (hk : k < N) :
      IsFiniteMeasure (π k) ∧
      (π k).fst = ν k + originalAtomSmoothingClassLaw κ c k ∧
      (π k).snd = ν (k+1) + originalAtomSmoothingClassLaw τ d k ∧
      Integrable (fun p ↦ dist p.1 p.2^2) (π k) ∧
      (∫ p, dist p.1 p.2^2 ∂π k) ≤ B k+δ := by
    simpa only [π, dite_eq_left hk] using (hstage k hk δ hδ).choose_spec
  have : ∀ k, IsFiniteMeasure (π k) := by
    intro k
    by_cases hk : k < N
    · exact (hp k hk).1
    · simp only [π, dite_eq_right hk]
      infer_instance
  obtain ⟨σ, hσ, henergy⟩ :=
    exists_originalAtoms_strictClassRepair_of_actualStages_deviationEnergy κ τ c d x y
      hκI hτI N hc hd ν π hν₀ hνN
      (fun k hk ↦ (hp k hk).2.1) (fun k hk ↦ (hp k hk).2.2.1)
      (fun k hk ↦ (hp k hk).2.2.2.1) hcolours
  have hsum : (∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2^2 ∂π k) ≤
      (∑ k ∈ Finset.range N, B k)+(N : ℝ)*δ := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, (B k+δ) :=
        Finset.sum_le_sum (fun k hk ↦ (hp k (Finset.mem_range.mp hk)).2.2.2.2)
      _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have herror : 3*(N : ℝ)*((N : ℝ)*δ) ≤ ε := by
    have heq : δ*(1+3*(N : ℝ)^2) = ε := div_mul_cancel₀ ε (by positivity)
    nlinarith
  refine ⟨σ, hσ, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ 3*(N : ℝ))
  nlinarith only [henergy, hm, herror]
end OTSelector.Reconstruction

end
end
