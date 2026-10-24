import OTSelector.Probability.CavityCells
import OTSelector.Finite.FractionalUnique
import Mathlib.Probability.Independence.Basic

/-!
# Almost-sure uniqueness for the original iid assignment problem

Each source row is independent of the original retained source array. Atomless differences
between its target costs rule out ties after addition of the exact retained-input vacancy
prices. Every optimal permutation uses that same unique cavity cell, row by row. The original
assignment optimizer, and then its whole fractional optimal face, are therefore unique almost
surely. The source probability space and sample array are not changed.
-/

open MeasureTheory ProbabilityTheory Set Filter

namespace OTSelector.Probability

variable {n : ℕ} {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]

/-- Under iid sampling and atomless target-cost differences, the original optimal assignment
is almost surely unique. The conclusion concerns all optimal permutations. -/
theorem ae_existsUnique_optimalAssignment_of_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : Fin (n + 1) → Ω → S) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c : Fin (n + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun s ↦ c j s - c k s))) :
    ∀ᵐ ω ∂P, ∃! σ, OptimalAssignment (fun i j ↦ c j (X i ω)) σ := by
  classical
  have hrow (i : Fin (n + 1)) : ∀ᵐ ω ∂P,
      ∀ σ τ, OptimalAssignment (fun k j ↦ c j (X k ω)) σ →
        OptimalAssignment (fun k j ↦ c j (X k ω)) τ → σ i = τ i := by
    let W := {k : Fin (n + 1) // k ≠ i} → S
    let W₀ : Ω → W := fun ω k ↦ X k.1 ω
    let retained : W → Fin (n + 1) → Fin (n + 1) → ℝ :=
      fun w k j ↦ if hk : k ≠ i then c j (w ⟨k, hk⟩) else 0
    let row : W × S → Fin (n + 1) → ℝ := fun z j ↦ c j z.2
    have hW : Measurable W₀ := measurable_pi_lambda _ fun k ↦ hX k.1
    have hret : ∀ k j, Measurable (fun w ↦ retained w k j) := by
      intro k j
      by_cases hk : k ≠ i
      · simpa only [retained, dite_eq_left hk, Function.comp_def] using
          (hc j).comp (measurable_pi_apply (⟨k, hk⟩ : {k // k ≠ i}))
      · simpa only [retained, dite_eq_right hk] using
          (measurable_const : Measurable (fun _ : W ↦ (0 : ℝ)))
    have hr : ∀ j, Measurable (fun z ↦ row z j) :=
      fun j ↦ (hc j).comp measurable_snd
    have hi : IndepFun W₀ (X i) P := by
      let A : Finset (Fin (n + 1)) := Finset.univ.erase i
      have hdis : Disjoint A {i} := by simp [A]
      have h := hindep.indepFun_finset A {i} hdis hX
      have hleft : Measurable
          (fun w : (k : A) → S ↦ fun k : {k : Fin (n + 1) // k ≠ i} ↦
            w ⟨k.1, by simp [A, k.2]⟩) :=
        measurable_pi_lambda _ fun _ ↦ measurable_pi_apply _
      exact h.comp hleft (measurable_pi_apply ⟨i, by simp⟩)
    have hup (ω : Ω) : Function.update (retained (W₀ ω)) i (row (W₀ ω, X i ω)) =
        (fun k j ↦ c j (X k ω)) := by
      funext k j
      by_cases hk : k = i
      · subst k
        simp [row]
      · simp [retained, W₀, hk]
    have hcell := ae_existsUnique_mem_cavityCell_of_indepFun_atomless P μ W₀ (X i)
      hW (hX i) hi (hlaw i) retained row hret hr i
      (Filter.Eventually.of_forall fun _ j k hjk ↦ hatom j k hjk)
    filter_upwards [hcell] with ω hω
    obtain ⟨j, _, huniq⟩ := hω
    intro σ τ hσ hτ
    have hσcell : (W₀ ω, X i ω) ∈ cavityCell retained row i (σ i) := by
      apply (mem_cavityCell_iff_exists_optimal_partner retained row i (σ i) _).mpr
      exact ⟨σ, by simpa only [hup] using hσ, rfl⟩
    have hτcell : (W₀ ω, X i ω) ∈ cavityCell retained row i (τ i) := by
      apply (mem_cavityCell_iff_exists_optimal_partner retained row i (τ i) _).mpr
      exact ⟨τ, by simpa only [hup] using hτ, rfl⟩
    exact (huniq (σ i) hσcell).trans (huniq (τ i) hτcell).symm
  filter_upwards [ae_all_iff.mpr hrow] with ω hω
  obtain ⟨σ, hσ⟩ := exists_optimalAssignment (fun i j ↦ c j (X i ω))
  refine ⟨σ, hσ, ?_⟩
  intro τ hτ
  apply Equiv.ext
  intro i
  exact hω i τ σ hτ hσ

/-- Under the same original iid assumptions, the entire fractional optimal face is a singleton. -/
theorem ae_existsUnique_optimalFractionalAssignment_of_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : Fin (n + 1) → Ω → S) (hX : ∀ i, Measurable (X i))
    (hindep : iIndepFun X P) (hlaw : ∀ i, P.map (X i) = μ)
    (c : Fin (n + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j k, j ≠ k → NullSingletonClass (μ.map (fun s ↦ c j s - c k s))) :
    ∀ᵐ ω ∂P, ∃! A, OptimalFractionalAssignment (fun i j ↦ c j (X i ω)) A := by
  filter_upwards [ae_existsUnique_optimalAssignment_of_iid_atomless
    P μ X hX hindep hlaw c hc hatom] with ω hω
  exact existsUnique_optimalFractionalAssignment_of_existsUnique_optimalAssignment _ hω

end OTSelector.Probability
