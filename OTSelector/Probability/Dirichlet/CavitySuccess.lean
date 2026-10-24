import OTSelector.Finite.AssignmentCavity
import OTSelector.Finite.CapacityAssignment
import OTSelector.Finite.TargetTreeCanonicalSuccess
import OTSelector.Finite.TargetTreePrices
import OTSelector.Probability.IIDCapacityCostUniqueness

/-!
Conditions: Finite measurable random costs; the iid successful-subset statements additionally assume independent equal-law rows, atomless pairwise cost differences, positive capacities and the exact total-capacity identity.

Objects: Measurable retained costs and successful events, the actual iid cost array, almost-sure uniqueness of a successful subset and total successful-subset probability one.

Proof detail: Take finite minima and strict comparisons to obtain measurability. Use iid assignment-cost uniqueness and the deterministic capacity-cavity theorem, then sum a measurable a.e. partition into its uniquely successful event.

References: OTSelector project: main.tex label thm:iid-cavity-dirichlet, line 4290; Rick Durrett: Section 2.1.2, Theorems 2.1.11–2.1.12, p. 48.
Relation: The generic finite event-partition lemma is elementary measure additivity; the existence and uniqueness of successful cavity subsets is the project’s capacity construction.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Probability.CavityDirichletSuccess.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Probability.CavityDirichletSuccess`; the selected original proof blocks follow. -/
section

/-!
# The exact original-law successful-subset probability identity

The successful retained subsets are measurable events computed from their actual cavity
optima. Under the original iid atomless-difference hypothesis, the constructed canonical
tree gives almost surely exactly one success. Summing its event probabilities is therefore
exactly one; no independent successful-subset or tree assumption is imposed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Probability

variable {n m : ℕ} {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]

/-- Measurable actual costs remain measurable after restricting to a fixed candidate. -/
theorem measurable_retainedSubsetCavityCost
    (cost : Ω → Fin (n + 1) → Fin (m + 1) → ℝ)
    (hc : ∀ k j, Measurable (fun ω ↦ cost ω k j))
    (I : {I : Finset (Fin n) // I.card = m}) (i₀ : Fin (n + 1))
    (k j : Fin (m + 1)) :
    Measurable (fun ω ↦ retainedSubsetCavityCost (cost ω) i₀ I k j) := by
  refine Fin.succAboveCases 0 ?_ (fun s ↦ ?_) k
  · simp only [retainedSubsetCavityCost, Fin.insertNth_apply_same]
    exact measurable_const
  · simpa only [retainedSubsetCavityCost_retained] using
      hc (i₀.succAbove (retainedSubsetRowEquiv I s)) j

/-- Each fixed actual candidate's strict success event is measurable. -/
theorem measurableSet_capacitySuccessfulSubset
    (r : Fin (m + 1) → ℕ) (cost : Ω → Fin (n + 1) → Fin (m + 1) → ℝ)
    (hc : ∀ k j, Measurable (fun ω ↦ cost ω k j)) (i₀ : Fin (n + 1))
    (I : {I : Finset (Fin n) // I.card = m}) :
    MeasurableSet {ω | CapacitySuccessfulSubset r (by simp) (cost ω) i₀ I} := by
  classical
  have hp (j : Fin (m + 1)) : Measurable (fun ω ↦
      capacityVacancyPrice (fun _ : Fin (m + 1) ↦ 1) (by simp)
        (retainedSubsetCavityCost (cost ω) i₀ I) 0 j (Nat.zero_lt_succ 0)) := by
    simp_rw [capacityVacancyPrice_unit_eq_assignmentCavityValue]
    exact measurable_assignmentCavityValue _
      (measurable_retainedSubsetCavityCost cost hc I i₀) 0 j
  simp only [CapacitySuccessfulSubset, ofPred_exists]
  apply MeasurableSet.iUnion
  intro s
  by_cases hs : CapacityFeasible (fun j ↦ r j - 1) s
  · simp only [hs, true_and, ofPred_forall]
    apply MeasurableSet.iInter
    intro k
    apply MeasurableSet.iInter
    intro j
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_lt ((hc (i₀.succAbove k) (s k)).add (hp (s k)))
      ((hc (i₀.succAbove k) j).add (hp j))
  · simp only [hs, false_and, ofPred_false]
    exact MeasurableSet.empty

/-- The full cavity matrix of the original retained array, with one artificial deleted row. -/
def iidCapacityInputCost (c : Fin (m + 1) → S → ℝ) (X : Fin n → Ω → S)
    (ω : Ω) : Fin (n + 1) → Fin (m + 1) → ℝ :=
  Fin.insertNth 0 (fun _ ↦ 0) (fun k j ↦ c j (X k ω))

omit [MeasurableSpace Ω] [MeasurableSpace S] in
@[simp]
theorem iidCapacityInputCost_retained (c : Fin (m + 1) → S → ℝ)
    (X : Fin n → Ω → S) (ω : Ω) (k : Fin n) (j : Fin (m + 1)) :
    iidCapacityInputCost c X ω ((0 : Fin (n + 1)).succAbove k) j = c j (X k ω) := by
  simp only [iidCapacityInputCost, Fin.insertNth_apply_succAbove]

/-- Actual iid atomless row differences imply almost surely one successful retained subset. -/
theorem ae_existsUnique_capacitySuccessfulSubset_of_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : Fin n → Ω → S) (hX : ∀ k, Measurable (X k))
    (hindep : iIndepFun X P) (hlaw : ∀ k, P.map (X k) = μ)
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (r : Fin (m + 1) → ℕ) (hr : ∀ j, 0 < r j) (htotal : ∑ j, r j = n + 1) :
    ∀ᵐ ω ∂P, ∃! I : {I : Finset (Fin n) // I.card = m},
      CapacitySuccessfulSubset r (by simp) (iidCapacityInputCost c X ω) 0 I := by
  filter_upwards [ae_injective_capacityAssignmentCost_of_iid_atomless
    P μ X hX hindep hlaw c hc hatom] with ω hω
  apply existsUnique_capacitySuccessfulSubset r htotal hr (by simp) (iidCapacityInputCost c X ω) 0
  intro z a b ha hb
  simp only [iidCapacityInputCost_retained] at ha hb
  exact hω (le_antisymm (ha.2 b hb.1) (hb.2 a ha.1))

/-- On any probability space, measurable finite events that hold uniquely almost surely
have total probability one. -/
theorem sum_measure_eq_one_of_ae_existsUnique {ι : Type*} [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (E : ι → Set Ω)
    (hE : ∀ i, MeasurableSet (E i)) (hunique : ∀ᵐ ω ∂P, ∃! i, ω ∈ E i) :
    ∑ i, P (E i) = 1 := by
  classical
  have hsum : (fun ω ↦ ∑ i, (E i).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω) =ᵐ[P]
      fun _ ↦ 1 := by
    filter_upwards [hunique] with ω hω
    obtain ⟨i, hi, hui⟩ := hω
    rw [Finset.sum_eq_single i]
    · simp only [indicator_of_mem hi]
    · intro j _ hji
      apply indicator_of_notMem
      exact fun hj ↦ hji (hui j hj)
    · exact fun h ↦ (h (Finset.mem_univ i)).elim
  have hlin := lintegral_finsetSum (μ := P)
    (f := fun i ↦ (E i).indicator (fun _ ↦ (1 : ℝ≥0∞))) Finset.univ
    (fun i _ ↦ measurable_const.indicator (hE i))
  rw [lintegral_congr_ae hsum] at hlin
  have hmeasure (i : ι) :
      (∫⁻ ω, (E i).indicator (fun _ ↦ (1 : ℝ≥0∞)) ω ∂P) = P (E i) :=
    lintegral_indicator_one (hE i)
  simp_rw [hmeasure] at hlin
  simpa only [lintegral_one, measure_univ] using hlin.symm

/-- The exact original iid probability identity supplied by the actual canonical target tree. -/
theorem sum_measure_capacitySuccessfulSubset_eq_one_of_iid_atomless
    (P : Measure Ω) [IsProbabilityMeasure P] (μ : Measure S)
    (X : Fin n → Ω → S) (hX : ∀ k, Measurable (X k))
    (hindep : iIndepFun X P) (hlaw : ∀ k, P.map (X k) = μ)
    (c : Fin (m + 1) → S → ℝ) (hc : ∀ j, Measurable (c j))
    (hatom : ∀ j l, j ≠ l → NullSingletonClass (μ.map (fun s ↦ c j s - c l s)))
    (r : Fin (m + 1) → ℕ) (hr : ∀ j, 0 < r j) (htotal : ∑ j, r j = n + 1) :
    ∑ I : {I : Finset (Fin n) // I.card = m},
      P {ω | CapacitySuccessfulSubset r (by simp) (iidCapacityInputCost c X ω) 0 I} = 1 := by
  apply sum_measure_eq_one_of_ae_existsUnique P _
  · intro I
    apply measurableSet_capacitySuccessfulSubset r _ _ 0 I
    intro k j
    refine Fin.succAboveCases 0 ?_ (fun s ↦ ?_) k
    · simp only [iidCapacityInputCost, Fin.insertNth_apply_same]
      exact measurable_const
    · simpa only [iidCapacityInputCost_retained, Function.comp_def] using (hc j).comp (hX s)
  · exact ae_existsUnique_capacitySuccessfulSubset_of_iid_atomless
      P μ X hX hindep hlaw c hc hatom r hr htotal

end OTSelector.Probability

end
end
