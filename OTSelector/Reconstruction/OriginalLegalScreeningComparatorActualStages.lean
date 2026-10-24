import OTSelector.Transport.Finite.ClasswiseAtomRepairEnergy
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorSubarrayCompletion

/-! Actual finite stage transports construct a maximum legal comparator on the
unchanged full input arrays, retaining all original core edges and exact labels. -/
open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 500000
variable {E : Type*} [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E] {m n : ℕ}

/-- True finite stage plans complete the retained core on the actual undeleted
unused subarrays. Exact excess-count bookkeeping proves the maximum cardinality;
the original signed matrix cost is bounded using the real endpoint energies. -/
theorem exists_legalMaximum_originalAtom_comparator_of_actualStages
    (G : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (hσ : PartialMatching.IsLegal G σ)
    (S : Finset (Fin m)) (T : Finset (Fin n))
    (hS : S ⊆ σ.freeRows) (hT : T ⊆ σ.freeCols)
    (hcount : σ.card + S.card = min m n)
    (κ : S → Measure E) (τ : T → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (τ j)]
    (c : S → ℕ) (d : T → ℕ) (x : Fin m → E) (y : Fin n → E)
    (hclasses : ∀ (i : S) (j : T), c i < d j → (i.val, j.val) ∈ G)
    (hκI : ∀ i : S, Integrable (fun u ↦ dist (x i) u ^ 2) (κ i))
    (hτI : ∀ j : T, Integrable (fun v ↦ dist v (y j) ^ 2) (τ j))
    (N : ℕ) (hc : ∀ i, c i < N) (hd : ∀ j, d j < N)
    (ν : ℕ → Measure E) (π : ℕ → Measure (E × E))
    [∀ k, IsFiniteMeasure (ν k)] [∀ k, IsFiniteMeasure (π k)]
    (hν₀ : ν 0 = 0) (hνN : ν N = 0)
    (hπ₁ : ∀ k < N, (π k).fst = ν k + originalAtomSmoothingClassLaw κ c k)
    (hπ₂ : ∀ k < N, (π k).snd = ν (k + 1) + originalAtomSmoothingClassLaw τ d k)
    (hstageCost : ∀ k < N, Integrable (fun p ↦ dist p.1 p.2 ^ 2) (π k))
    (hcolours : ∀ k < N, (∀ i, c i ≠ k) ∨ (∀ j, d j ≠ k))
    (cost : Fin m → Fin n → ℝ) {K B : ℝ} (hK : 0 ≤ K)
    (hcost : ∀ (i : S) (j : T), cost i j ≤ K * dist (x i) (y j) ^ 2 + B) :
    ∃ ζ : OTSelector.PartialMatching m n,
      PartialMatching.IsLegal G ζ ∧ ζ.card = PartialMatching.legalMaximumCard G ∧
      σ.edges ⊆ ζ.edges ∧
      ζ.cost cost ≤ σ.cost cost + K *
        (3 * (N : ℝ) * (∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k) +
          3 * (∑ i, ∫ u, dist (x i) u ^ 2 ∂κ i) +
          3 * (∑ j, ∫ v, dist v (y j) ^ 2 ∂τ j)) + B * S.card ∧
      PartialMatching.legalMaximumValue G cost ≤ ζ.cost cost := by
  classical
  obtain ⟨e, he, henergy⟩ := exists_originalAtoms_strictClassRepair_of_actualStages_deviationEnergy
    κ τ c d (fun i ↦ x i) (fun j ↦ y j) hκI hτI N hc hd ν π
    hν₀ hνN hπ₁ hπ₂ hstageCost hcolours
  obtain ⟨ζ, hζ, hmax, hretained, _, hζcost, _⟩ :=
    PartialMatching.exists_legalMaximum_completion_of_subarrayEquiv G σ hσ S T hS hT hcount e
      (fun i ↦ hclasses i (e i) (he i)) cost
  have hsum : (∑ i : S, cost i (e i)) ≤
      K * (3 * (N : ℝ) * (∑ k ∈ Finset.range N, ∫ p, dist p.1 p.2 ^ 2 ∂π k) +
        3 * (∑ i, ∫ u, dist (x i) u ^ 2 ∂κ i) +
        3 * (∑ j, ∫ v, dist v (y j) ^ 2 ∂τ j)) + B * S.card := by
    calc
      _ ≤ ∑ i : S, (K * dist (x i) (y (e i)) ^ 2 + B) :=
        Finset.sum_le_sum (fun i _ ↦ hcost i (e i))
      _ = K * (∑ i : S, dist (x i) (y (e i)) ^ 2) + B * S.card := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
          Finset.card_univ, Fintype.card_coe, nsmul_eq_mul, mul_comm B]
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left henergy hK) le_rfl
  refine ⟨ζ, hζ, hmax, hretained, ?_, PartialMatching.legalMaximumValue_le cost hζ hmax⟩
  rw [hζcost]
  linarith only [hsum]

end OTSelector.Reconstruction
