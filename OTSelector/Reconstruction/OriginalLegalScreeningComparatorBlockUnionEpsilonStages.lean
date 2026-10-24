import OTSelector.Reconstruction.OriginalLegalScreeningComparatorBlockUnionUnused
import OTSelector.Transport.Finite.ClasswiseAtomRepairEpsilon

/-! Actual finite epsilon-stage transports on unused original block atoms yield a legal maximum. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction.PartialMatching
variable {m n : ℕ} {β E : Type*} [Fintype β] [LinearOrder β]
  [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [StandardBorelSpace E] [Nonempty E]

/-- Literal stage budgets and literal smoothing deviations of one original unused block. -/
def originalUnusedBlockStageRepairBudget
    (κ : Fin m → Measure E) (τ : Fin n → Measure E) (x : Fin m → E) (y : Fin n → E)
    (S : Finset (Fin m)) (T : Finset (Fin n)) (N : ℕ) (B : ℕ → ℝ) : ℝ :=
  3*(N : ℝ)*(∑ k ∈ Finset.range N, B k) +
    3*(∑ i : S, ∫ u, dist (x i.val) u^2 ∂κ i.val) +
    3*(∑ j : T, ∫ v, dist v (y j.val)^2 ∂τ j.val)

/-- Genuine local epsilon-stage plans construct the block repairs on the original unused
labels. Their actual marginal identities and smoothing energies are consumed directly;
no local finished matching, residual capacity or prescribed global rank is assumed.
The result preserves the original core and attains the actual legal graph maximum,
paying the local physical stage budgets plus the true block count discrepancies. -/
theorem exists_legalMaximum_of_ordered_unused_block_epsilonStages
    (G : Finset (Fin m × Fin n)) (blockS : Fin m → β) (blockT : Fin n → β)
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal G σ)
    (hsame : ∀ e ∈ σ.edges, blockS e.1 = blockT e.2)
    (hforward : ∀ i j, (i,j) ∈ G → blockS i ≤ blockT j)
    (hcomplete : ∀ i j, blockS i < blockT j → (i,j) ∈ G)
    (S : β → Finset (Fin m)) (T : β → Finset (Fin n))
    (hS : ∀ b, S b ⊆ σ.freeRows) (hT : ∀ b, T b ⊆ σ.freeCols)
    (hSb : ∀ b i, i ∈ S b → blockS i = b)
    (hTb : ∀ b j, j ∈ T b → blockT j = b)
    (hcount : ∀ b, (σ.edges.filter (fun e ↦ blockS e.1 = b)).card + (S b).card =
      min (Finset.univ.filter (fun i ↦ blockS i = b)).card
        (Finset.univ.filter (fun j ↦ blockT j = b)).card)
    (κ : Fin m → Measure E) (τ : Fin n → Measure E)
    [∀ i, IsProbabilityMeasure (κ i)] [∀ j, IsProbabilityMeasure (τ j)]
    (clockS : Fin m → ℕ) (clockT : Fin n → ℕ) (x : Fin m → E) (y : Fin n → E)
    (hclockLegal : ∀ b (i : S b) (j : T b), clockS i.val < clockT j.val → (i.val,j.val) ∈ G)
    (hκI : ∀ i, Integrable (fun u ↦ dist (x i) u^2) (κ i))
    (hτI : ∀ j, Integrable (fun v ↦ dist v (y j)^2) (τ j))
    (N : β → ℕ) (hc : ∀ b (i : S b), clockS i.val < N b)
    (hd : ∀ b (j : T b), clockT j.val < N b)
    (ν : β → ℕ → Measure E) [∀ b k, IsFiniteMeasure (ν b k)]
    (hν₀ : ∀ b, ν b 0 = 0) (hνN : ∀ b, ν b (N b) = 0) (B : β → ℕ → ℝ)
    (hstage : ∀ b k, k < N b → ∀ δ : ℝ, 0 < δ → ∃ π : Measure (E × E),
      IsFiniteMeasure π ∧
      π.fst = ν b k + originalAtomSmoothingClassLaw (fun i : S b ↦ κ i.val) (fun i ↦ clockS i.val) k ∧
      π.snd = ν b (k+1) + originalAtomSmoothingClassLaw (fun j : T b ↦ τ j.val) (fun j ↦ clockT j.val) k ∧
      Integrable (fun p ↦ dist p.1 p.2^2) π ∧ (∫ p, dist p.1 p.2^2 ∂π) ≤ B b k+δ)
    (hcolours : ∀ b k, k < N b → (∀ i : S b, clockS i.val ≠ k) ∨ (∀ j : T b, clockT j.val ≠ k))
    (C : ℝ) (hC : 0 ≤ C)
    (hcrossCost : ∀ i j, blockS i < blockT j → dist (x i) (y j)^2 ≤ C) :
    ∃ extra γ : OTSelector.PartialMatching m n,
      IsLegal G γ ∧ γ.card = legalMaximumCard G ∧ σ.edges ⊆ γ.edges ∧
      (∀ e ∈ extra.edges, blockS e.1 < blockT e.2) ∧
      extra.card ≤ ∑ b, Nat.dist (Finset.univ.filter (fun i ↦ blockS i = b)).card
        (Finset.univ.filter (fun j ↦ blockT j = b)).card ∧
      γ.cost (fun i j ↦ dist (x i) (y j)^2) ≤ σ.cost (fun i j ↦ dist (x i) (y j)^2) +
        (∑ b, originalUnusedBlockStageRepairBudget κ τ x y (S b) (T b) (N b) (B b)) +
        C*((∑ b, Nat.dist (Finset.univ.filter (fun i ↦ blockS i = b)).card
          (Finset.univ.filter (fun j ↦ blockT j = b)).card : ℕ) : ℝ) := by
  classical
  let cost : Fin m → Fin n → ℝ := fun i j ↦ dist (x i) (y j)^2
  have hlocal (b : β) : ∃ ζ : OTSelector.PartialMatching m n,
      IsLegal G ζ ∧ (∀ e ∈ ζ.edges, blockS e.1 = b ∧ blockT e.2 = b) ∧
      (∀ e ∈ σ.edges, blockS e.1 = b → e ∈ ζ.edges) ∧
      ζ.card = min (Finset.univ.filter (fun i ↦ blockS i = b)).card
        (Finset.univ.filter (fun j ↦ blockT j = b)).card ∧
      ζ.cost cost ≤ (∑ e ∈ σ.edges.filter (fun e ↦ blockS e.1 = b), cost e.1 e.2) +
        originalUnusedBlockStageRepairBudget κ τ x y (S b) (T b) (N b) (B b) := by
    obtain ⟨e,he,henergy⟩ := exists_originalAtoms_strictClassRepair_of_epsilonStages_deviationEnergy
      (fun i : S b ↦ κ i.val) (fun j : T b ↦ τ j.val)
      (fun i ↦ clockS i.val) (fun j ↦ clockT j.val) (fun i ↦ x i.val) (fun j ↦ y j.val)
      (fun i ↦ hκI i.val) (fun j ↦ hτI j.val) (N b) (hc b) (hd b) (ν b) (hν₀ b) (hνN b)
      (B b) (hstage b) (hcolours b)
    obtain ⟨ζ,hlegal,hlabels,hkeep,hcard,hcost⟩ := exists_blockMatching_of_unused_equiv
      G blockS blockT σ hσ hsame b (S b) (T b) (hS b) (hT b) (hSb b) (hTb b) e
      (fun i ↦ hclockLegal b i (e i) (he i)) (hcount b)
    refine ⟨ζ,hlegal,hlabels,hkeep,hcard,?_⟩
    rw [hcost cost]
    exact add_le_add le_rfl henergy
  choose ζ hlegal hlabels hkeep hcard henergy using hlocal
  obtain ⟨extra,γ,hγ,hmax,hσkeep,_,_,hstrict,hdiscrep,hcost⟩ :=
    exists_legalMaximum_of_ordered_block_matchings G blockS blockT σ ζ hlabels hlegal
      (fun e he ↦ hkeep (blockS e.1) e he rfl) hcard hforward hcomplete
  refine ⟨extra,γ,hγ,hmax,hσkeep,hstrict,hdiscrep,?_⟩
  have htotal := (hcost cost).2 C hC (fun e he ↦ hcrossCost _ _ (hstrict e he))
  have hsum : (∑ b, (ζ b).cost cost) ≤ σ.cost cost +
      ∑ b, originalUnusedBlockStageRepairBudget κ τ x y (S b) (T b) (N b) (B b) := by
    calc
      _ ≤ ∑ b, ((∑ e ∈ σ.edges.filter (fun e ↦ blockS e.1 = b), cost e.1 e.2) +
          originalUnusedBlockStageRepairBudget κ τ x y (S b) (T b) (N b) (B b)) :=
        Finset.sum_le_sum (fun b _ ↦ henergy b)
      _ = _ := by rw [Finset.sum_add_distrib,sum_block_core_cost]
  exact htotal.trans (add_le_add hsum le_rfl)

end OTSelector.Reconstruction.PartialMatching
