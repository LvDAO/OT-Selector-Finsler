import OTSelector.Finite.CommonSampleMatchingCore
import OTSelector.Finite.LegalMatchingValue
import OTSelector.Finite.MatchingUnion
import OTSelector.Probability.MarkedRelativeLawMatching

/-!
# Legal finite repair on the actual unused endpoint graph

A retained core is completed only through legal edges between its unused rows
and columns. The exact residual capacity identifies when the core extends to a
legal maximum-cardinality matching. The added kinetic cost is the literal
legal residual minimum; no conditional iid property of selected endpoints is
asserted or used.
-/

open Set MeasureTheory
open scoped BigOperators

noncomputable section
namespace OTSelector.Reconstruction.PartialMatching

variable {m n : ℕ}

/-- Legal edges whose source and target have not already been used by the
retained partial matching. -/
def residualAllowed (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n) : Finset (Fin m × Fin n) := by
  classical
  exact allowed.filter fun e ↦ e.1 ∉ σ.rows ∧ e.2 ∉ σ.cols

theorem residualAllowed_subset (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n) : residualAllowed allowed σ ⊆ allowed := by
  classical
  exact Finset.filter_subset _ _

/-- A residual legal matching is disjoint from the core in both capacities. -/
theorem residualAllowed_disjoint {allowed : Finset (Fin m × Fin n)}
    (σ ρ : OTSelector.PartialMatching m n)
    (hρ : IsLegal (residualAllowed allowed σ) ρ) :
    Disjoint σ.rows ρ.rows ∧ Disjoint σ.cols ρ.cols := by
  classical
  constructor
  · apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp (hρ he)).2.1 hi
  · apply Finset.disjoint_left.mpr
    intro j hi hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp (hρ he)).2.2 hi

/-- The core and any residual matching form a legal matching on the original
graph; this includes all clock constraints encoded by `allowed`. -/
theorem isLegal_union_residual {allowed : Finset (Fin m × Fin n)}
    (σ ρ : OTSelector.PartialMatching m n) (hσ : IsLegal allowed σ)
    (hρ : IsLegal (residualAllowed allowed σ) ρ) :
    IsLegal allowed (σ.union ρ (residualAllowed_disjoint σ ρ hρ).1
      (residualAllowed_disjoint σ ρ hρ).2) := by
  intro e he
  rcases Finset.mem_union.mp he with he | he
  · exact hσ he
  · exact residualAllowed_subset allowed σ (hρ he)

/-- The exact residual capacity never exceeds the actual legal maximum. -/
theorem core_add_residualCapacity_le {allowed : Finset (Fin m × Fin n)}
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal allowed σ) :
    σ.card + legalMaximumCard (residualAllowed allowed σ) ≤ legalMaximumCard allowed := by
  obtain ⟨ρ, hρ, hcard⟩ := exists_legalMaximumCard (residualAllowed allowed σ)
  have h := card_le_legalMaximumCard (isLegal_union_residual σ ρ hσ hρ)
  rwa [OTSelector.PartialMatching.card_union, hcard] at h

/-- Actual legal reserve capacity constructs a maximum completion preserving
every retained edge. Its added kinetic cost is exactly the optimal residual
cost on the actual selected unused endpoints. -/
theorem exists_legal_completion_of_residual_capacity
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ)
    (hcapacity : σ.card + legalMaximumCard (residualAllowed allowed σ) =
      legalMaximumCard allowed) (c : Fin m → Fin n → ℝ) :
    ∃ τ : OTSelector.PartialMatching m n,
      IsLegal allowed τ ∧ τ.card = legalMaximumCard allowed ∧ σ.edges ⊆ τ.edges ∧
      (∑ e ∈ τ.edges \ σ.edges, c e.1 e.2) =
        legalMaximumValue (residualAllowed allowed σ) c := by
  classical
  obtain ⟨ρ, hρ, hρcard, hρcost⟩ :=
    exists_cost_eq_legalMaximumValue (residualAllowed allowed σ) c
  obtain ⟨hr, hc⟩ := residualAllowed_disjoint σ ρ hρ
  let τ := σ.union ρ hr hc
  have hdis : Disjoint σ.edges ρ.edges := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    exact (Finset.disjoint_left.mp hr)
      (Finset.mem_image.mpr ⟨e, he, rfl⟩) (Finset.mem_image.mpr ⟨e, he', rfl⟩)
  have hsdiff : τ.edges \ σ.edges = ρ.edges := by
    ext e
    simp only [τ, OTSelector.PartialMatching.union_edges, Finset.mem_sdiff,
      Finset.mem_union]
    constructor
    · rintro ⟨he | he, hn⟩
      · exact (hn he).elim
      · exact he
    · intro he
      exact ⟨Or.inr he, fun hs ↦ Finset.disjoint_left.mp hdis hs he⟩
  refine ⟨τ, isLegal_union_residual σ ρ hσ hρ, ?_, ?_, ?_⟩
  · dsimp only [τ]
    rw [OTSelector.PartialMatching.card_union, hρcard, hcapacity]
  · exact Finset.subset_union_left
  · rw [hsdiff]
    exact hρcost

/-- Any maximum completion forces the same exact residual-capacity identity.
This criterion applies sample by sample, even after inspecting an optimizer. -/
theorem residual_capacity_of_legal_completion
    {allowed : Finset (Fin m × Fin n)} (σ τ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) (hτ : IsLegal allowed τ)
    (hsub : σ.edges ⊆ τ.edges) (hcard : τ.card = legalMaximumCard allowed) :
    σ.card + legalMaximumCard (residualAllowed allowed σ) = legalMaximumCard allowed := by
  classical
  let ρ := τ.subMatching (τ.edges \ σ.edges) Finset.sdiff_subset
  have hρ : IsLegal (residualAllowed allowed σ) ρ := by
    intro e he
    obtain ⟨heτ, hen⟩ := Finset.mem_sdiff.mp he
    apply Finset.mem_filter.mpr
    refine ⟨hτ heτ, ?_, ?_⟩
    · intro hi
      obtain ⟨e', he', hei⟩ := Finset.mem_image.mp hi
      exact hen ((τ.row_inj e heτ e' (hsub he') hei.symm) ▸ he')
    · intro hj
      obtain ⟨e', he', hej⟩ := Finset.mem_image.mp hj
      exact hen ((τ.col_inj e heτ e' (hsub he') hej.symm) ▸ he')
  have hρcard : ρ.card = τ.card - σ.card := Finset.card_sdiff_of_subset hsub
  have hb := card_le_legalMaximumCard hρ
  rw [hρcard] at hb
  have hsle : σ.card ≤ τ.card := Finset.card_le_card hsub
  have hu := core_add_residualCapacity_le σ hσ
  omega

/-- Exact legal residual capacity is equivalent to existence of a completion
which keeps the full core. No complete bipartite or uniform clock assumption
is added. -/
theorem residual_capacity_iff_exists_legal_completion
    {allowed : Finset (Fin m × Fin n)} (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) :
    σ.card + legalMaximumCard (residualAllowed allowed σ) = legalMaximumCard allowed ↔
      ∃ τ : OTSelector.PartialMatching m n,
        IsLegal allowed τ ∧ τ.card = legalMaximumCard allowed ∧ σ.edges ⊆ τ.edges := by
  constructor
  · intro hcapacity
    obtain ⟨τ, hτ, hcard, hsub, -⟩ :=
      exists_legal_completion_of_residual_capacity σ hσ hcapacity (fun _ _ ↦ 0)
    exact ⟨τ, hτ, hcard, hsub⟩
  · rintro ⟨τ, hτ, hcard, hsub⟩
    exact residual_capacity_of_legal_completion σ τ hσ hτ hsub hcard

/-- The optimal residual repair costs no more than the actual residual edges
of any prescribed original legal completion containing the same core. This
permits charging the repair to a previously proved original-subplan energy. -/
theorem legal_residual_value_le_original_completion
    {allowed : Finset (Fin m × Fin n)} (σ τ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ) (hτ : IsLegal allowed τ)
    (hsub : σ.edges ⊆ τ.edges) (hcard : τ.card = legalMaximumCard allowed)
    (c : Fin m → Fin n → ℝ) :
    legalMaximumValue (residualAllowed allowed σ) c ≤
      ∑ e ∈ τ.edges \ σ.edges, c e.1 e.2 := by
  classical
  let ρ := τ.subMatching (τ.edges \ σ.edges) Finset.sdiff_subset
  have hρ : IsLegal (residualAllowed allowed σ) ρ := by
    intro e he
    obtain ⟨heτ, hen⟩ := Finset.mem_sdiff.mp he
    apply Finset.mem_filter.mpr
    refine ⟨hτ heτ, ?_, ?_⟩
    · intro hi
      obtain ⟨e', he', hei⟩ := Finset.mem_image.mp hi
      exact hen ((τ.row_inj e heτ e' (hsub he') hei.symm) ▸ he')
    · intro hj
      obtain ⟨e', he', hej⟩ := Finset.mem_image.mp hj
      exact hen ((τ.col_inj e heτ e' (hsub he') hej.symm) ▸ he')
  have hcapacity := residual_capacity_of_legal_completion σ τ hσ hτ hsub hcard
  have hρcard : ρ.card = τ.card - σ.card := Finset.card_sdiff_of_subset hsub
  have hmax : ρ.card = legalMaximumCard (residualAllowed allowed σ) := by omega
  exact legalMaximumValue_le c hρ hmax

end OTSelector.Reconstruction.PartialMatching

namespace OTSelector.Probability

open OTSelector.PartialMatching OTSelector.Reconstruction.PartialMatching

variable {X Y : Type*} {m n : ℕ}

/-- The partial model matching on exactly the endpoints which common sampling
leaves unchanged. -/
def commonSampleMatching (σ : OTSelector.PartialMatching m n)
    (x x' : Fin m → X) (y y' : Fin n → Y) : OTSelector.PartialMatching m n :=
  σ.subMatching (commonSampleCore σ x x' y y') (commonSampleCore_subset σ x x' y y')

/-- The exact legal residual capacity constructs the actual repair witness
for the law comparison. Its kinetic remainder is the literal minimum on the
unused legal graph. Sample selection is arbitrary and may be adaptive. -/
theorem hasCommonSampleRepair_of_legal_residual_capacity
    (c c' g : X → Y → ℝ) (t : ℝ)
    (x x' : Fin m → X) (y y' : Fin n → Y)
    (σ : OTSelector.PartialMatching m n) (hσ : σ.card = min m n)
    (hopt : σ.cost (fun i j ↦ c (x' i) (y' j) + t * g (x' i) (y' j)) =
      sampledTiltedValue c g t (x', y'))
    (allowed : Finset (Fin m × Fin n))
    (hlegal : commonSampleCore σ x x' y y' ⊆ allowed)
    (hfull : legalMaximumCard allowed = min m n)
    (hcapacity : let S := commonSampleMatching σ x x' y y'
      S.card + legalMaximumCard (residualAllowed allowed S) = legalMaximumCard allowed) :
    let S := commonSampleMatching σ x x' y y'
    HasCommonSampleRepair c c' g t x x' y y'
      (legalMaximumValue (residualAllowed allowed S) (fun i j ↦ c' (x i) (y j))) := by
  let S := commonSampleMatching σ x x' y y'
  obtain ⟨τ, hτ, hτcard, hsub, hcost⟩ :=
    exists_legal_completion_of_residual_capacity S hlegal hcapacity
      (fun i j ↦ c' (x i) (y j))
  refine ⟨σ, τ, hσ, hopt, hτcard.trans hfull, hsub, le_of_eq hcost⟩

end OTSelector.Probability
