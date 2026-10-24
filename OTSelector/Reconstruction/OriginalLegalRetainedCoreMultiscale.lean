import OTSelector.Reconstruction.FinslerOriginalCollarValueDensity
import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveHierarchy

/-! Retaining the same finite core while paying residual repair at its true
spatial parent scales. Used original observations do not enter the deficiencies. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

/-- Exact legal capacity compares the original signed minimum to the retained
cost plus the true residual signed minimum, with no ambient edge bound. -/
theorem legalMaximumValue_le_core_add_residual
    {m n : ℕ} {allowed : Finset (Fin m × Fin n)}
    (σ : OTSelector.PartialMatching m n) (hσ : IsLegal allowed σ)
    (hcapacity : σ.card + legalMaximumCard (residualAllowed allowed σ) =
      legalMaximumCard allowed) (c : Fin m → Fin n → ℝ) :
    legalMaximumValue allowed c ≤ σ.cost c +
      legalMaximumValue (residualAllowed allowed σ) c := by
  obtain ⟨τ,hτ,hcard,hsub,hadded⟩ :=
    exists_legal_completion_of_residual_capacity σ hσ hcapacity c
  have hcost := cost_eq_add_cost_sdiff hsub c
  rw [hadded] at hcost
  exact (legalMaximumValue_le c hτ hcard).trans_eq hcost

/-- Original source-neighborhood classes induce residual classes by adjoining
one empty neighborhood for already used source observations. -/
theorem residualAllowed_source_classes
    {m n : ℕ} {J : Type*} (allowed : Finset (Fin m × Fin n))
    (σ : OTSelector.PartialMatching m n)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i,j) ∈ allowed ↔ sourceAllows (sourceClass i) j) :
    ∃ label : Fin m → Option J, ∃ allows : Option J → Fin n → Prop,
      ∀ i j, (i,j) ∈ residualAllowed allowed σ ↔ allows (label i) j := by
  classical
  refine ⟨fun i ↦ if i ∈ σ.rows then none else some (sourceClass i),
    fun a j ↦ match a with
      | none => False
      | some a => j ∉ σ.cols ∧ sourceAllows a j, ?_⟩
  intro i j
  by_cases hi : i ∈ σ.rows <;>
    simp [residualAllowed,hi,hallowed,and_comm]

/-- The same retained core admits the existing active hierarchy estimate on
its original unused graph. Only actual free rows enter each child deficiency;
the signed cost and the original spatial partitions are retained exactly. -/
theorem legalMaximumValue_le_core_add_active_hierarchy
    {m n : ℕ} {J : Type*} [Fintype J]
    {C : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (allowed : Finset (Fin m × Fin n)) (σ : OTSelector.PartialMatching m n)
    (hσ : IsLegal allowed σ)
    (hcapacity : σ.card + legalMaximumCard (residualAllowed allowed σ) =
      legalMaximumCard allowed)
    (s : (k : ℕ) → Fin m → C k) (t : (k : ℕ) → Fin n → C k)
    (parent : (k : ℕ) → C (k + 1) → C k) (K : ℕ)
    (hs : ∀ k, k < K → ∀ i, parent k (s (k + 1) i) = s k i)
    (ht : ∀ k, k < K → ∀ j, parent k (t (k + 1) j) = t k j)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i,j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k, k < K → ∀ i j, (i,j) ∈ allowed →
      s k i = t k j → |c i j| ≤ B k)
    (root : C 0) (hsroot : ∀ i, s 0 i = root) (htroot : ∀ j, t 0 j = root) :
    legalMaximumValue allowed c ≤ σ.cost c +
      (∑ b : C K, legalMaximumValue
        (spatialLegalBlock (residualAllowed allowed σ) (s K) (t K) b) c) +
      ∑ k ∈ Finset.range K,
        (((m - σ.card : ℕ) : ℝ) - ∑ b : C (k + 1),
          (legalMaximumCard (spatialLegalBlock (residualAllowed allowed σ)
            (s (k + 1)) (t (k + 1)) b) : ℝ)) *
          (2 * (Fintype.card J + 2 : ℕ) * B k) := by
  classical
  let tagS : Fin m → Option Unit := fun i ↦ if i ∈ σ.rows then none else some ()
  let tagT : Fin n → Option Unit := fun j ↦ if j ∈ σ.cols then none else some ()
  have hactive : ∀ p ∈ residualAllowed allowed σ,
      (tagS p.1).isSome = true ∧ (tagT p.2).isSome = true := by
    intro p hp
    have hfree := (Finset.mem_filter.mp hp).2
    simp [tagS,tagT,hfree.1,hfree.2]
  obtain ⟨label,allows,hclasses⟩ :=
    residualAllowed_source_classes allowed σ sourceClass sourceAllows hallowed
  have htag : blockFinset tagS (some ()) = σ.freeRows := by
    ext i
    simp [blockFinset,tagS,OTSelector.PartialMatching.freeRows]
  have hcount : (∑ a : Unit, (blockSizeS tagS (some a) : ℝ)) =
      ((m - σ.card : ℕ) : ℝ) := by
    simp only [Fintype.sum_unique,blockSizeS,htag,freeRows_card]
  have h := legalMaximumValue_le_active_hierarchical_blocks_upto
    (residualAllowed allowed σ) tagS tagT hactive s t parent K hs ht label allows hclasses
    c B hB0
    (fun k hk i j hij hcell ↦ hB k hk i j (residualAllowed_subset allowed σ hij) hcell)
    root hsroot htroot
  rw [hcount] at h
  have hcard : Fintype.card (Option (Option J)) = Fintype.card J + 2 := by
    simp only [Fintype.card_option]
  rw [hcard] at h
  have hbase := legalMaximumValue_le_core_add_residual σ hσ hcapacity c
  linarith

end OTSelector.Reconstruction.PartialMatching
