import OTSelector.Reconstruction.MarkedStationaryValueLegalActiveTypes
import OTSelector.Reconstruction.MarkedStationaryValueLegalMultiscale
import OTSelector.Reconstruction.MarkedStationaryValueLegalEmbedding

/-! Hierarchical legal repair on the literal original active rows and columns.
Only active source deficiencies are charged, at their actual parent scales. -/
open Set Function
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Summing all proper original optional types counts precisely the active
source indices. Inactive original points are absent from the repair budget. -/
theorem sum_some_blockSizeS_eq_active {m : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (tag : Fin m → Option T) :
    (∑ a : T, blockSizeS tag (some a)) = blockSizeS (fun i ↦ (tag i).isSome) true := by
  classical
  let U := blockFinset (fun i ↦ (tag i).isSome) true
  have hnone : (U.filter (fun i ↦ tag i = none)).card = 0 := by
    have heq : U.filter (fun i ↦ tag i = none) = ∅ := by
      ext i
      by_cases h : tag i = none <;> simp [U, blockFinset, h]
    rw [heq, Finset.card_empty]
  have hsome (a : T) : U.filter (fun i ↦ tag i = some a) = blockFinset tag (some a) := by
    ext i
    simp only [U, blockFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h ↦ h.2
    · intro h
      exact ⟨by simp [h], h⟩
  have h : U.card = ∑ a : Option T, (U.filter (fun i ↦ tag i = a)).card :=
    Finset.card_eq_sum_card_fiberwise (fun _ _ ↦ Finset.mem_univ _)
  simpa only [Fintype.sum_option, hnone, hsome, zero_add, blockSizeS, U] using h.symm

namespace PartialMatching

/-- Restricting to actual active indices commutes with every original spatial
child graph. -/
theorem inducedLegalGraph_spatialLegalBlock_map
    {a b m n : ℕ} {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (allowed : Finset (Fin m × Fin n)) (e : Fin a ↪ Fin m) (f : Fin b ↪ Fin n)
    (s : Fin m → Cell) (t : Fin n → Cell) (c : Cell) :
    inducedLegalGraph (spatialLegalBlock allowed s t c) e f =
      spatialLegalBlock (inducedLegalGraph allowed e f) (s ∘ e) (t ∘ f) c := by
  classical
  ext p
  simp [inducedLegalGraph, spatialLegalBlock]

/-- The original hierarchy's natural deficiencies equal its real source
count minus the sum of actual child legal ranks. -/
theorem sum_spatial_source_defects_eq
    {m n : ℕ} {Cell : Type*} [Fintype Cell] [DecidableEq Cell]
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → Cell) (t : Fin n → Cell) :
    (∑ b : Cell, (((blockFinset s b).card - legalMaximumCard
      (spatialLegalBlock allowed s t b) : ℕ) : ℝ)) =
      (m : ℝ) - ∑ b : Cell, (legalMaximumCard (spatialLegalBlock allowed s t b) : ℝ) := by
  simp_rw [Nat.cast_sub (spatialLegalBlock_source_card_le allowed s t _)]
  rw [Finset.sum_sub_distrib, ← Nat.cast_sum, sum_card_blockFinset]

/-- Repairing the actual original active subcloud pays the real active child
deficiencies at their parent scales. Inactive original observations contribute
neither artificial deficits nor arbitrary global completion costs. -/
theorem legalMaximumValue_le_active_hierarchical_blocks_upto
    {m n : ℕ} {T J : Type*} [Fintype T] [DecidableEq T] [Fintype J]
    {C : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (allowed : Finset (Fin m × Fin n)) (tagS : Fin m → Option T) (tagT : Fin n → Option T)
    (hactive : ∀ p ∈ allowed, (tagS p.1).isSome = true ∧ (tagT p.2).isSome = true)
    (s : (k : ℕ) → Fin m → C k) (t : (k : ℕ) → Fin n → C k)
    (parent : (k : ℕ) → C (k + 1) → C k) (K : ℕ)
    (hs : ∀ k, k < K → ∀ i, parent k (s (k + 1) i) = s k i)
    (ht : ∀ k, k < K → ∀ j, parent k (t (k + 1) j) = t k j)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k, k < K → ∀ i j, (i, j) ∈ allowed → s k i = t k j → |c i j| ≤ B k)
    (root : C 0) (hsroot : ∀ i, s 0 i = root) (htroot : ∀ j, t 0 j = root)
    :
    legalMaximumValue allowed c ≤
      (∑ b : C K, legalMaximumValue (spatialLegalBlock allowed (s K) (t K) b) c) +
      ∑ k ∈ Finset.range K,
        ((∑ a : T, (blockSizeS tagS (some a) : ℝ)) -
          ∑ b : C (k + 1), (legalMaximumCard
            (spatialLegalBlock allowed (s (k + 1)) (t (k + 1)) b) : ℝ)) *
              (2 * (Fintype.card (Option J) : ℝ) * B k) := by
  classical
  let fs : Fin m → Bool := fun i ↦ (tagS i).isSome
  let ft : Fin n → Bool := fun j ↦ (tagT j).isSome
  let e := spatialSourceEmbedding fs true
  let f := spatialTargetEmbedding ft true
  let G := inducedLegalGraph allowed e f
  have hcarry : ∀ p ∈ allowed, p.1 ∈ range e ∧ p.2 ∈ range f := by
    intro p hp
    exact ⟨mem_range_spatialSourceEmbedding fs true p.1 (hactive p hp).1,
      mem_range_spatialTargetEmbedding ft true p.2 (hactive p hp).2⟩
  have hcarryB (k : ℕ) (b : C k) : ∀ p ∈ spatialLegalBlock allowed (s k) (t k) b,
      p.1 ∈ range e ∧ p.2 ∈ range f := by
    intro p hp
    exact hcarry p (Finset.mem_filter.mp hp).1
  have hval : legalMaximumValue G (fun i j ↦ c (e i) (f j)) = legalMaximumValue allowed c :=
    legalMaximumValue_inducedLegalGraph allowed e f hcarry c
  have hleafV (k : ℕ) (b : C k) :
      legalMaximumValue (spatialLegalBlock G (s k ∘ e) (t k ∘ f) b)
        (fun i j ↦ c (e i) (f j)) =
        legalMaximumValue (spatialLegalBlock allowed (s k) (t k) b) c := by
    have h := legalMaximumValue_inducedLegalGraph
      (spatialLegalBlock allowed (s k) (t k) b) e f (hcarryB k b) c
    rw [inducedLegalGraph_spatialLegalBlock_map] at h
    exact h
  have hleafR (k : ℕ) (b : C k) :
      legalMaximumCard (spatialLegalBlock G (s k ∘ e) (t k ∘ f) b) =
        legalMaximumCard (spatialLegalBlock allowed (s k) (t k) b) := by
    have h := legalMaximumCard_inducedLegalGraph
      (spatialLegalBlock allowed (s k) (t k) b) e f (hcarryB k b)
    rw [inducedLegalGraph_spatialLegalBlock_map] at h
    exact h
  have hdef (k : ℕ) :
      (∑ b : C k, (((blockFinset (s k ∘ e) b).card -
        legalMaximumCard (spatialLegalBlock G (s k ∘ e) (t k ∘ f) b) : ℕ) : ℝ)) =
        (∑ a : T, (blockSizeS tagS (some a) : ℝ)) -
          ∑ b : C k, (legalMaximumCard (spatialLegalBlock allowed (s k) (t k) b) : ℝ) := by
    rw [sum_spatial_source_defects_eq]
    have hcount : (blockSizeS fs true : ℝ) = ∑ a : T, (blockSizeS tagS (some a) : ℝ) := by
      exact_mod_cast (sum_some_blockSizeS_eq_active tagS).symm
    rw [hcount]
    simp only [hleafR]
  have h := legalMaximumValue_le_hierarchical_spatial_blocks_upto G
    (fun k ↦ s k ∘ e) (fun k ↦ t k ∘ f) parent K
    (fun k hk i ↦ hs k hk (e i)) (fun k hk j ↦ ht k hk (f j))
    (fun i ↦ sourceClass (e i)) (fun a j ↦ sourceAllows a (f j))
    (by intro i j; exact (by simpa only [G, inducedLegalGraph, Finset.mem_filter,
      Finset.mem_univ, true_and] using hallowed (e i) (f j)))
    (fun i j ↦ c (e i) (f j)) B hB0
    (fun k hk i j hij hcell ↦ hB k hk (e i) (f j) (Finset.mem_filter.mp hij).2 hcell)
    root (fun i ↦ hsroot (e i)) (fun j ↦ htroot (f j))
  simpa only [hval, hleafV, hdef] using h

/-- The unrestricted active hierarchy API follows from finite-depth repair. -/
theorem legalMaximumValue_le_active_hierarchical_blocks
    {m n : ℕ} {T J : Type*} [Fintype T] [DecidableEq T] [Fintype J]
    {C : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (allowed : Finset (Fin m × Fin n)) (tagS : Fin m → Option T) (tagT : Fin n → Option T)
    (hactive : ∀ p ∈ allowed, (tagS p.1).isSome = true ∧ (tagT p.2).isSome = true)
    (s : (k : ℕ) → Fin m → C k) (t : (k : ℕ) → Fin n → C k)
    (parent : (k : ℕ) → C (k + 1) → C k)
    (hs : ∀ k i, parent k (s (k + 1) i) = s k i)
    (ht : ∀ k j, parent k (t (k + 1) j) = t k j)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k i j, (i, j) ∈ allowed → s k i = t k j → |c i j| ≤ B k)
    (root : C 0) (hsroot : ∀ i, s 0 i = root) (htroot : ∀ j, t 0 j = root)
    (K : ℕ) :
    legalMaximumValue allowed c ≤
      (∑ b : C K, legalMaximumValue (spatialLegalBlock allowed (s K) (t K) b) c) +
      ∑ k ∈ Finset.range K,
        ((∑ a : T, (blockSizeS tagS (some a) : ℝ)) -
          ∑ b : C (k + 1), (legalMaximumCard
            (spatialLegalBlock allowed (s (k + 1)) (t (k + 1)) b) : ℝ)) *
              (2 * (Fintype.card (Option J) : ℝ) * B k) := by
  exact legalMaximumValue_le_active_hierarchical_blocks_upto allowed tagS tagT hactive
    s t parent K (fun k _ ↦ hs k) (fun k _ ↦ ht k) sourceClass sourceAllows hallowed
    c B hB0 (fun k _ ↦ hB k) root hsroot htroot

end PartialMatching
end OTSelector.Reconstruction
