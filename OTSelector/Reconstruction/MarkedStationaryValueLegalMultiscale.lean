import OTSelector.Reconstruction.MarkedStationaryValueLegalHierarchy
import OTSelector.Reconstruction.MarkedStationaryValueLegalScalarRepair

/-!
# Multiscale repair of actual legal matching values

The partitions are finite bookkeeping of spatial cells. Their refinement maps
are the only nesting data. The same original legal graph and signed cost are
used at every level, and each repair is paid at its parent scale.
-/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

namespace PartialMatching

/-- The true legal optimum is bounded by actual leaf optima and the sum of
original child source deficiencies weighted at their parent scales. -/
theorem legalMaximumValue_le_hierarchical_spatial_blocks_upto
    {m n : ℕ} {J : Type*} [Fintype J]
    {C : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (allowed : Finset (Fin m × Fin n))
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
        (∑ b : C (k + 1), (((OTSelector.blockFinset (s (k + 1)) b).card -
          legalMaximumCard (spatialLegalBlock allowed (s (k + 1)) (t (k + 1)) b) : ℕ) : ℝ)) *
            (2 * (Fintype.card (Option J) : ℝ) * B k) := by
  classical
  let value : ℕ → ℝ := fun k ↦
    ∑ b : C k, legalMaximumValue (spatialLegalBlock allowed (s k) (t k) b) c
  let error : ℕ → ℝ := fun k ↦
    (∑ b : C (k + 1), (((OTSelector.blockFinset (s (k + 1)) b).card -
      legalMaximumCard (spatialLegalBlock allowed (s (k + 1)) (t (k + 1)) b) : ℕ) : ℝ)) *
        (2 * (Fintype.card (Option J) : ℝ) * B k)
  have hstep (k) (hk : k < K) : value k ≤ value (k + 1) + error k := by
    have hsfun : parent k ∘ s (k + 1) = s k := funext (hs k hk)
    have htfun : parent k ∘ t (k + 1) = t k := funext (ht k hk)
    have hv := sum_parent_legalMaximumValue_le_children_add_deficits allowed
      (s (k + 1)) (t (k + 1)) (parent k) sourceClass sourceAllows hallowed c (hB0 k)
      (fun i j hij hcell ↦ hB k hk i j hij (by simpa only [hs k hk, ht k hk] using hcell))
    simpa only [hsfun, htfun, value, error] using hv
  have hgraph (b : C 0) : spatialLegalBlock allowed (s 0) (t 0) b =
      if b = root then allowed else ∅ := by
    ext e
    by_cases hb : b = root
    · subst b
      simp [spatialLegalBlock, hsroot, htroot]
    · simp [spatialLegalBlock, hsroot, htroot, hb, Ne.symm hb]
  have hroot : value 0 = legalMaximumValue allowed c := by
    simp [value, hgraph, apply_ite (fun g ↦ legalMaximumValue g c)]
  have htotal (L : ℕ) (hL : L ≤ K) : value 0 ≤ value L + ∑ k ∈ Finset.range L, error k := by
    induction L with
    | zero => simp
    | succ L ih =>
      have h := hstep L (Nat.lt_of_lt_of_le (Nat.lt_succ_self L) hL)
      have hprev := ih (Nat.le_trans (Nat.le_succ L) hL)
      rw [Finset.sum_range_succ]
      linarith
  simpa only [hroot, value, error] using htotal K le_rfl

/-- The unrestricted hierarchy API follows from the finite-depth version. -/
theorem legalMaximumValue_le_hierarchical_spatial_blocks
    {m n : ℕ} {J : Type*} [Fintype J]
    {C : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (allowed : Finset (Fin m × Fin n))
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
        (∑ b : C (k + 1), (((OTSelector.blockFinset (s (k + 1)) b).card -
          legalMaximumCard (spatialLegalBlock allowed (s (k + 1)) (t (k + 1)) b) : ℕ) : ℝ)) *
            (2 * (Fintype.card (Option J) : ℝ) * B k) := by
  exact legalMaximumValue_le_hierarchical_spatial_blocks_upto allowed s t parent K
    (fun k _ ↦ hs k) (fun k _ ↦ ht k) sourceClass sourceAllows hallowed c B hB0
    (fun k _ ↦ hB k) root hsroot htroot

end PartialMatching

/-- Original scalar supports produce the finite source classes internally.
The spatial partitions introduce no balance or geometric-rank requirement. -/
theorem FiniteScalarBins.legalMaximumValue_le_hierarchical_spatial_blocks
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ)
    (hsource : ∀ i, source i ∈ I) (hsep : ∀ i j, gap ≤ |target j - source i|)
    {C : ℕ → Type*} [∀ k, Fintype (C k)] [∀ k, DecidableEq (C k)]
    (s : (k : ℕ) → Fin m → C k) (t : (k : ℕ) → Fin n → C k)
    (parent : (k : ℕ) → C (k + 1) → C k)
    (hs : ∀ k i, parent k (s (k + 1) i) = s k i)
    (ht : ∀ k j, parent k (t (k + 1) j) = t k j)
    (c : Fin m → Fin n → ℝ) (B : ℕ → ℝ) (hB0 : ∀ k, 0 ≤ B k)
    (hB : ∀ k i j, (i, j) ∈ scalarClockLegalGraph source target →
      s k i = t k j → |c i j| ≤ B k)
    (root : C 0) (hsroot : ∀ i, s 0 i = root) (htroot : ∀ j, t 0 j = root)
    (K : ℕ) :
    PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c ≤
      (∑ b : C K, PartialMatching.legalMaximumValue
        (PartialMatching.spatialLegalBlock (scalarClockLegalGraph source target) (s K) (t K) b) c) +
      ∑ k ∈ Finset.range K,
        (∑ b : C (k + 1), (((OTSelector.blockFinset (s (k + 1)) b).card -
          PartialMatching.legalMaximumCard (PartialMatching.spatialLegalBlock
            (scalarClockLegalGraph source target) (s (k + 1)) (t (k + 1)) b) : ℕ) : ℝ)) *
            (2 * ((D.count : ℝ) + 1) * B k) := by
  obtain ⟨label, allows, hallowed⟩ := D.exists_source_neighborhood_classes hgap source target
    hsource hsep
  simpa only [Fintype.card_option, Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
    PartialMatching.legalMaximumValue_le_hierarchical_spatial_blocks
      (scalarClockLegalGraph source target) s t parent hs ht label allows hallowed
      c B hB0 hB root hsroot htroot K

end OTSelector.Reconstruction
