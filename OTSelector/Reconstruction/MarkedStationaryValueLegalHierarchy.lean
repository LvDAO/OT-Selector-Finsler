import OTSelector.Reconstruction.MarkedStationaryValueLegalNestedBlocks
import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity

/-!
# Legal matching repair at the actual parent scale

Child optima are repaired separately in each parent. Only actual legal edges
enter the signed cost bound; a zero extension is used solely to apply the
finite augmentation theorem. Summing the parent deficits gives the original
source deficiencies of the children, with a class constant independent of the
number of spatial cells and of the point-cloud sizes.
-/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {β γ J : Type*} [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ] [Fintype J]

omit [Fintype γ] [Fintype J] in
/-- Restricting a finite-class graph to one spatial parent adds only the
empty source neighborhood. -/
theorem spatialLegalBlock_exists_classes
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → γ) (t : Fin n → γ) (p : γ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j) :
    ∃ label : Fin m → Option J, ∃ allows : Option J → Fin n → Prop,
      ∀ i j, (i, j) ∈ spatialLegalBlock allowed s t p ↔ allows (label i) j := by
  classical
  let label : Fin m → Option J := fun i ↦ if s i = p then some (sourceClass i) else none
  let allows : Option J → Fin n → Prop := fun a j ↦
    match a with
    | none => False
    | some a => t j = p ∧ sourceAllows a j
  refine ⟨label, allows, ?_⟩
  intro i j
  by_cases hi : s i = p <;>
    simp [spatialLegalBlock, label, allows, hi, hallowed, and_comm]

/-- The repair in one parent pays its actual legal deficit and the edge bound
of that parent, including both removed and inserted signed edges. -/
theorem legalMaximumValue_parent_le_children
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β)
    (parent : β → γ) (p : γ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, (i, j) ∈ spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p →
      |c i j| ≤ B) :
    legalMaximumValue (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) c ≤
      (∑ b, if parent b = p then legalMaximumValue (spatialLegalBlock allowed s t b) c
        else 0) +
      ((legalMaximumCard (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) -
        ∑ b, if parent b = p then legalMaximumCard (spatialLegalBlock allowed s t b)
          else 0 : ℕ) : ℝ) * (2 * (Fintype.card (Option J) : ℝ) * B) := by
  classical
  let pg := spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p
  let block := spatialLegalBlock pg s t
  obtain ⟨label, allows, hclass⟩ := spatialLegalBlock_exists_classes allowed
    (parent ∘ s) (parent ∘ t) p sourceClass sourceAllows hallowed
  let d := allowedMaskedCost pg c
  have hd : ∀ i j, |d i j| ≤ B := abs_allowedMaskedCost_le pg c hB0 hB
  have hv := legalMaximumValue_le_sum_blocks_add_class_deficit pg block
    (fun _ ↦ Finset.filter_subset _ _) (spatialLegalBlock_pairwise_rows pg s t)
    (spatialLegalBlock_pairwise_cols pg s t) label allows hclass d hB0 hd
  have hc (b) : legalMaximumValue (block b) d = legalMaximumValue (block b) c := by
    apply legalMaximumValue_congr_on_allowed
    intro i j hij
    have hp : (i, j) ∈ pg := (Finset.mem_filter.mp hij).1
    simp only [d, allowedMaskedCost, hp, ite_true]
  have hp : legalMaximumValue pg d = legalMaximumValue pg c :=
    legalMaximumValue_allowedMaskedCost pg c
  have hv' : legalMaximumValue pg c ≤
      (∑ b, legalMaximumValue (block b) c) +
      ((legalMaximumCard pg - ∑ b, legalMaximumCard (block b) : ℕ) : ℝ) *
        (2 * (Fintype.card (Option J) : ℝ) * B) := by
    rw [hp] at hv
    simp only [hc] at hv
    refine hv.trans (add_le_add le_rfl ?_)
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    nlinarith
  simpa only [block, pg, spatialLegalBlock_refine, apply_ite legalMaximumCard,
    apply_ite (fun g ↦ legalMaximumValue g c), legalMaximumCard_empty,
    legalMaximumValue_empty] using hv'

/-- Sum the actual parent repairs. The fixed class constant does not grow
with the number of parents, and the source deficiencies stay on the children. -/
theorem sum_parent_legalMaximumValue_le_children_add_deficits
    (allowed : Finset (Fin m × Fin n)) (s : Fin m → β) (t : Fin n → β)
    (parent : β → γ)
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ i j, (i, j) ∈ allowed → parent (s i) = parent (t j) → |c i j| ≤ B) :
    (∑ p, legalMaximumValue (spatialLegalBlock allowed (parent ∘ s) (parent ∘ t) p) c) ≤
      (∑ b, legalMaximumValue (spatialLegalBlock allowed s t b) c) +
      (∑ b, (((OTSelector.blockFinset s b).card -
        legalMaximumCard (spatialLegalBlock allowed s t b) : ℕ) : ℝ)) *
        (2 * (Fintype.card (Option J) : ℝ) * B) := by
  classical
  have hv (p) := legalMaximumValue_parent_le_children allowed s t parent p
    sourceClass sourceAllows hallowed c hB0 (fun i j hij ↦ by
      obtain ⟨he, hs, ht⟩ := Finset.mem_filter.mp hij
      exact hB i j he (hs.trans ht.symm))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun p _ ↦ hv p)
  have hf : (∑ p : γ, ∑ b : β, if parent b = p then
      legalMaximumValue (spatialLegalBlock allowed s t b) c else 0) =
      ∑ b, legalMaximumValue (spatialLegalBlock allowed s t b) c := by
    rw [Finset.sum_comm]
    simp
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hf] at hsum
  refine hsum.trans (add_le_add le_rfl ?_)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  simpa only [Nat.cast_sum] using
    (Nat.cast_le (α := ℝ)).mpr (sum_parent_legal_deficit_le_source_deficits allowed s t parent)

end OTSelector.Reconstruction.PartialMatching
