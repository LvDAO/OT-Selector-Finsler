import OTSelector.Reconstruction.MarkedStationaryValueLegalClassValue
import OTSelector.Finite.MatchingFamily

/-!
# Actual legal block pressure comparison

Choose true legal optima independently in disjoint index blocks, unite their
original edges, and recover the global legal maximum by bounded alternating
chains. The true graph cardinality deficit is retained; no block or global
perfect matching is presumed to exist.
-/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction.PartialMatching
set_option backward.isDefEq.respectTransparency false

variable {m n : ℕ} {β J : Type*} [Fintype β] [Fintype J]

/-- Finite-volume legal subadditivity with the actual block Hall deficits. -/
theorem legalMaximumValue_le_sum_blocks_add_class_deficit
    (allowed : Finset (Fin m × Fin n)) (block : β → Finset (Fin m × Fin n))
    (hsub : ∀ b, block b ⊆ allowed)
    (hrows : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.fst)
      ((block b').image Prod.fst)))
    (hcols : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.snd)
      ((block b').image Prod.snd)))
    (sourceClass : Fin m → J) (sourceAllows : J → Fin n → Prop)
    (hallowed : ∀ i j, (i, j) ∈ allowed ↔ sourceAllows (sourceClass i) j)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    legalMaximumValue allowed c ≤ (∑ b, legalMaximumValue (block b) c) +
      ((legalMaximumCard allowed - ∑ b, legalMaximumCard (block b) : ℕ) : ℝ) *
        ((2 * (Fintype.card J : ℝ) - 1) * B) := by
  classical
  choose σ hlegal hcard hcost using fun b ↦ exists_cost_eq_legalMaximumValue (block b) c
  have hrowSub (b) : (σ b).rows ⊆ (block b).image Prod.fst := by
    intro i hi
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_image.mpr ⟨e, hlegal b he, rfl⟩
  have hcolSub (b) : (σ b).cols ⊆ (block b).image Prod.snd := by
    intro j hj
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_image.mpr ⟨e, hlegal b he, rfl⟩
  have hr : Pairwise (fun b b' ↦ Disjoint (σ b).rows (σ b').rows) :=
    fun b b' hbb' ↦ (hrows hbb').mono (hrowSub b) (hrowSub b')
  have hc : Pairwise (fun b b' ↦ Disjoint (σ b).cols (σ b').cols) :=
    fun b b' hbb' ↦ (hcols hbb').mono (hcolSub b) (hcolSub b')
  let core := OTSelector.PartialMatching.disjointFamily σ hr hc
  have hcore : IsLegal allowed core := by
    intro e he
    obtain ⟨b, _, heb⟩ := Finset.mem_biUnion.mp he
    exact hsub b (hlegal b heb)
  have hvalue := legalMaximumValue_le_cost_add_class_deficit core hcore sourceClass
    sourceAllows hallowed c hB0 hB
  simpa only [core, OTSelector.PartialMatching.disjointFamily_cost,
    OTSelector.PartialMatching.disjointFamily_card, hcost, hcard] using hvalue

end OTSelector.Reconstruction.PartialMatching
