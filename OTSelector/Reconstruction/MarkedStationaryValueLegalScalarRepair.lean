import OTSelector.Reconstruction.MarkedStationaryValueLegalClassValue
import OTSelector.Reconstruction.MarkedStationaryValueLegalTypes
import OTSelector.Reconstruction.MarkedStationaryValueLegalBlock

/-!
# Legal scalar-bin recovery without a neighborhood-constancy premise

All opposite-color scalar support values are separated by the original gap.
The original finite bins then give identical legal target neighborhoods to
all source observations in one bin. The actual clock graph therefore admits
the finite-class augmentation bound, including arbitrary interleaving.
-/

open Set Function
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Close source scalars separated from a target by the original gap have
the same strict clock order relative to that target. -/
theorem scalar_forward_iff_of_close_sources {s s' t gap : ℝ}
    (hclose : |s - s'| < gap)
    (hsep : gap ≤ |t - s|) (hsep' : gap ≤ |t - s'|) :
    s < t ↔ s' < t := by
  constructor
  · intro h
    by_contra hn
    have hn' : t ≤ s' := le_of_not_gt hn
    rw [abs_of_nonpos (by linarith : t - s' ≤ 0)] at hsep'
    have hdiff : s' - s ≤ |s - s'| := by simpa only [neg_sub] using neg_le_abs (s - s')
    linarith
  · intro h
    by_contra hn
    have hn' : t ≤ s := le_of_not_gt hn
    rw [abs_of_nonpos (by linarith : t - s ≤ 0)] at hsep
    have hdiff : s - s' ≤ |s - s'| := le_abs_self _
    linarith

/-- Original compact scalar bins produce the source-class graph themselves;
no constant-neighborhood condition is supplied on the sampled graph. -/
theorem FiniteScalarBins.exists_source_neighborhood_classes
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ)
    (hsource : ∀ i, source i ∈ I)
    (hsep : ∀ i j, gap ≤ |target j - source i|) :
    ∃ label : Fin m → Fin D.count, ∃ allows : Fin D.count → Fin n → Prop,
      ∀ i j, (i, j) ∈ scalarClockLegalGraph source target ↔ allows (label i) j := by
  classical
  have hbins (i : Fin m) : ∃ b : Fin D.count, source i ∈ D.cell b := by
    have h := hsource i
    rw [← D.union_eq] at h
    exact mem_iUnion.mp h
  choose label hlabel using hbins
  let allows : Fin D.count → Fin n → Prop :=
    fun a j ↦ ∃ i, label i = a ∧ source i < target j
  have hsame (i i' : Fin m) (heq : label i = label i') (j : Fin n) :
      source i < target j ↔ source i' < target j := by
    apply scalar_forward_iff_of_close_sources _ (hsep i j) (hsep i' j)
    have hd := D.diameter (label i) (source i) (hlabel i) (source i') (heq.symm ▸ hlabel i')
    linarith
  have hallowed (i j) : (i, j) ∈ scalarClockLegalGraph source target ↔ allows (label i) j := by
    simp only [scalarClockLegalGraph, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h ↦ ⟨i, rfl, h⟩,
      fun ⟨i', hi', hforward⟩ ↦ (hsame i' i hi' j).mp hforward⟩
  exact ⟨label, allows, hallowed⟩

/-- The actual scalar graph is repaired using its produced finite source
classes and its true missing legal cardinality. -/
theorem FiniteScalarBins.legalMaximumValue_le_cost_add_deficit
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    {m n : ℕ} (source : Fin m → ℝ) (target : Fin n → ℝ)
    (hsource : ∀ i, source i ∈ I)
    (hsep : ∀ i j, gap ≤ |target j - source i|)
    (σ : OTSelector.PartialMatching m n)
    (hσ : PartialMatching.IsLegal (scalarClockLegalGraph source target) σ)
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c ≤
      σ.cost c +
        ((PartialMatching.legalMaximumCard (scalarClockLegalGraph source target) -
          σ.card : ℕ) : ℝ) * ((2 * (D.count : ℝ) - 1) * B) := by
  obtain ⟨label, allows, hallowed⟩ := D.exists_source_neighborhood_classes hgap source target
    hsource hsep
  simpa only [Fintype.card_fin] using
    PartialMatching.legalMaximumValue_le_cost_add_class_deficit σ hσ label allows hallowed
      c hB0 hB

/-- Actual legal block optima glue with the scalar bins' fixed cardinality
constant; no separate finite-class graph condition is imposed. -/
theorem FiniteScalarBins.legalMaximumValue_le_sum_blocks_add_deficit
    {I : Set ℝ} {gap : ℝ} (D : FiniteScalarBins I gap) (hgap : 0 < gap)
    {m n : ℕ} {β : Type*} [Fintype β]
    (source : Fin m → ℝ) (target : Fin n → ℝ)
    (hsource : ∀ i, source i ∈ I)
    (hsep : ∀ i j, gap ≤ |target j - source i|)
    (block : β → Finset (Fin m × Fin n))
    (hsub : ∀ b, block b ⊆ scalarClockLegalGraph source target)
    (hrows : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.fst)
      ((block b').image Prod.fst)))
    (hcols : Pairwise (fun b b' ↦ Disjoint ((block b).image Prod.snd)
      ((block b').image Prod.snd)))
    (c : Fin m → Fin n → ℝ) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ i j, |c i j| ≤ B) :
    PartialMatching.legalMaximumValue (scalarClockLegalGraph source target) c ≤
      (∑ b, PartialMatching.legalMaximumValue (block b) c) +
        ((PartialMatching.legalMaximumCard (scalarClockLegalGraph source target) -
          ∑ b, PartialMatching.legalMaximumCard (block b) : ℕ) : ℝ) *
          ((2 * (D.count : ℝ) - 1) * B) := by
  obtain ⟨label, allows, hallowed⟩ := D.exists_source_neighborhood_classes hgap source target
    hsource hsep
  simpa only [Fintype.card_fin] using
    PartialMatching.legalMaximumValue_le_sum_blocks_add_class_deficit
      (scalarClockLegalGraph source target) block hsub hrows hcols label allows hallowed
      c hB0 hB

end OTSelector.Reconstruction
