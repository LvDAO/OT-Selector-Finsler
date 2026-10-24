import OTSelector.Reconstruction.FinslerRelativeLawOriginalFineDeterministicCellTags
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCompactRefinedPopulation

/-! Bad observed types retain their literal original physical cell on the same fine sample. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false

variable {X Y Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [Fintype C] [Fintype T] [DecidableEq T]
    {π : Measure (X × Y)} [IsFiniteMeasure π] (D : PopulationSubcouplingTypes π T)
    (η : Measure (X × Y)) (hη : η ≤ π)
    (good : T → Measure (X × Y)) (bad : C → T → Measure (X × Y))
    (hsplit : ∀ t, good t + ∑ c, bad c t = (D.rnSubplanTypes η hη).component (false, t))
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- Literal joint bad-component cells hold for every bad observed vertex before
any sample-dependent matching is chosen. -/
theorem rnCellRefinedTypes_bad_cell_properties
    (left : X → Z) (right : Y → Z) (hleft : Measurable left) (hright : Measurable right)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (hbad : ∀ c t, ∀ᵐ p ∂bad c t, left p.1 ∈ cell c ∧ right p.2 ∈ cell c)
    (n : ℕ) :
    let R := D.rnCellRefinedTypes η hη good bad hsplit
    let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
    ∀ᵐ sample ∂P,
      (∀ i c t, (sample.1 i).2.bind cellRefinedBadType = some (c, t) →
        left (sample.1 i).1 ∈ cell c ∧
          fineOriginalRetainedCellTag left cell (sample.1 i) = some c) ∧
      (∀ j c t, (sample.2 j).2.bind cellRefinedBadType = some (c, t) →
        right (sample.2 j).1 ∈ cell c ∧
          fineOriginalRetainedCellTag right cell (sample.2 j) = some c) := by
  let R := D.rnCellRefinedTypes η hη good bad hsplit
  let Ps : CellRefinedType C T → X → Prop := fun tag x ↦
    match tag with | .inl _ => True | .inr p => left x ∈ cell p.1
  let Pt : CellRefinedType C T → Y → Prop := fun tag y ↦
    match tag with | .inl _ => True | .inr p => right y ∈ cell p.1
  have hs (tag : CellRefinedType C T) : ∀ᵐ x ∂R.source tag, Ps tag x := by
    cases tag with
    | inl _ => exact Filter.Eventually.of_forall fun _ ↦ trivial
    | inr p =>
      change ∀ᵐ x ∂(bad p.1 p.2).map Prod.fst, left x ∈ cell p.1
      exact (ae_map_iff measurable_fst.aemeasurable (hleft (hcell p.1))).mpr
        ((hbad p.1 p.2).mono fun _ h ↦ h.1)
  have ht (tag : CellRefinedType C T) : ∀ᵐ y ∂R.target tag, Pt tag y := by
    cases tag with
    | inl _ => exact Filter.Eventually.of_forall fun _ ↦ trivial
    | inr p =>
      change ∀ᵐ y ∂(bad p.1 p.2).map Prod.snd, right y ∈ cell p.1
      exact (ae_map_iff measurable_snd.aemeasurable (hright (hcell p.1))).mpr
        ((hbad p.1 p.2).mono fun _ h ↦ h.2)
  have hp := R.iid_marked_type_properties (μ := μ) (ν := ν) (I := Fin n) (J := Fin n)
    Ps Pt hs ht
  dsimp only
  filter_upwards [hp] with sample hsample
  constructor
  · intro i c t hi
    have hmem := hsample.1 i (.inr (c, t))
      ((cellRefinedBadType_bind_some_iff (sample.1 i).2 (c, t)).mp hi)
    exact ⟨hmem, fineOriginalRetainedCellTag_eq_some_of_bad left cell hdisj _ hi hmem⟩
  · intro j c t hj
    have hmem := hsample.2 j (.inr (c, t))
      ((cellRefinedBadType_bind_some_iff (sample.2 j).2 (c, t)).mp hj)
    exact ⟨hmem, fineOriginalRetainedCellTag_eq_some_of_bad right cell hdisj _ hj hmem⟩

end OTSelector.Reconstruction.PopulationSubcouplingTypes

namespace OTSelector.Reconstruction

/-- The actual compact bad pieces inherit both physical cell labels from the
original calibrated common-label law. No separate bad-cell support is assumed. -/
theorem original_rn_compact_bad_joint_cells
    {X Z W C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace W]
    [Fintype C] [Fintype T] {π : Measure (X × X)} [IsFiniteMeasure π]
    (D : PopulationSubcouplingTypes π T) (η : Measure (X × X)) (hη : η ≤ π)
    (a : X → Z) (ha : Measurable a) (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (coord : T → X × X → W) (hcoord : ∀ t, Measurable (coord t))
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : T → C → Set W) (hK : ∀ t c, MeasurableSet (K t c)) :
    ∀ c t, ∀ᵐ p ∂D.rnCellCompactBadComponent η hη
      (fun p ↦ a p.1) coord cell K c t,
      a p.1 ∈ cell c ∧ a p.2 ∈ cell c := by
  intro c t
  have hbad := compactColorBadComponent_ae_mem
    ((D.rnSubplanTypes η hη).component (false, t))
    (fun p ↦ a p.1) (coord t) (ha.comp measurable_fst) (hcoord t) cell hcell (K t) (hK t) c
  have hle : D.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K c t ≤ π :=
    Measure.restrict_le_self.trans ((D.rnSubplanTypes_component_le η hη (false, t)).trans
      (D.component_le t))
  filter_upwards [hbad, ae_mono hle hlabel] with p hp heq
  exact ⟨hp.1, heq ▸ hp.1⟩

end OTSelector.Reconstruction
