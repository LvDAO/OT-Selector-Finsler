import OTSelector.Reconstruction.FinslerRelativeLawOriginalCellGoodMarkObservation
import OTSelector.Reconstruction.FinslerConcreteUpperCompactColorSplit

/-! Literal original compact-cell restrictions produce one marked population for all three repairs. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {X Y Z W C T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [MeasurableSpace W] [Fintype C] [Fintype T]
    {π : Measure (X × Y)} [IsFiniteMeasure π]
    (D : PopulationSubcouplingTypes π T) (η : Measure (X × Y)) (hη : η ≤ π)
    (label : X × Y → Z) (coord : T → X × Y → W)
    (cell : C → Set Z) (K : T → C → Set W)

/-- The compact good share of each actual retained original type. -/
def rnCellCompactGoodComponent (t : T) : Measure (X × Y) :=
  compactColorGoodComponent ((D.rnSubplanTypes η hη).component (false, t))
    label (coord t) cell (K t)

/-- The discarded compact-core share remains in its actual original cell and atlas type. -/
def rnCellCompactBadComponent (c : C) (t : T) : Measure (X × Y) :=
  compactColorBadComponent ((D.rnSubplanTypes η hη).component (false, t))
    label (coord t) cell (K t) c

variable (hlabel : Measurable label) (hcoord : ∀ t, Measurable (coord t))
    (hcell : ∀ c, MeasurableSet (cell c)) (hdisjoint : Pairwise (Disjoint on cell))
    (hcover : ∀ t, ∀ᵐ p ∂(D.rnSubplanTypes η hη).component (false, t),
      label p ∈ ⋃ c, cell c)
    (hK : ∀ t c, MeasurableSet (K t c))

include hlabel hcoord hcell hdisjoint hcover hK

/-- Restriction to actual compact cell cores discharges the per-old reconstruction identity. -/
theorem rnCellCompact_split (t : T) :
    D.rnCellCompactGoodComponent η hη label coord cell K t +
      ∑ c, D.rnCellCompactBadComponent η hη label coord cell K c t =
        (D.rnSubplanTypes η hη).component (false, t) :=
  compactColorGood_add_sum_bad_eq _ label (coord t) hlabel (hcoord t)
    cell hcell hdisjoint (hcover t) (K t) (hK t)

/-- A single explicit fine population marking is built from the actual retained compact restrictions. -/
def compactCellRefinedTypes : PopulationSubcouplingTypes π (CellRefinedType C T) :=
  D.rnCellRefinedTypes η hη
    (D.rnCellCompactGoodComponent η hη label coord cell K)
    (D.rnCellCompactBadComponent η hη label coord cell K)
    (D.rnCellCompact_split η hη label coord cell K hlabel hcoord hcell hdisjoint hcover hK)

variable [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (Bool × T))] [MeasurableSingletonClass (Option (Bool × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    {μ : Measure X} {ν : Measure Y} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- One original fine marked experiment simultaneously supplies the unchanged old-T law,
the unchanged retained/residual law, and the original-T good-only hierarchy law. -/
theorem compactCellRefinedTypes_iid_laws {I J : Type*} [Fintype I] [Fintype J]
    (hπ : Vlasov.IsCoupling π μ ν) :
    let R := D.compactCellRefinedTypes η hη label coord cell K
      hlabel hcoord hcell hdisjoint hcover hK
    let A := D.rnSubplanTypes η hη
    let G := R.partialCoarsen cellRefinedGoodType
    let law := (Measure.pi (fun _ : I ↦ R.sourceMarkedLaw μ)).prod
      (Measure.pi (fun _ : J ↦ R.targetMarkedLaw ν))
    law.map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.map cellRefinedOldType))
          (fun sample j ↦ ((sample j).1, (sample j).2.map cellRefinedOldType))) =
      (Measure.pi (fun _ : I ↦ D.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ D.targetMarkedLaw ν)) ∧
    law.map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.map cellRefinedSubplanType))
          (fun sample j ↦ ((sample j).1, (sample j).2.map cellRefinedSubplanType))) =
      (Measure.pi (fun _ : I ↦ A.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ A.targetMarkedLaw ν)) ∧
    law.map
        (Prod.map (fun sample i ↦ ((sample i).1, (sample i).2.bind cellRefinedGoodType))
          (fun sample j ↦ ((sample j).1, (sample j).2.bind cellRefinedGoodType))) =
      (Measure.pi (fun _ : I ↦ G.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : J ↦ G.targetMarkedLaw ν)) := by
  let good := D.rnCellCompactGoodComponent η hη label coord cell K
  let bad := D.rnCellCompactBadComponent η hη label coord cell K
  have hs := D.rnCellCompact_split η hη label coord cell K
    hlabel hcoord hcell hdisjoint hcover hK
  exact ⟨D.rnCellRefinedTypes_iid_old_law η hη good bad hs μ ν,
    D.rnCellRefinedTypes_iid_subplan_law η hη good bad hs μ ν,
    D.rnCellRefinedTypes_iid_good_law η hη good bad hs hπ⟩

end OTSelector.Reconstruction.PopulationSubcouplingTypes
