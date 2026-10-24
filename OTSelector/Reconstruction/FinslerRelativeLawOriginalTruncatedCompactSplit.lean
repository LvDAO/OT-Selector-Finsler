import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedTypeRestriction
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCompactRefinedPopulation

/-! Actual deterministic truncation supplies the retained cell cover for fixed compact refinements. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction.PopulationSubcouplingTypes
set_option backward.isDefEq.respectTransparency false

variable {X Z W C T : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [MeasurableSpace W] [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (D : PopulationSubcouplingTypes (χ + ξ) T)
    (a : X → Z) (ha : Measurable a)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))

omit [MeasurableSpace W] in
/-- Every literal retained old-type share is carried by the prescribed cell union;
this is discharged by the actual original RN restriction identity. -/
theorem rn_truncated_retained_cell_cover (t : T) :
    ∀ᵐ p ∂(D.rnSubplanTypes (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c))
      (restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell))).component
        (false, t), a p.1 ∈ ⋃ c, cell c := by
  rw [original_retained_type_label_restriction χ ξ D a ha (MeasurableSet.iUnion hcell) t]
  exact ae_restrict_mem ((ha.comp measurable_fst) (MeasurableSet.iUnion hcell))

/-- The fixed compact good and bad pieces reconstruct the actual truncated RN
retained component, without an additional retained support or split hypothesis. -/
theorem rn_truncated_compact_split
    (coord : T → X × X → W) (hcoord : ∀ t, Measurable (coord t))
    (hdisj : Pairwise (Disjoint on cell)) (K : T → C → Set W)
    (hK : ∀ t c, MeasurableSet (K t c)) :
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c)
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha (MeasurableSet.iUnion hcell)
    ∀ t,
      D.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K t +
        ∑ c, D.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K c t =
          (D.rnSubplanTypes η hη).component (false, t) := by
  dsimp only
  exact D.rnCellCompact_split _ _ _ coord cell K (ha.comp measurable_fst) hcoord
    hcell hdisj (D.rn_truncated_retained_cell_cover χ ξ a ha cell hcell) hK

end OTSelector.Reconstruction.PopulationSubcouplingTypes
