import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedCellTrace
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCompactRefinedPopulation

/-! Deterministic traces preserve the entire original fine marked population. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace PopulationSubcouplingTypes
/-- Equal original component measures give the same finite RN marked family, including
its unmarked remainder. This is equality of the construction, before sampling. -/
theorem eq_of_components {X Y T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [Fintype T] {π : Measure (X × Y)}
    (D E : PopulationSubcouplingTypes π T) (h : ∀ t, D.component t = E.component t) : D = E := by
  cases D with | mk Dc Dh =>
    cases E with | mk Ec Eh =>
      have hcomp : Dc = Ec := funext h
      subst Ec
      rfl
end PopulationSubcouplingTypes

/-- Fixed macrocell compact colors and their deterministic traces define literally
the same original fine marked population. The index type and every old type remain fixed. -/
theorem original_cell_trace_fine_types_eq
    {X Z W C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace W]
    [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (D : PopulationSubcouplingTypes (χ + ξ) T) (a : X → Z) (ha : Measurable a)
    (cell : C → Set Z) {G : Set Z} (hG : MeasurableSet G)
    (hcover : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c)
    (coord : T → X × X → W) (K : T → C → Set W)
    (hsplit : let η := restrictOriginalRetainedResidual χ ξ a G
      let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
      ∀ t, D.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K t +
        ∑ c, D.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K c t =
          (D.rnSubplanTypes η hη).component (false, t))
    (htrace : MeasurableSet (⋃ c, cell c ∩ G))
    (hsplitTrace : let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G)
      let hη := restrictOriginalRetainedResidual_le χ ξ a ha htrace
      ∀ t, D.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord
        (fun c ↦ cell c ∩ G) K t +
        ∑ c, D.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord
          (fun c ↦ cell c ∩ G) K c t =
            (D.rnSubplanTypes η hη).component (false, t)) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let ηTrace := restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G)
    let hηTrace := restrictOriginalRetainedResidual_le χ ξ a ha htrace
    D.rnCellRefinedTypes ηTrace hηTrace
      (D.rnCellCompactGoodComponent ηTrace hηTrace (fun p ↦ a p.1) coord
        (fun c ↦ cell c ∩ G) K)
      (D.rnCellCompactBadComponent ηTrace hηTrace (fun p ↦ a p.1) coord
        (fun c ↦ cell c ∩ G) K) hsplitTrace =
    D.rnCellRefinedTypes η hη
      (D.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K)
      (D.rnCellCompactBadComponent η hη (fun p ↦ a p.1) coord cell K) hsplit := by
  dsimp only
  apply PopulationSubcouplingTypes.eq_of_components
  intro tag
  have hηeq := original_cell_trace_residual_eq χ ξ a cell G hcover
  rcases tag with ⟨b, t⟩ | ⟨c, t⟩
  · cases b
    · change D.rnSubplanComponent (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G)) t =
        D.rnSubplanComponent (restrictOriginalRetainedResidual χ ξ a G) t
      exact congrArg (fun η ↦ D.rnSubplanComponent η t) hηeq
    · change compactColorGoodComponent
        (D.component t - D.rnSubplanComponent
          (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G)) t)
        (fun p ↦ a p.1) (coord t) (fun c ↦ cell c ∩ G) (K t) =
        compactColorGoodComponent
          (D.component t - D.rnSubplanComponent (restrictOriginalRetainedResidual χ ξ a G) t)
          (fun p ↦ a p.1) (coord t) cell (K t)
      rw [hηeq]
      exact original_retained_compact_good_cell_trace χ ξ D a ha hG coord cell K t
  · change compactColorBadComponent
      (D.component t - D.rnSubplanComponent
        (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G)) t)
      (fun p ↦ a p.1) (coord t) (fun c ↦ cell c ∩ G) (K t) c =
      compactColorBadComponent
        (D.component t - D.rnSubplanComponent (restrictOriginalRetainedResidual χ ξ a G) t)
        (fun p ↦ a p.1) (coord t) cell (K t) c
    rw [hηeq]
    exact original_retained_compact_bad_cell_trace χ ξ D a ha hG coord cell K c t

end OTSelector.Reconstruction
