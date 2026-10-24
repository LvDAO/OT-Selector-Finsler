import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedCellTrace
import OTSelector.Reconstruction.FinslerRelativeLawOriginalCompactRefinedPopulation

/-! Fixed compact carriers pass to every deterministic trace of the original macrocells. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The original common label and exact RN restriction give both traced-cell
memberships for every compact good pairing. No new compact selection or
separation depth is introduced after the deterministic truncation. -/
theorem PopulationTypedCostData.original_compact_good_trace_carriers
    {X Z C T : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {q : ℕ} {cost : X → X → ℝ} (D : PopulationTypedCostData (χ + ξ) μ ν T q cost)
    (a : X → Z) (ha : Measurable a) {G : Set Z} (hG : MeasurableSet G)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hcover : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c)
    (hlabel : ∀ᵐ p ∂χ + ξ, a p.1 = a p.2)
    (K : T → C → Set (DyadicUnitCube q))
    (hcarriers : let η := restrictOriginalRetainedResidual χ ξ a G
      let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
      ∀ t, ∀ᵐ p ∂D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1)
        (fun t p ↦ D.sourceCoordinate t p.1) cell K t,
        ∃ c, a p.1 ∈ cell c ∧ a p.2 ∈ cell c ∧
          D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c) :
    let trace := fun c ↦ cell c ∩ G
    let htrace := MeasurableSet.iUnion (fun c ↦ (hcell c).inter hG)
    let η := restrictOriginalRetainedResidual χ ξ a (⋃ c, trace c)
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha htrace
    ∀ t, ∀ᵐ p ∂D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1)
      (fun t p ↦ D.sourceCoordinate t p.1) trace K t,
      ∃ c, a p.1 ∈ trace c ∧ a p.2 ∈ trace c ∧
        D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c := by
  dsimp only
  intro t
  let η := restrictOriginalRetainedResidual χ ξ a G
  let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
  let coord := fun t (p : X × X) ↦ D.sourceCoordinate t p.1
  let good := D.types.rnCellCompactGoodComponent η hη (fun p ↦ a p.1) coord cell K t
  have hgoodEq : D.types.rnCellCompactGoodComponent
      (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G))
      (restrictOriginalRetainedResidual_le χ ξ a ha
        (MeasurableSet.iUnion fun c ↦ (hcell c).inter hG))
      (fun p ↦ a p.1) coord (fun c ↦ cell c ∩ G) K t = good := by
    change compactColorGoodComponent
      (D.types.component t - D.types.rnSubplanComponent
        (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G)) t)
      (fun p ↦ a p.1) (coord t) (fun c ↦ cell c ∩ G) (K t) = _
    rw [original_cell_trace_residual_eq χ ξ a cell G hcover]
    exact original_retained_compact_good_cell_trace χ ξ D.types a ha hG coord cell K t
  rw [hgoodEq]
  have hGgood : ∀ᵐ p ∂good, a p.1 ∈ G := by
    change ∀ᵐ p ∂compactColorGoodComponent
      ((D.types.rnSubplanTypes η hη).component (false, t))
      (fun p ↦ a p.1) (coord t) cell (K t), a p.1 ∈ G
    rw [original_retained_compact_good_label_restriction χ ξ D.types rfl a ha hG
      (fun p ↦ a p.1) coord cell K t]
    exact ae_restrict_mem ((ha.comp measurable_fst) hG)
  have hlabelGood : ∀ᵐ p ∂good, a p.1 = a p.2 := by
    unfold good PopulationSubcouplingTypes.rnCellCompactGoodComponent compactColorGoodComponent
    apply ae_finsetSum_measure_iff.mpr
    intro c _
    apply ae_restrict_of_ae
    exact ae_mono ((D.types.rnSubplanTypes_component_le η hη (false,t)).trans
      (D.types.component_le t)) hlabel
  filter_upwards [hcarriers t, hGgood, hlabelGood] with p hp hg hl
  obtain ⟨c, hcs, hct, hks, hkt⟩ := hp
  exact ⟨c, ⟨hcs, hg⟩, ⟨hct, hl ▸ hg⟩, hks, hkt⟩

end OTSelector.Reconstruction
