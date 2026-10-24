import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedCompactRestriction

/-! Fixed reference cells intersect deterministic labels without changing the original fine split. -/
open Set Function MeasureTheory
open scoped BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Intersecting fixed reference cells with deterministic labels keeps the same finite index type. -/
theorem iUnion_original_cell_trace {C Z : Type*} (cell : C → Set Z) (G : Set Z) :
    (⋃ c, cell c ∩ G) = (⋃ c, cell c) ∩ G := by
  ext z
  simp only [mem_iUnion, mem_inter_iff]
  exact ⟨fun ⟨c, hc, hG⟩ ↦ ⟨⟨c, hc⟩, hG⟩,
    fun ⟨⟨c, hc⟩, hG⟩ ↦ ⟨c, hc, hG⟩⟩

/-- The actual original retained support makes the traced-cell residual exactly
the original prescribed-label residual, before drawing or refining any sample. -/
theorem original_cell_trace_residual_eq
    {X Z C : Type*} [MeasurableSpace X]
    (χ ξ : Measure (X × X)) (a : X → Z) (cell : C → Set Z) (G : Set Z)
    (hsupport : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c) :
    restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ G) =
      restrictOriginalRetainedResidual χ ξ a G := by
  rw [iUnion_original_cell_trace]
  unfold restrictOriginalRetainedResidual
  congr 1
  apply Measure.restrict_congr_set
  filter_upwards [hsupport] with p hp
  change (¬(a p.1 ∈ ⋃ c, cell c ∧ a p.1 ∈ G)) = (a p.1 ∉ G)
  simp only [hp, true_and]

section CompactTrace
variable {X Z W C : Type*} [MeasurableSpace X] [Fintype C]
    (τ : Measure X) (label : X → Z)
    (coord : X → W) (cell : C → Set Z) (K : C → Set W)
    {G : Set Z} (hG : MeasurableSet (label ⁻¹' G))

include hG

/-- The exact truncated good component uses the same fixed compact colors whether
one records the original cells or their deterministic traces. -/
theorem compactColorGoodComponent_cell_trace :
    compactColorGoodComponent (τ.restrict (label ⁻¹' G)) label coord
      (fun c ↦ cell c ∩ G) K =
      compactColorGoodComponent (τ.restrict (label ⁻¹' G)) label coord cell K := by
  unfold compactColorGoodComponent
  apply Finset.sum_congr rfl
  intro c _
  apply Measure.restrict_congr_set
  filter_upwards [ae_restrict_mem hG] with x hx
  change label x ∈ G at hx
  change (label x ∈ cell c ∩ G ∧ coord x ∈ K c) = (label x ∈ cell c ∧ coord x ∈ K c)
  simp only [mem_inter_iff, hx, and_true]

omit [Fintype C] in
/-- Bad(cell,type) is literally unchanged by tracing the deterministic labels;
the same old type and fixed compact color are retained. -/
theorem compactColorBadComponent_cell_trace (c : C) :
    compactColorBadComponent (τ.restrict (label ⁻¹' G)) label coord
      (fun c ↦ cell c ∩ G) K c =
      compactColorBadComponent (τ.restrict (label ⁻¹' G)) label coord cell K c := by
  apply Measure.restrict_congr_set
  filter_upwards [ae_restrict_mem hG] with x hx
  change label x ∈ G at hx
  change (label x ∈ cell c ∩ G ∧ coord x ∉ K c) = (label x ∈ cell c ∧ coord x ∉ K c)
  simp only [mem_inter_iff, hx, and_true]

end CompactTrace

/-- Every retained original type uses the SAME compact good share after replacing
fixed reference cells by their deterministic traces. No new type marking is allocated. -/
theorem original_retained_compact_good_cell_trace
    {X Z W C T : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype C] [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (D : PopulationSubcouplingTypes (χ + ξ) T) (a : X → Z) (ha : Measurable a)
    {G : Set Z} (hG : MeasurableSet G) (coord : T → X × X → W)
    (cell : C → Set Z) (K : T → C → Set W) (t : T) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let τ := (D.rnSubplanTypes η hη).component (false, t)
    compactColorGoodComponent τ (fun p ↦ a p.1) (coord t) (fun c ↦ cell c ∩ G) (K t) =
      compactColorGoodComponent τ (fun p ↦ a p.1) (coord t) cell (K t) := by
  dsimp only
  rw [original_retained_type_label_restriction χ ξ D a ha hG t]
  exact compactColorGoodComponent_cell_trace _ (fun p : X × X ↦ a p.1)
    (coord t) cell (K t) ((ha.comp measurable_fst) hG)

/-- Each actual bad(cell,type) share has the same traced-cell identity. -/
theorem original_retained_compact_bad_cell_trace
    {X Z W C T : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [Fintype T]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (D : PopulationSubcouplingTypes (χ + ξ) T) (a : X → Z) (ha : Measurable a)
    {G : Set Z} (hG : MeasurableSet G) (coord : T → X × X → W)
    (cell : C → Set Z) (K : T → C → Set W) (c : C) (t : T) :
    let η := restrictOriginalRetainedResidual χ ξ a G
    let hη := restrictOriginalRetainedResidual_le χ ξ a ha hG
    let τ := (D.rnSubplanTypes η hη).component (false, t)
    compactColorBadComponent τ (fun p ↦ a p.1) (coord t) (fun c ↦ cell c ∩ G) (K t) c =
      compactColorBadComponent τ (fun p ↦ a p.1) (coord t) cell (K t) c := by
  dsimp only
  rw [original_retained_type_label_restriction χ ξ D a ha hG t]
  exact compactColorBadComponent_cell_trace _ (fun p : X × X ↦ a p.1)
    (coord t) cell (K t) ((ha.comp measurable_fst) hG) c

end OTSelector.Reconstruction
