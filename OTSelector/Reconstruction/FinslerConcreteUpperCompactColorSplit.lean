import OTSelector.Reconstruction.FinslerConcreteUpperCompactTypeColors

/-! Compact good type shares and literal bad color shares partition each
original retained component. The good share keeps no color in its type index;
this preserves the original type count in its leading hierarchy energy. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {X Z W C : Type*} [MeasurableSpace X] [MeasurableSpace Z]
  [MeasurableSpace W] [Fintype C]

/-- The original component share whose actual coordinate lies in the compact
core of its own literal original color. -/
def compactColorGoodComponent (τ : Measure X) (label : X → Z) (coord : X → W)
    (cell : C → Set Z) (K : C → Set W) : Measure X :=
  ∑ c, τ.restrict ((label ⁻¹' cell c) ∩ (coord ⁻¹' K c))

/-- The exact discarded original component in one fixed literal color. -/
def compactColorBadComponent (τ : Measure X) (label : X → Z) (coord : X → W)
    (cell : C → Set Z) (K : C → Set W) (c : C) : Measure X :=
  τ.restrict ((label ⁻¹' cell c) \ (coord ⁻¹' K c))

/-- Good(type) and bad(color,type) recover each old component exactly. This is
an equality of unchanged original measures before any empirical marking. -/
theorem compactColorGood_add_sum_bad_eq
    (τ : Measure X) (label : X → Z) (coord : X → W)
    (hlabel : Measurable label) (hcoord : Measurable coord)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisjoint : Pairwise (Disjoint on cell))
    (hcover : ∀ᵐ x ∂τ, label x ∈ ⋃ c, cell c)
    (K : C → Set W) (hK : ∀ c, MeasurableSet (K c)) :
    compactColorGoodComponent τ label coord cell K +
      ∑ c, compactColorBadComponent τ label coord cell K c = τ := by
  classical
  have hpre : Pairwise (Disjoint on fun c ↦ label ⁻¹' cell c) :=
    fun c c' hcc' ↦ (hdisjoint hcc').preimage label
  unfold compactColorGoodComponent compactColorBadComponent
  rw [← Finset.sum_add_distrib]
  simp_rw [Measure.restrict_inter_add_sdiff _ (hcoord (hK _))]
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion hpre (fun c ↦ hlabel (hcell c))]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [hcover] with x hx
  obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨c, hc⟩

/-- Each bad share has exactly its literal original missing-core mass. -/
theorem compactColorBadComponent_univ
    (τ : Measure X) (label : X → Z) (coord : X → W)
    (cell : C → Set Z) (K : C → Set W) (c : C) :
    compactColorBadComponent τ label coord cell K c Set.univ =
      τ ((label ⁻¹' cell c) \ (coord ⁻¹' K c)) := by
  simp only [compactColorBadComponent, Measure.restrict_apply_univ]

/-- Every exact component reconstruction gives domination without assuming any
mutual singularity of the original type components. -/
theorem compactColorGoodComponent_le
    (τ : Measure X) (label : X → Z) (coord : X → W)
    (hlabel : Measurable label) (hcoord : Measurable coord)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisjoint : Pairwise (Disjoint on cell))
    (hcover : ∀ᵐ x ∂τ, label x ∈ ⋃ c, cell c)
    (K : C → Set W) (hK : ∀ c, MeasurableSet (K c)) :
    compactColorGoodComponent τ label coord cell K ≤ τ := by
  exact (Measure.le_add_right (ν' := ∑ c, compactColorBadComponent τ label coord cell K c)
    (le_refl (compactColorGoodComponent τ label coord cell K))).trans_eq
      (compactColorGood_add_sum_bad_eq τ label coord hlabel hcoord cell hcell hdisjoint hcover K hK)

/-- The good component retains a literal original color and its matching
compact coordinate carrier almost everywhere. -/
theorem compactColorGoodComponent_ae_mem
    (τ : Measure X) (label : X → Z) (coord : X → W)
    (hlabel : Measurable label) (hcoord : Measurable coord)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Set W) (hK : ∀ c, MeasurableSet (K c)) :
    ∀ᵐ x ∂compactColorGoodComponent τ label coord cell K,
      ∃ c, label x ∈ cell c ∧ coord x ∈ K c := by
  classical
  unfold compactColorGoodComponent
  apply ae_finsetSum_measure_iff.mpr
  intro c _
  filter_upwards [ae_restrict_mem ((hlabel (hcell c)).inter (hcoord (hK c)))] with x hx
  exact ⟨c, hx⟩

/-- The bad component remains inside its own original cell. -/
theorem compactColorBadComponent_ae_mem
    (τ : Measure X) (label : X → Z) (coord : X → W)
    (hlabel : Measurable label) (hcoord : Measurable coord)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Set W) (hK : ∀ c, MeasurableSet (K c)) (c : C) :
    ∀ᵐ x ∂compactColorBadComponent τ label coord cell K c,
      label x ∈ cell c ∧ coord x ∉ K c :=
  ae_restrict_mem ((hlabel (hcell c)).diff (hcoord (hK c)))

end OTSelector.Reconstruction
