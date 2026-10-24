import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedCellTrace

/-! Dependent deterministic spatial cutoffs join one unchanged original residual. -/
open Set Function MeasureTheory
open scoped BigOperators ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Disjoint original cells recover their own prescribed cutoff from the one
global retained-label set, even when the coordinate charts depend on the cell. -/
theorem original_cellwise_cutoff_trace
    {Z C : Type*} (cell cutoff : C → Set Z) (hdisj : Pairwise (Disjoint on cell)) (c : C) :
    cell c ∩ (⋃ d, cell d ∩ cutoff d) = cell c ∩ cutoff c := by
  ext z
  constructor
  · rintro ⟨hc, hz⟩
    obtain ⟨d, hd⟩ := mem_iUnion.mp hz
    by_cases hdc : d = c
    · subst d
      exact ⟨hc, hd.2⟩
    · exact False.elim ((Set.disjoint_left.mp (hdisj hdc)) hd.1 hc)
  · rintro ⟨hc, hcut⟩
    exact ⟨hc, mem_iUnion.mpr ⟨c, hc, hcut⟩⟩

/-- The entire discarded original cell support is precisely the union of the
original losses inside each fixed cell. No empirical point is selected here. -/
theorem original_cellwise_cutoff_discard
    {Z C : Type*} (cell cutoff : C → Set Z) (hdisj : Pairwise (Disjoint on cell)) :
    (⋃ c, cell c) \ (⋃ c, cell c ∩ cutoff c) = ⋃ c, cell c \ cutoff c := by
  ext z
  constructor
  · rintro ⟨hz, hnot⟩
    obtain ⟨c,hc⟩ := mem_iUnion.mp hz
    exact mem_iUnion.mpr ⟨c, hc, fun hcut ↦ hnot (mem_iUnion.mpr ⟨c,hc,hcut⟩)⟩
  · intro hz
    obtain ⟨c,hc,hnot⟩ := mem_iUnion.mp hz
    refine ⟨mem_iUnion.mpr ⟨c,hc⟩, ?_⟩
    intro hglobal
    have htrace : z ∈ cell c ∩ (⋃ d, cell d ∩ cutoff d) := ⟨hc,hglobal⟩
    rw [original_cellwise_cutoff_trace cell cutoff hdisj c] at htrace
    exact hnot htrace.2

/-- One deterministic union of the original cell cutoffs increases the true
residual by at most the sum of the ORIGINAL removed label masses. -/
theorem original_cellwise_cutoff_residual_mass_le
    {X Z C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype C]
    (χ ξ : Measure (X × X)) (μ ν : Measure X)
    (hwhole : Vlasov.IsCoupling (χ + ξ) μ ν)
    (a : X → Z) (ha : Measurable a) (cell cutoff : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c)) (hcutoff : ∀ c, MeasurableSet (cutoff c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsupport : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c) :
    restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ cutoff c) univ ≤
      ξ univ + ∑ c, (μ.map a) (cell c \ cutoff c) := by
  have hbound := restrictOriginalRetainedResidual_mass_le χ ξ μ ν hwhole a ha
    (MeasurableSet.iUnion hcell)
    (MeasurableSet.iUnion fun c ↦ (hcell c).inter (hcutoff c)) hsupport
  rw [original_cellwise_cutoff_discard cell cutoff hdisj] at hbound
  exact hbound.trans (add_le_add (le_refl _) (measure_iUnion_fintype_le (μ.map a) _))

/-- The same once-counted residual estimate in real units is ready for the
original small-mass energy bound, before choosing empirical size. -/
theorem original_cellwise_cutoff_residual_real_mass_le
    {X Z C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [Fintype C]
    (χ ξ : Measure (X × X)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (μ ν : Measure X) [IsFiniteMeasure μ]
    (hwhole : Vlasov.IsCoupling (χ + ξ) μ ν)
    (a : X → Z) (ha : Measurable a) (cell cutoff : C → Set Z)
    (hcell : ∀ c, MeasurableSet (cell c)) (hcutoff : ∀ c, MeasurableSet (cutoff c))
    (hdisj : Pairwise (Disjoint on cell))
    (hsupport : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c) :
    (restrictOriginalRetainedResidual χ ξ a (⋃ c, cell c ∩ cutoff c) univ).toReal ≤
      (ξ univ).toReal + ∑ c, (μ.map a).real (cell c \ cutoff c) := by
  have hbound := original_cellwise_cutoff_residual_mass_le χ ξ μ ν hwhole a ha
    cell cutoff hcell hcutoff hdisj hsupport
  have hsum : (∑ c, (μ.map a) (cell c \ cutoff c)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun c _ ↦ measure_ne_top _ _
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, hsum⟩) hbound
  rw [ENNReal.toReal_add (measure_ne_top _ _) hsum,
    ENNReal.toReal_sum (fun c _ ↦ measure_ne_top _ _)] at hreal
  exact hreal

end OTSelector.Reconstruction
