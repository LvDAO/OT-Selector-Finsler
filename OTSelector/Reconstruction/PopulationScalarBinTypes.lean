import OTSelector.Reconstruction.FiniteScalarBins
import OTSelector.Probability.SubcouplingTypeMarking

/-!
# Original chart and scalar-bin population types

The unchanged population coupling splits by its assigned chart and its actual
source and target scalar bins. Positive types retain the original support gap,
and their label marginals agree whenever the original pairing preserves labels.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

variable {X Y J : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace J] [MeasurableSingletonClass J] [Fintype J]
  {I : Set ℝ} {δ : ℝ} (D : FiniteScalarBins I δ)
  (chart : X × Y → J) (source : X → ℝ) (target : Y → ℝ)

/-- A type records the original assigned chart and both original scalar bins. -/
def scalarBinTypeSet (t : J × Fin D.count × Fin D.count) : Set (X × Y) :=
  chart ⁻¹' {t.1} ∩ ((source ⁻¹' D.cell t.2.1) ×ˢ (target ⁻¹' D.cell t.2.2))

omit [Fintype J] in
/-- Every actual chart-bin type is measurable. -/
theorem measurableSet_scalarBinTypeSet (hchart : Measurable chart)
    (hs : Measurable source) (ht : Measurable target) (t : J × Fin D.count × Fin D.count) :
    MeasurableSet (scalarBinTypeSet D chart source target t) :=
  (hchart (measurableSet_singleton _)).inter
    ((hs (D.measurable_cell _)).prod (ht (D.measurable_cell _)))

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace J]
    [MeasurableSingletonClass J] [Fintype J] in
/-- Distinct chart-bin types are disjoint as actual endpoint sets. -/
theorem pairwiseDisjoint_scalarBinTypeSet :
    Pairwise (fun t t' ↦ Disjoint (scalarBinTypeSet D chart source target t)
      (scalarBinTypeSet D chart source target t')) := by
  intro t t' htt'
  apply disjoint_left.mpr
  intro p hp hp'
  apply htt'
  have hj : t.1 = t'.1 := hp.1.symm.trans hp'.1
  have hs : t.2.1 = t'.2.1 := by
    by_contra h
    exact disjoint_left.mp (D.disjoint h) hp.2.1 hp'.2.1
  have ht : t.2.2 = t'.2.2 := by
    by_contra h
    exact disjoint_left.mp (D.disjoint h) hp.2.2 hp'.2.2
  exact Prod.ext hj (Prod.ext hs ht)

omit [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace J]
    [MeasurableSingletonClass J] [Fintype J] in
/-- The types cover exactly the original endpoint pairs whose two scalars lie
in the retained range; they take no closure of an assigned chart. -/
theorem iUnion_scalarBinTypeSet :
    (⋃ t, scalarBinTypeSet D chart source target t) =
      ((source ⁻¹' I) ×ˢ (target ⁻¹' I)) := by
  ext p
  constructor
  · intro hp
    obtain ⟨t, ht⟩ := mem_iUnion.mp hp
    exact ⟨D.subset _ ht.2.1, D.subset _ ht.2.2⟩
  · intro hp
    obtain ⟨i, hi⟩ := mem_iUnion.mp (D.union_eq.symm ▸ hp.1)
    obtain ⟨j, hj⟩ := mem_iUnion.mp (D.union_eq.symm ▸ hp.2)
    exact mem_iUnion.mpr ⟨(chart p, i, j), rfl, hi, hj⟩

/-- The exact restriction sum keeps the full original coupling on its scalar range. -/
theorem sum_restrict_scalarBinTypeSet (π : Measure (X × Y))
    (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target) :
    (∑ t, π.restrict (scalarBinTypeSet D chart source target t)) =
      π.restrict ((source ⁻¹' I) ×ˢ (target ⁻¹' I)) := by
  rw [← Measure.sum_fintype, ← Measure.restrict_iUnion
    (pairwiseDisjoint_scalarBinTypeSet D chart source target)
    (measurableSet_scalarBinTypeSet D chart source target hchart hs ht),
    iUnion_scalarBinTypeSet]

/-- The concrete chart-bin restrictions are valid original subcoupling types. -/
def scalarBinPopulationTypes (π : Measure (X × Y))
    (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target) :
    PopulationSubcouplingTypes π (J × Fin D.count × Fin D.count) where
  component t := π.restrict (scalarBinTypeSet D chart source target t)
  dominated := by
    rw [sum_restrict_scalarBinTypeSet D chart source target π hchart hs ht]
    exact Measure.restrict_le_self

/-- If the original scalar range carries the original populations, every bit of
original pairing mass is recovered by these finite types. -/
theorem scalarBinPopulationTypes_sum_eq (π : Measure (X × Y))
    (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target)
    (hI : ∀ᵐ p ∂π, source p.1 ∈ I ∧ target p.2 ∈ I) :
    (∑ t, (scalarBinPopulationTypes D chart source target π hchart hs ht).component t) = π := by
  exact (sum_restrict_scalarBinTypeSet D chart source target π hchart hs ht).trans
    (Measure.restrict_eq_self_of_ae_mem hI)

/-- A positive actual chart-bin type has the half-gap estimate for all endpoint
scalars in its two bins, including independently sampled type endpoints. -/
theorem scalarBinPopulationTypes_gap (π : Measure (X × Y))
    (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (t : J × Fin D.count × Fin D.count)
    (hmass : (scalarBinPopulationTypes D chart source target π hchart hs ht).component t univ ≠ 0) :
    ∀ x ∈ D.cell t.2.1, ∀ y ∈ D.cell t.2.2, δ / 2 ≤ y - x := by
  apply D.gap_of_type_mass_ne_zero π
    (A := scalarBinTypeSet D chart source target t) (fun p hp ↦ hp.2)
  · simpa only [scalarBinPopulationTypes, Measure.restrict_apply_univ] using hmass
  · exact hgap

/-- Label preservation of the original coupling passes to every chart-bin type,
so the actual two label submarginals agree without imposing a balance condition. -/
theorem scalarBinPopulationTypes_common_label
    {Z : Type*} [MeasurableSpace Z] (π : Measure (X × Y))
    (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target)
    (left : J → X → Z) (right : J → Y → Z)
    (hleft : ∀ j, Measurable (left j)) (hright : ∀ j, Measurable (right j))
    (hlabel : ∀ᵐ p ∂π, left (chart p) p.1 = right (chart p) p.2)
    (t : J × Fin D.count × Fin D.count) :
    ((scalarBinPopulationTypes D chart source target π hchart hs ht).source t).map (left t.1) =
      ((scalarBinPopulationTypes D chart source target π hchart hs ht).target t).map
        (right t.1) := by
  rw [PopulationSubcouplingTypes.source, PopulationSubcouplingTypes.target,
    Measure.map_map (hleft _) measurable_fst, Measure.map_map (hright _) measurable_snd]
  apply Measure.map_congr
  filter_upwards [ae_restrict_of_ae hlabel,
    ae_restrict_mem (measurableSet_scalarBinTypeSet D chart source target hchart hs ht t)]
    with p hp hpt
  simpa only [Function.comp_apply, show chart p = t.1 from hpt.1] using hp

/-- The original marginal of every type is carried by its assigned actual bin. -/
theorem scalarBinPopulationTypes_marginal_bins (π : Measure (X × Y))
    (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target)
    (t : J × Fin D.count × Fin D.count) :
    (∀ᵐ x ∂(scalarBinPopulationTypes D chart source target π hchart hs ht).source t,
      source x ∈ D.cell t.2.1) ∧
    (∀ᵐ y ∂(scalarBinPopulationTypes D chart source target π hchart hs ht).target t,
      target y ∈ D.cell t.2.2) := by
  have hmem := ae_restrict_mem
    (μ := π) (measurableSet_scalarBinTypeSet D chart source target hchart hs ht t)
  constructor
  · apply (ae_map_iff measurable_fst.aemeasurable (hs (D.measurable_cell t.2.1))).mpr
    filter_upwards [hmem] with p hp using hp.2.1
  · apply (ae_map_iff measurable_snd.aemeasurable (ht (D.measurable_cell t.2.2))).mpr
    filter_upwards [hmem] with p hp using hp.2.2

/-- Independently sampled endpoints of every original type inherit the half-gap.
Zero-mass types satisfy the same statement without any separate conditioning. -/
theorem scalarBinPopulationTypes_independent_gap (π : Measure (X × Y))
    (hchart : Measurable chart) (hs : Measurable source) (ht : Measurable target)
    (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1)
    (t : J × Fin D.count × Fin D.count) :
    let T := scalarBinPopulationTypes D chart source target π hchart hs ht
    ∀ᵐ p ∂(T.source t).prod (T.target t), δ / 2 ≤ target p.2 - source p.1 := by
  let T := scalarBinPopulationTypes D chart source target π hchart hs ht
  change ∀ᵐ p ∂(T.source t).prod (T.target t), δ / 2 ≤ target p.2 - source p.1
  by_cases hm : T.component t univ = 0
  · have he : T.component t = 0 := Measure.measure_univ_eq_zero.mp hm
    simp only [PopulationSubcouplingTypes.source, PopulationSubcouplingTypes.target,
      he, Measure.map_zero, Measure.zero_prod, ae_zero, Filter.eventually_bot]
  · have hg := scalarBinPopulationTypes_gap D chart source target π hchart hs ht hgap t hm
    obtain ⟨hsource, htarget⟩ :=
      scalarBinPopulationTypes_marginal_bins D chart source target π hchart hs ht t
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hsource,
      Measure.quasiMeasurePreserving_snd.ae htarget] with p hp hq
    exact hg (source p.1) hp (target p.2) hq

omit D in
/-- Compact original physical supports and their actual scalar maps produce a
finite full-mass type decomposition with uniformly separated positive types. -/
theorem exists_scalarBinPopulationTypes_of_compact_support
    [TopologicalSpace X] [BorelSpace X] [TopologicalSpace Y] [BorelSpace Y]
    {A : Set X} {B : Set Y} (hA : IsCompact A) (hB : IsCompact B)
    {μ : Measure X} {ν : Measure Y} (π : Measure (X × Y))
    (hπ : Vlasov.IsCoupling π μ ν)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hchart : Measurable chart) (hs : Continuous source) (ht : Continuous target)
    (hδ : 0 < δ) (hgap : ∀ᵐ p ∂π, δ ≤ target p.2 - source p.1) :
    ∃ D : FiniteScalarBins (source '' A ∪ target '' B) δ,
      (∑ t, (scalarBinPopulationTypes D chart source target π hchart
        hs.measurable ht.measurable).component t) = π ∧
      ∀ t : J × Fin D.count × Fin D.count,
        (scalarBinPopulationTypes D chart source target π hchart
          hs.measurable ht.measurable).component t univ ≠ 0 →
        ∀ x ∈ D.cell t.2.1, ∀ y ∈ D.cell t.2.2, δ / 2 ≤ y - x := by
  obtain ⟨D⟩ := exists_finiteScalarBins ((hA.image hs).union (hB.image ht)) hδ
  have hpA : ∀ᵐ p ∂π, p.1 ∈ A := by
    have he : ∀ᵐ x ∂π.map Prod.fst, x ∈ A := hπ.1.symm ▸ hμ
    exact ae_of_ae_map measurable_fst.aemeasurable he
  have hpB : ∀ᵐ p ∂π, p.2 ∈ B := by
    have he : ∀ᵐ y ∂π.map Prod.snd, y ∈ B := hπ.2.symm ▸ hν
    exact ae_of_ae_map measurable_snd.aemeasurable he
  refine ⟨D, scalarBinPopulationTypes_sum_eq D chart source target π hchart
    hs.measurable ht.measurable ?_, ?_⟩
  · filter_upwards [hpA, hpB] with p hpA hpB
    exact ⟨Or.inl (mem_image_of_mem source hpA), Or.inr (mem_image_of_mem target hpB)⟩
  · intro t hm
    exact scalarBinPopulationTypes_gap D chart source target π hchart
      hs.measurable ht.measurable hgap t hm

end OTSelector.Reconstruction
