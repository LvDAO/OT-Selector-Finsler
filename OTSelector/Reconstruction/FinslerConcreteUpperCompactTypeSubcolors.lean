import OTSelector.Reconstruction.FinslerConcreteUpperCompactTypeColors

/-! Original calibrated geometry separates compact coordinate cores of different
retained label cells within every fixed original population type. No continuity
or Lipschitz property is imposed on the original label inverse. -/
open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M Z T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [Fintype T]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {a : M → Z}
  {π : Measure (M × M)} [IsFiniteMeasure π]
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {q : ℕ}

/-- Every finite original label partition has almost-full compact coordinate
cores for each fixed original type. Their color images are disjoint, and every
original good endpoint in a selected coordinate core has that literal label
color. The discarded mass is measured in the unchanged original component. -/
theorem PopulationTypedCostData.exists_original_compact_subtype_colors
    (D : PopulationTypedCostData π μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (τ : T → Measure (M × M)) (hτ : ∀ t, τ t ≤ D.types.component t)
    (_hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hreg : ∀ᵐ p ∂π, p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u)
    (hcal : let _inst : MetricSpace M := F.metricSpace
      ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {C : Type*} [Fintype C] (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisjoint : Pairwise (Disjoint on cell)) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : T → C → Set (DyadicUnitCube q),
      (∀ t c, IsCompact (K t c)) ∧
      (∀ t, Pairwise (Disjoint on K t)) ∧
      (∀ t c, (τ t)
        ({p | a p.1 ∈ cell c} \ {p | D.sourceCoordinate t p.1 ∈ K t c}) < ε) ∧
      (∀ t c x, D.sourceGood t x → x ∈ F.potentialRegularDomain u →
        D.sourceCoordinate t x ∈ K t c → a x ∈ cell c) ∧
      (∀ t c y, D.targetGood t y → y ∈ F.potentialRegularDomain u →
        D.targetCoordinate t y ∈ K t c → a y ∈ cell c) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI (t : T) : IsFiniteMeasure (τ t) := isFiniteMeasure_of_le (D.types.component t) (hτ t)
  have hpairGood (t : T) : ∀ᵐ p ∂τ t,
      D.sourceGood t p.1 ∧ D.targetGood t p.2 := by
    have hs := ae_of_ae_map measurable_fst.aemeasurable (D.source_good t)
    have ht := ae_of_ae_map measurable_snd.aemeasurable (D.target_good t)
    filter_upwards [ae_mono (hτ t) hs, ae_mono (hτ t) ht] with p hs ht
    exact ⟨hs, ht⟩
  have hprop (t : T) (c : C) :
      ∀ᵐ p ∂(τ t).restrict {p | a p.1 ∈ cell c},
        D.sourceGood t p.1 ∧ D.targetGood t p.2 ∧
        D.sourceCoordinate t p.1 = D.targetCoordinate t p.2 ∧
        p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u ∧
        a p.1 = a p.2 ∧ a p.1 ∈ cell c := by
    filter_upwards [ae_restrict_of_ae (hpairGood t),
      ae_restrict_of_ae (ae_mono (hτ t) (D.paired_coordinate t)),
      ae_restrict_of_ae (ae_mono ((hτ t).trans (D.types.component_le t)) hreg),
      ae_restrict_of_ae (ae_mono ((hτ t).trans (D.types.component_le t)) hcal),
      ae_restrict_mem ((ha.comp measurable_fst) (hcell c))] with p hg hp hr hc hm
    exact ⟨hg.1, hg.2, hp, hr.1, hr.2, ((horder _ hr.1 _ hr.2).mpr hc).1, hm⟩
  have hcore (t : T) (c : C) := exists_lusin_compact_core_with_ae_property
    (ν := τ t) ((ha.comp measurable_fst) (hcell c))
    (measure_ne_top _ _) ((D.measurable_sourceCoordinate t).comp measurable_fst)
    (hprop t c) hε
  choose A hAsub hA hmass hcont hAgood using hcore
  let K (t : T) (c : C) := (fun p : M × M ↦ D.sourceCoordinate t p.1) '' A t c
  have hKcompact (t c) : IsCompact (K t c) := (hA t c).image_of_continuousOn (hcont t c)
  have hsource (t c x) (hx : D.sourceGood t x) (hxreg : x ∈ F.potentialRegularDomain u)
      (hxK : D.sourceCoordinate t x ∈ K t c) : a x ∈ cell c := by
    obtain ⟨p, hp, heq⟩ := hxK
    have hg := hAgood t c p hp
    have hlabel := D.same_coordinate_original_label hu horder hx hg.2.1 hxreg hg.2.2.2.2.1
      (heq.symm.trans hg.2.2.1)
    rw [hlabel, ← hg.2.2.2.2.2.1]
    exact hg.2.2.2.2.2.2
  have htarget (t c y) (hy : D.targetGood t y) (hyreg : y ∈ F.potentialRegularDomain u)
      (hyK : D.targetCoordinate t y ∈ K t c) : a y ∈ cell c := by
    obtain ⟨p, hp, heq⟩ := hyK
    have hg := hAgood t c p hp
    have hlabel := D.same_coordinate_original_label hu horder hg.1 hy hg.2.2.2.1 hyreg heq
    rw [← hlabel]
    exact hg.2.2.2.2.2.2
  refine ⟨K, hKcompact, ?_, ?_, hsource, htarget⟩
  · intro t c c' hcc'
    apply disjoint_left.mpr
    intro v hvc hvc'
    obtain ⟨p, hp, hpeq⟩ := hvc
    have hg := hAgood t c p hp
    have hpK : D.sourceCoordinate t p.1 ∈ K t c' := by
      rw [show D.sourceCoordinate t p.1 = v from hpeq]
      exact hvc'
    have hc' := hsource t c' p.1 hg.1 hg.2.2.2.1 hpK
    exact (Set.disjoint_left.mp (hdisjoint hcc')) hg.2.2.2.2.2.2 hc'
  · intro t c
    exact (measure_mono (show {p | a p.1 ∈ cell c} \ {p | D.sourceCoordinate t p.1 ∈ K t c} ⊆
      {p | a p.1 ∈ cell c} \ A t c from by
        intro p hp
        exact ⟨hp.1, fun hpA ↦ hp.2 ⟨p, hpA, rfl⟩⟩)).trans_lt (hmass t c)

end OTSelector.Reconstruction
