import OTSelector.Reconstruction.FinslerConcreteUpperCompactColorSplit
import OTSelector.Reconstruction.FinslerConcreteUpperCompactTypeSubcolors
import OTSelector.Finite.CompactDyadicColors
/-! Actual original type components split into one compact good share per old
type and one small bad share per cell. A single positive dyadic depth separates
all good colors of all original types, before drawing any original sample. -/
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

/-- Original componentwise compact approximation preserves exact old type
mass and provides all good color carriers needed by one global hierarchy. -/
theorem PopulationTypedCostData.exists_original_compact_subtype_split_depth
    (D : PopulationTypedCostData π μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (τ : T → Measure (M × M)) (hτ : ∀ t, τ t ≤ D.types.component t)
    (hF : F.IsSmoothStronglyConvex)
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
    (hdisjoint : Pairwise (Disjoint on cell))
    (hcover : ∀ t, ∀ᵐ p ∂τ t, a p.1 ∈ ⋃ c, cell c) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ (K : T → C → Set (DyadicUnitCube q)) (depth : ℕ),
      0 < depth ∧ (∀ t c, IsCompact (K t c)) ∧
      (∀ t, Pairwise (Disjoint on K t)) ∧
      (∀ k ≥ depth, ∀ t c c', ∀ x ∈ K t c, ∀ y ∈ K t c',
        dyadicCubeCell k x = dyadicCubeCell k y → c = c') ∧
      (∀ t,
        compactColorGoodComponent (τ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) +
        ∑ c, compactColorBadComponent (τ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c = τ t) ∧
      (∀ t c, compactColorBadComponent (τ t) (fun p ↦ a p.1)
        (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c Set.univ < ε) ∧
      (∀ t, ∀ᵐ p ∂compactColorGoodComponent (τ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t),
        ∃ c, a p.1 ∈ cell c ∧ a p.2 ∈ cell c ∧
          D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c) := by
  classical
  letI : MetricSpace M := F.metricSpace
  obtain ⟨K, hK, hKdis, hsmall, hsource, htarget⟩ :=
    D.exists_original_compact_subtype_colors τ hτ hF hcomplete hu ha horder hreg hcal cell hcell hdisjoint hε
  obtain ⟨depth, hdepth⟩ := exists_dyadic_level_separating_typed_compact_colors q K hK hKdis
  have hKm (t c) : MeasurableSet (K t c) := (hK t c).measurableSet
  refine ⟨K, max 1 depth, by omega, hK, hKdis, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact hdepth k ((le_max_right 1 depth).trans hk)
  · intro t
    exact compactColorGood_add_sum_bad_eq (τ t) _ _ (ha.comp measurable_fst)
      ((D.measurable_sourceCoordinate t).comp measurable_fst) cell hcell hdisjoint
      (hcover t) (K t) (hKm t)
  · intro t c
    rw [compactColorBadComponent_univ]
    exact hsmall t c
  · intro t
    have hg := compactColorGoodComponent_ae_mem (τ t) _ _
      (ha.comp measurable_fst) ((D.measurable_sourceCoordinate t).comp measurable_fst)
      cell hcell (K t) (hKm t)
    have hle := compactColorGoodComponent_le (τ t) _ _ (ha.comp measurable_fst)
      ((D.measurable_sourceCoordinate t).comp measurable_fst) cell hcell hdisjoint
      (hcover t) (K t) (hKm t)
    have hr := ae_mono (hle.trans ((hτ t).trans (D.types.component_le t))) hreg
    have hc := ae_mono (hle.trans ((hτ t).trans (D.types.component_le t))) hcal
    have hp := ae_mono (hle.trans (hτ t)) (D.paired_coordinate t)
    filter_upwards [hg, hr, hc, hp] with p hg hr hc hp
    obtain ⟨c, hpc, hpK⟩ := hg
    have halabel := ((horder p.1 hr.1 p.2 hr.2).mpr hc).1
    exact ⟨c, hpc, halabel ▸ hpc, hpK, hp ▸ hpK⟩

end OTSelector.Reconstruction
