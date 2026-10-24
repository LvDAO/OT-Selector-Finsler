import OTSelector.Reconstruction.FinslerConcreteUpperCompactColorSplitDepth

/-! A single compact type/color approximation works for every later dominated
original retained subpopulation. In particular deterministic microscopic
truncations keep one fixed dyadic separation depth before the empirical limit. -/
open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

/-- Discarded compact-color mass is monotone in the unchanged original measure. -/
theorem compactColorBadComponent_mono
    {X Z W C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace W]
    {τ σ : Measure X} (h : τ ≤ σ) (label : X → Z) (coord : X → W)
    (cell : C → Set Z) (K : C → Set W) (c : C) :
    compactColorBadComponent τ label coord cell K c ≤
      compactColorBadComponent σ label coord cell K c :=
  Measure.restrict_mono_measure h _

/-- The compact good share is monotone, so all original point carriers pass to
later deterministic subpopulations on the same fixed coordinate cores. -/
theorem compactColorGoodComponent_mono
    {X Z W C : Type*} [MeasurableSpace X] [MeasurableSpace Z] [MeasurableSpace W] [Fintype C]
    {τ σ : Measure X} (h : τ ≤ σ) (label : X → Z) (coord : X → W)
    (cell : C → Set Z) (K : C → Set W) :
    compactColorGoodComponent τ label coord cell K ≤
      compactColorGoodComponent σ label coord cell K :=
  Finset.sum_le_sum (fun _ _ ↦ Measure.restrict_mono_measure h _)

variable {E M Z T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [Fintype T]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {a : M → Z}
  {π : Measure (M × M)} [IsFiniteMeasure π]
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {q : ℕ}

/-- The actual compact/color approximation and its positive separation depth
are chosen once from the original retained components, before every later
original submeasure or changing microscopic grid is supplied. -/
theorem PopulationTypedCostData.exists_uniform_original_compact_subtype_splits
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
      (∀ k ≥ depth, ∀ t c c', ∀ x ∈ K t c, ∀ y ∈ K t c',
        dyadicCubeCell k x = dyadicCubeCell k y → c = c') ∧
      ∀ σ : T → Measure (M × M), (∀ t, σ t ≤ τ t) →
      (∀ t, compactColorGoodComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) +
        ∑ c, compactColorBadComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c = σ t) ∧
      (∀ t c, compactColorBadComponent (σ t) (fun p ↦ a p.1)
        (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c Set.univ < ε) ∧
      (∀ t, ∀ᵐ p ∂compactColorGoodComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t),
        ∃ c, a p.1 ∈ cell c ∧ a p.2 ∈ cell c ∧
          D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c) := by
  classical
  obtain ⟨K, depth, hd, hK, hdis, hsep, hsplit, hsmall, hgood⟩ :=
    D.exists_original_compact_subtype_split_depth τ hτ hF hcomplete hu ha horder
      hreg hcal cell hcell hdisjoint hcover hε
  refine ⟨K, depth, hd, hK, hsep, ?_⟩
  intro σ hσ
  have hKm (t c) : MeasurableSet (K t c) := (hK t c).measurableSet
  refine ⟨?_, ?_, ?_⟩
  · intro t
    exact compactColorGood_add_sum_bad_eq (σ t) _ _ (ha.comp measurable_fst)
      ((D.measurable_sourceCoordinate t).comp measurable_fst) cell hcell hdisjoint
      (ae_mono (hσ t) (hcover t)) (K t) (hKm t)
  · intro t c
    exact ((compactColorBadComponent_mono (hσ t) (fun p ↦ a p.1)
      (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c) Set.univ).trans_lt (hsmall t c)
  · intro t
    exact ae_mono (compactColorGoodComponent_mono (hσ t) (fun p ↦ a p.1)
      (fun p ↦ D.sourceCoordinate t p.1) cell (K t)) (hgood t)

end OTSelector.Reconstruction
