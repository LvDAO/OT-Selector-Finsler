import OTSelector.Reconstruction.FinslerConcreteUpperUniformSmallCompactSplits
import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedTypeRestriction
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling

/-! One actual compact color family and separation depth work for every
deterministic label restriction of the same original retained coupling. -/
open Set Function MeasureTheory ProbabilityTheory Manifold Metric OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

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
theorem PopulationTypedCostData.exists_original_retained_compact_truncation_splits
    (D : PopulationTypedCostData π μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (χ ξ : Measure (M × M)) [IsFiniteMeasure χ] [IsFiniteMeasure ξ]
    (hwhole : χ + ξ = π)
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
    (hcover : ∀ᵐ p ∂χ, a p.1 ∈ ⋃ c, cell c) {θ : ℝ} (hθ : 0 < θ) :
    ∃ (K : T → C → Set (DyadicUnitCube q)) (depth : ℕ),
      0 < depth ∧ (∀ t c, IsCompact (K t c)) ∧
      (∀ k ≥ depth, ∀ t c c', ∀ x ∈ K t c, ∀ y ∈ K t c',
        dyadicCubeCell k x = dyadicCubeCell k y → c = c') ∧
      ∀ (G : Set Z) (hG : MeasurableSet G),
      let ηG := restrictOriginalRetainedResidual χ ξ a G
      let hηG := (restrictOriginalRetainedResidual_le χ ξ a ha hG).trans_eq hwhole
      let σ := fun t ↦ (D.types.rnSubplanTypes ηG hηG).component (false, t)
      (∀ t, compactColorGoodComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) +
        ∑ c, compactColorBadComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c = σ t) ∧
      (∑ p : C × T, compactColorBadComponent (σ p.2) (fun z ↦ a z.1)
        (fun z ↦ D.sourceCoordinate p.2 z.1) cell (K p.2) p.1 Set.univ).toReal < θ ∧
      (∀ t, ∀ᵐ p ∂compactColorGoodComponent (σ t) (fun p ↦ a p.1)
          (fun p ↦ D.sourceCoordinate t p.1) cell (K t),
        ∃ c, a p.1 ∈ cell c ∧ a p.2 ∈ cell c ∧
          D.sourceCoordinate t p.1 ∈ K t c ∧ D.targetCoordinate t p.2 ∈ K t c) := by
  classical
  have hξ : ξ ≤ π := (Measure.le_add_left le_rfl).trans_eq hwhole
  let τ := fun t ↦ (D.types.rnSubplanTypes ξ hξ).component (false, t)
  have hτ (t) : τ t ≤ D.types.component t := D.types.rnSubplanTypes_component_le ξ hξ (false, t)
  have hsum : (∑ t, τ t) = χ := by
    rw [D.types.rnSubplanTypes_complementary_sum_eq ξ hξ D.sum_eq, ← hwhole,
      Measure.add_sub_cancel]
  have hτχ (t) : τ t ≤ χ := by
    calc τ t ≤ ∑ t, τ t := Finset.single_le_sum (fun _ _ ↦ Measure.zero_le _) (Finset.mem_univ t)
      _ = χ := hsum
  have hcoverτ (t) : ∀ᵐ p ∂τ t, a p.1 ∈ ⋃ c, cell c := ae_mono (hτχ t) hcover
  obtain ⟨K, depth, hd, hK, hsep, hall⟩ :=
    D.exists_uniform_original_compact_subtype_splits_small_total τ hτ hF hcomplete hu ha horder
      hreg hcal cell hcell hdisjoint hcoverτ hθ
  refine ⟨K, depth, hd, hK, hsep, ?_⟩
  intro G hG
  dsimp only
  exact hall _ (fun t ↦ original_retained_type_label_restriction_le_of_sum_eq χ ξ a ha hG
    D.types hwhole t)

end OTSelector.Reconstruction
