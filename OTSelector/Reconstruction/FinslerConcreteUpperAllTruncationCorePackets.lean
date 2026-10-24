import OTSelector.Reconstruction.FinslerConcreteUpperRetainedCompactTruncation
import OTSelector.Reconstruction.FinslerConcreteUpperFineEnergyBudget
import OTSelector.Reconstruction.FinslerRelativeLawOriginalRetainedTypeRestriction
import OTSelector.Reconstruction.FinslerRelativeLawRetainedFlagSampling

/-! Fixed original compact colors produce the good/bad energy and source-defect
packets for every later deterministic truncation and every empirical order. -/
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
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {q : ℕ}

/-- The actual compact/color approximation and its positive separation depth
are chosen once from the original retained components, before every later
original submeasure or changing microscopic grid is supplied. -/
theorem PopulationTypedCostData.exists_original_all_truncation_expected_core_packets
    (D : PopulationTypedCostData π μ ν T q
      (fun x y ↦ (F.lengthEDist x y).toReal - u y + u x))
    (hq : 4 < q) (hπ : Vlasov.IsCoupling π μ ν)
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
    {C : Type*} [Fintype C]
    [MeasurableSpace (Option T)] [MeasurableSingletonClass (Option T)]
    [MeasurableSpace (Option (C × T))] [MeasurableSingletonClass (Option (C × T))]
    [MeasurableSpace (Option (CellRefinedType C T))]
    [MeasurableSingletonClass (Option (CellRefinedType C T))]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
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
      let good := fun t ↦ compactColorGoodComponent (σ t) (fun p ↦ a p.1)
        (fun p ↦ D.sourceCoordinate t p.1) cell (K t)
      let bad := fun c t ↦ compactColorBadComponent (σ t) (fun p ↦ a p.1)
        (fun p ↦ D.sourceCoordinate t p.1) cell (K t) c
      ∃ hsplit : ∀ t, good t + ∑ c, bad c t = σ t,
        (∑ p : C × T, bad p.1 p.2 Set.univ).toReal < θ ∧
      ∀ n : ℕ, 0 < n →
      let cost := fun x y ↦ (F.lengthEDist x y).toReal - u y + u x
      let R := D.types.rnCellRefinedTypes ηG hηG good bad hsplit
      let P := (Measure.pi (fun _ : Fin n ↦ R.sourceMarkedLaw μ)).prod
        (Measure.pi (fun _ : Fin n ↦ R.targetMarkedLaw ν))
      ∃ KG KB : ℕ, depth ≤ KG ∧ 1 ≤ KB ∧
        Integrable (fun sample ↦
          fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG sample +
          fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB sample) P ∧
        ((n : ℝ) ^ (2 / (q : ℝ)) / n) *
          (∫ sample, fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG sample +
            fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB sample ∂P) ≤
          D.quadraticConstant * dyadicMatchingConstant q * (Fintype.card T : ℝ) ^ (2 / (q : ℝ)) +
          D.quadraticConstant * dyadicMatchingConstant q * (Fintype.card (C × T) : ℝ) ^ (2 / (q : ℝ)) *
            (∑ p : C × T, bad p.1 p.2 Set.univ).toReal ^ (1 - 2 / (q : ℝ)) +
          D.globalBound * (Real.sqrt (2 * Fintype.card T) + Real.sqrt (2 * Fintype.card (C × T))) *
            (n : ℝ) ^ (2 / (q : ℝ) - 1 / 2) ∧
        Integrable (fun sample ↦ fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate depth sample +
          fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample) P ∧
        (∫ sample, fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate depth sample +
          fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample ∂P) ≤
          (Fintype.card T : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ depth + 1) ^ q) +
          (Fintype.card (C × T) : ℝ) * Real.sqrt (2 * (n : ℝ) * ((2 : ℝ) ^ (1 : ℕ) + 1) ^ q) ∧
        ∀ᵐ sample ∂P, ∃ coreGood coreBad : OTSelector.PartialMatching n n,
          (∀ e ∈ coreGood.edges, ∃ t,
            (sample.1 e.1).2.bind cellRefinedGoodType = some t ∧
            (sample.2 e.2).2.bind cellRefinedGoodType = some t ∧
            ∃ c, cellRefinedGoodCell a cell (sample.1 e.1) = some c ∧
              cellRefinedGoodCell a cell (sample.2 e.2) = some c) ∧
          (∀ e ∈ coreBad.edges, ∃ p : C × T,
            (sample.1 e.1).2.bind cellRefinedBadType = some p ∧
            (sample.2 e.2).2.bind cellRefinedBadType = some p) ∧
          coreGood.cost (fun i j ↦ cost (sample.1 i).1 (sample.2 j).1) ≤
            fineGoodHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KG sample ∧
          coreBad.cost (fun i j ↦ cost (sample.1 i).1 (sample.2 j).1) ≤
            fineBadHierarchyEnergy D.sourceCoordinate D.targetCoordinate cost KB sample ∧
          fineGoodSourceCount sample - (coreGood.card : ℝ) ≤
            fineGoodDiscrepancy D.sourceCoordinate D.targetCoordinate depth sample ∧
          fineBadSourceCount sample - (coreBad.card : ℝ) ≤
            fineBadDiscrepancy D.sourceCoordinate D.targetCoordinate sample := by
  classical
  obtain ⟨K, depth, hd, hK, hsep, hall⟩ :=
    D.exists_original_retained_compact_truncation_splits χ ξ hwhole hF hcomplete hu ha horder
      hreg hcal cell hcell hdisjoint hcover hθ
  refine ⟨K, depth, hd, hK, hsep, ?_⟩
  intro G hG
  dsimp only
  obtain ⟨hsplit, hsmall, hgood⟩ := hall G hG
  refine ⟨hsplit, hsmall, ?_⟩
  intro n hn
  exact D.exists_original_good_bad_expected_core_packet _ _ _ _ hsplit hq hn hd hπ
    a a ha ha cell hcell hdisjoint K (fun t c ↦ (hK t c).measurableSet) hgood
      (hsep depth le_rfl)

end OTSelector.Reconstruction
