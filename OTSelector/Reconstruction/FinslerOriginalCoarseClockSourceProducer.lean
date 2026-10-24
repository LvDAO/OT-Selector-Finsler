import OTSelector.Reconstruction.FinslerOriginalCoarseClockRepair
import OTSelector.Reconstruction.FinslerConditionalLegalBlock
import OTSelector.Reconstruction.FinslerPhysicalSceneClockScreenCoefficient

/-! Original compact disjoint calibrated carriers produce one fixed coarse
repair partition. Actual coefficient cores and arbitrarily fine coefficient
resampling are then controlled by this same partition. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {δ : ℝ≥0∞}

/-- The fixed coarse partition is produced from the original compact disjoint
calibrated carriers before any core or fine coefficient bins. On every original
core, a smaller actual clock screen and arbitrarily accurate fine models retain
at most twice this coarse count of source neighborhoods. -/
theorem exists_original_coarse_clock_source_control
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hbalance : μ.map a = ν.map a) {A B N : Set M}
    (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B) (hN : MeasurableSet N)
    (hμA : ∀ᵐ x ∂μ, x ∈ A) (hνB : ∀ᵐ x ∂ν, x ∈ B)
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ x ∂ν, x ∈ N)
    (horder : let _inst : MetricSpace M := F.metricSpace;
      ∀ x ∈ N, ∀ y ∈ N, (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y) :
    ∃ gap : ℝ, 0 < gap ∧ ∃ coarse : FiniteScalarBins (u '' A ∪ u '' B) gap,
    ∀ C : OriginalPopulationCoefficientCore P a κ (μ.map a) μ ν δ,
    ∀ {rootLoss : ℝ≥0∞}, rootLoss ≠ 0 →
    ∃ C' : OriginalPopulationCoefficientCore P a κ (μ.map a) μ ν δ,
      C'.seedIndex = C.seedIndex ∧ C'.window.val.1 = C.window.val.1 ∧
      C'.window.val.2.1 = C.window.val.2.1 ∧ C'.roots ⊆ C.roots ∧
      (μ.map a) (C.roots \ C'.roots) < rootLoss ∧
      ∀ᵐ z ∂μ.map a, ∀ hz : z ∈ C'.roots,
      ∃ K ≥ 0,
        (∀ {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width),
          ∀ i j v, |C'.clockClassKinetic Q z i j v| ≤ K * ∑ l, v l ^ 2) ∧
        ∀ (f : M × M →ᵇ ℝ) {width ε probeError : ℝ},
          0 < width → 0 < ε → 0 < probeError →
        ∃ fine : FiniteScalarBins (u '' A ∪ u '' B) width,
          (∀ i j, C'.clockClassAllowed fine i j →
            ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
              (∀ v, |matrixQuadratic (C'.matrix z (x,y)) v -
                C'.clockClassKinetic fine z i j v| ≤ ε * C'.clockClassKinetic fine z i j v) ∧
              |originalReferenceClockProbe C' z hz f (x,y) -
                C'.clockClassProbe fine z hz f i j| ≤ probeError) ∧
          ∀ (m n : ℕ) (source : Fin m → ↥(u '' A ∪ u '' B)) (target : Fin n → ↥(u '' A ∪ u '' B)),
            (∀ i, (source i).val ∈ (condDistrib u a μ z).support) →
            (∀ j, (target j).val ∈ (condDistrib u a ν z).support) →
            ∃ label : Fin m → Fin coarse.count × Bool,
              ∃ allows : (Fin coarse.count × Bool) → Fin n → Prop,
              ∀ i j, C'.clockClassAllowed fine (fine.rangeClassify (source i))
                (fine.rangeClassify (target j)) ↔ allows (label i) j := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨gap,hgap,coarse,hseparated⟩ := exists_population_conditional_scalar_bins μ ν ha
    hbalance hu.continuous hA hB hAB hN hμA hνB hμN hνN horder
  refine ⟨gap,hgap,coarse,?_⟩
  intro C rootLoss hrootLoss
  obtain ⟨C',hseed,hl,hr,hgap',hsub,hloss⟩ :=
    C.exists_smaller_clock_screen_refinement hF hcomplete hu ha hinj hgap hrootLoss
  refine ⟨C',hseed,hl,hr,hsub,hloss,?_⟩
  filter_upwards [hseparated] with z hzSeparated
  intro hz
  obtain ⟨K,hK,hbound⟩ := C'.exists_all_clockClassKinetic_bound z hz
  refine ⟨K,hK,hbound,?_⟩
  intro f width ε probeError hwidth hε hprobe
  obtain ⟨fine,hmodel⟩ := C'.exists_full_clockClass_model_with_endpoints hF hcomplete hu ha hinj
    z hz f f.continuous ((hA.image hu.continuous).union (hB.image hu.continuous)) hwidth hε hprobe
  have hfull : ∀ i j, C'.clockClassAllowed fine i j →
      ∀ x ∈ fine.cell i, ∀ y ∈ fine.cell j,
        x ∈ Icc (C'.window.val.1 : ℝ) C'.window.val.2.1 ∧
        y ∈ Icc (C'.window.val.1 : ℝ) C'.window.val.2.1 ∧ x < y := by
    intro i j hij x hx y hy
    have h := hmodel i j hij x hx y hy
    exact ⟨h.1,h.2.1,h.2.2.2.1⟩
  refine ⟨fine,?_,?_⟩
  · intro i j hij x hx y hy
    exact (hmodel i j hij x hx y hy).2.2.2.2
  · intro m n source target hsource htarget
    exact C'.exists_fine_clock_mask_coarse_source_classes fine coarse hgap hgap' hfull source target
      (fun i j ↦ hzSeparated.2 _ (hsource i) _ (htarget j))

end OTSelector.Reconstruction
