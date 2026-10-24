import OTSelector.Reconstruction.FinslerOriginalGapBoundHaarCore
import OTSelector.Reconstruction.FinslerPopulationLocalPressureCore

/-! The true local distance-expansion core keeps the original support-gap
certificate of its rational windows; no additional geometric input is used. -/
open Set Function MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original Haar law supplies the actual geometric remainder on a further
large compact core, preserving every intensity, moment and recovery identity. -/
theorem PopulationFinitePressureCoreLaw.exists_local_core_with_original_gap
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] {η₀ η₁ : Measure M}
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}
    (hcore : PopulationFinitePressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hmoments : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instLocalPressureCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    (Good : (ℚ → M) → Prop) (hGood : ∀ᵐ z ∂lambda, Good z)
    (δ : ℝ≥0∞) (hδ : δ ≠ 0) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ ε,
      ∀ i, (D.haar.continuous.coefficient i).roots.Nonempty →
        ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap := by
  let _instLocalPressureCoreMetric : MetricSpace M := F.metricSpace
  let _instLocalPressureCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instLocalPressureCorePolish : PolishSpace M := inferInstance
  let _instLocalPressureCoreBorel : BorelSpace (ℚ → M) := inferInstance
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  obtain ⟨D,hgapD⟩ := hcore.exists_haar_core_with_original_gap hrecovery hmoments hcover
    hF hcomplete hu ha hinj hgap hsep r Good hGood δ hδ (ε / 2) (ENNReal.half_pos hε).ne'
  obtain ⟨K, hloss, hK, hrem⟩ :=
    OriginalPopulationCoefficientCore.exists_finite_uniform_distance_refinement
      hF hcomplete hu ha hinj D.continuous.coefficient hκ (ENNReal.half_pos hε).ne'
  have hsmall : lambda (⋃ i, K i)ᶜ < ε := by
    have hcover : (⋃ i, K i)ᶜ ⊆ D.continuous.population.rootsᶜ ∪
        ((⋃ i, (D.continuous.coefficient i).roots) \ ⋃ i, K i) := by
      intro z hz
      by_cases h : z ∈ D.continuous.population.roots
      · exact Or.inr ⟨D.continuous.union_eq.symm ▸ h, hz⟩
      · exact Or.inl h
    exact ((measure_mono hcover).trans (measure_union_le _ _)).trans_lt
      (by simpa only [ENNReal.add_halves] using
        ENNReal.add_lt_add D.continuous.population.complement_small hloss)
  refine ⟨{
    haar := D.refine hrecovery hcomplete ha hu.continuous.measurable
      (fun i ↦ (hK i).2.1) (fun i ↦ (hK i).1) hsmall
    remainder := hrem },?_⟩
  intro i hnonempty
  exact hgapD i (hnonempty.mono (hK i).1)

end OTSelector.Reconstruction
