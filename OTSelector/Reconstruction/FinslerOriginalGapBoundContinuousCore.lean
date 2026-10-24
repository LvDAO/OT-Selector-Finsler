import OTSelector.Reconstruction.FinslerOriginalGapBoundCoefficientCores
import OTSelector.Reconstruction.FinslerPopulationContinuousPressureCore

/-! Preserve the actual rational-window gap certificate while assembling
continuous original coefficient and full conditional-law cores. -/
open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The original supported moment, density and recovery laws produce finite joint
coefficient continuity cores without replacing the original label measure. -/
theorem PopulationFinitePressureCoreLaw.exists_continuous_core_with_original_gap
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    [IsFiniteMeasure lambda] {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
    (hcore : PopulationFinitePressureCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v b)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b lambda η₀ η₁)
    (hmoments : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instContinuousCoreMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    (Good : (ℚ → M) → Prop) (hGood : ∀ᵐ z ∂lambda, Good z)
    (δ : ℝ≥0∞) (hδ : δ ≠ 0) (ε : ℝ≥0∞) (hε : ε ≠ 0) :
    ∃ D : PopulationContinuousPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good δ ε,
      ∀ i, (D.coefficient i).roots.Nonempty →
        ((D.coefficient i).window.val.2.2 : ℝ) ≤ gap := by
  let _instJointCoreMetric : MetricSpace M := F.metricSpace
  let _instJointCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instJointCorePolish : PolishSpace M := inferInstance
  let _instJointCoreLabelsBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨D⟩ := hcore Good hGood (ε / 2) (ENNReal.half_pos hε).ne'
  obtain ⟨N, C, hdisjoint, hcompact, hsub, _, hloss, _,hgapC⟩ :=
    hmoments.exists_finite_coefficient_cores_within_original_gap hcover hF hcomplete hu ha hinj
      hgap hsep hGood hδ (ENNReal.half_pos hε).ne' D.compact
  have hsmall : lambda (⋃ i, (C i).roots)ᶜ < ε := by
    apply hloss.trans_le
    calc
      lambda D.rootsᶜ + ε / 2 ≤ ε / 2 + ε / 2 := add_le_add D.complement_small.le le_rfl
      _ = ε := ENNReal.add_halves _
  exact ⟨{
    population := D.refine hrecovery hcomplete ha hu.continuous.measurable hcompact hsub hsmall
    count := N
    coefficient := C
    disjoint := hdisjoint
    union_eq := rfl
    recovery := hrecovery.finite_recovery ha hu.continuous.measurable _
      (fun i ↦ (C i).roots_compact.measurableSet) hdisjoint },hgapC⟩

end OTSelector.Reconstruction
