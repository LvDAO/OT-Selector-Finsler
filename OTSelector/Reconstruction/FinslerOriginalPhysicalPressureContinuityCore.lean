import OTSelector.Reconstruction.FinslerOriginalPhysicalRootPressure
import OTSelector.MeasureTheory.LusinCompactProperty

/-! Actual canonical original root pressures are continuous on deterministic
large compact original cores. No pressure continuity hypothesis is added. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z] [BorelSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

/-- Original physical laws internally give compact continuity cores for the
same canonical pressure at any fixed physical tilt. Original root mass is
lost by less than the requested amount, and any given original AE property
holds at every retained root. All choices precede original iid sampling. -/
theorem exists_compact_original_physical_pressure_continuity_core
    (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hdim : 6 ≤ finrank ℝ E)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diameter)
    (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
    (hγ : ∀ᵐ z ∂lambda, Vlasov.IsCoupling (γ z)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ) (t : ℝ)
    {H : Set Z} (hH : MeasurableSet H) (hfinite : lambda H ≠ ⊤)
    {Good : Z → Prop} (hGood : ∀ᵐ z ∂lambda.restrict H, Good z)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K ⊆ H, IsCompact K ∧ lambda (H \ K) < ε ∧
      ContinuousOn (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t) K ∧
      ∀ z ∈ K, Good z := by
  let p := originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t
  have hp : AEStronglyMeasurable p lambda :=
    (originalPhysicalFinslerRootPressure_measurable_nonneg f hlaw hF hcomplete hu ha hinj
      hdim hgap hsep γ hγ hb t).1
  let pB := hp.mk p
  have hpB : Measurable pB := hp.stronglyMeasurable_mk.measurable
  have hproperty : ∀ᵐ z ∂lambda.restrict H, pB z = p z ∧ Good z :=
    (ae_restrict_of_ae hp.ae_eq_mk.symm).and hGood
  obtain ⟨K,hKH,hK,hloss,hcont,hall⟩ :=
    exists_lusin_compact_core_with_ae_property hH hfinite hpB hproperty hε
  refine ⟨K,hKH,hK,hloss,?_,fun z hz ↦ (hall z hz).2⟩
  exact hcont.congr (fun z hz ↦ (hall z hz).1.symm)

end OTSelector.Reconstruction
