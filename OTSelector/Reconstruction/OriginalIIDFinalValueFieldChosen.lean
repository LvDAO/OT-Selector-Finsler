import OTSelector.Reconstruction.OriginalIIDFinalValueFieldFinalInputs
import OTSelector.Reconstruction.OriginalIIDFinalValueFieldCommonGap
import OTSelector.Reconstruction.FinslerOriginalChosenPopulationAtlas

/-! The SAME chosen population atlas exposes the exact remaining reverse-pressure continuation. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal NNReal Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M}
/-- No population potential is reselected. The original chosen atlas produces
all standing data, one common physical/conditional gap, and the complete final
fields once the explicitly named local focal reverse comparison is connected. -/
theorem chosenPopulationPotential_final_inputs_from_focal_reverse
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (m : Measure E) [m.IsAddHaarMeasure] (ωM : Measure M)
    (ρ₀ ρ₁ : M → ℝ) {K₀ K₁ : ℝ≥0}
    (hρ₀ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₀ ρ₀)
    (hρ₁ : let _inst : MetricSpace M := F.metricSpace; LipschitzWith K₁ ρ₁)
    (hρ₀nonneg : ∀ x, 0 ≤ ρ₀ x) (hρ₁nonneg : ∀ x, 0 ≤ ρ₁ x)
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)))]
    (v : M → E → ℝ)
    (hv : ∀ old, ContinuousOn (v old) (extChartAt 𝓘(ℝ, E) old).target)
    (hvnonneg : ∀ old, ∀ y ∈ (extChartAt 𝓘(ℝ, E) old).target, 0 ≤ v old y)
    (hvolume : ∀ old : M, let χ := extChartAt 𝓘(ℝ, E) old
      (ωM.restrict χ.source).map χ = (m.restrict χ.target).withDensity
        (fun y => ENNReal.ofReal (v old y)))
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₀ x)), x ∈ A)
    (hν : ∀ᵐ y ∂ωM.withDensity (fun x => ENNReal.ofReal (ρ₁ x)), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (R : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (R n)]
    (X Y : ∀ n, Fin (n+1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (R n)) (hYi : ∀ n, iIndepFun (Y n) (R n))
    (hXlaw : ∀ n i, (R n).map (X n i) = ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))
    (hYlaw : ∀ n i, (R n).map (Y n i) = ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))
    (hXY : ∀ n, IndepFun (fun ξ i ↦ X n i ξ) (fun ξ i ↦ Y n i ξ) (R n)) :
    let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
    let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
    let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
    let μp : ProbabilityMeasure M := ⟨μ,inferInstance⟩
    let νp : ProbabilityMeasure M := ⟨ν,inferInstance⟩
    ∃ (a : M → (ℚ → M)) (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker) (b : (ℚ → M) × ℝ → M)
      (vP : ℕ → E → ℝ) (gap diameter : ℝ) (hκ : ∀ j, (κ j).IsAddHaarMeasure),
      letI := hκ
      (let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u) ∧ Measurable a ∧ Measurable b ∧
      (∀ x ∈ F.potentialRegularDomain u, b (a x,u x)=x) ∧
      (∀ r : ℝ, PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ vP b r) ∧
      PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν ∧
      0 < gap ∧ (let _inst : MetricSpace M := F.metricSpace; ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y) ∧
      PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter ∧
      ((∀ᵐ z ∂μ.map a, ∀ f : M × M →ᵇ ℝ, ∀ j, ∀ hz : z ∈ populationSeedRootPiece P a κ (μ.map a) j,
          ∀ data : OriginalSeedConditionalMoments (P j).seed
            (populationSeedPieceLabel P a κ (μ.map a) j ⟨z,hz⟩)
            (condDistrib u a μ z) (condDistrib u a ν z),
          ∀ Qf : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
            (condDistrib u a μ z) (condDistrib u a ν z) (data.originalFocalKinetic gap)
            (originalPhysicalRootProbe b f z),
          ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure (finrank ℝ (P j).seed.covector.ker)
            id id (condDistrib u a μ z) (condDistrib u a ν z) (data.originalFocalKinetic gap)
            (originalPhysicalRootProbe b f z) R t) ≤ Qf.value t) →
        ∃ inputs : FinslerSelectorFinalInputs F μp νp hA hB hμ hν R X Y u,
          inputs.pressureLower = originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν ∧
          inputs.pressureUpper = originalSameAtlasUpperPressure P a κ μp νp b hA hB hμ hν) := by
  let μ := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x))
  let ν := ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x))
  let u := chosenPopulationPotential hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁
    hρ₀nonneg hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : BorelSpace (ℚ → M) := inferInstance
  have hatlas := chosenPopulationPotential_atlas
    hF hcomplete hdim m ωM ρ₀ ρ₁ hρ₀ hρ₁ hρ₀nonneg
      hρ₁nonneg v hv hvnonneg hvolume hA hB hAB hμ hν
  dsimp only [ChosenWitnessSpec] at hatlas
  obtain ⟨a,hu,_hN,hμreg,hνreg,ha,hinj,horder,hbalance,hface,
    P,κ,b,_hcover,_hμcover,_hνcover,hκ,_hprod,hb,hbinv,_hwindow,htail⟩ := hatlas
  obtain ⟨_hμwindow,_hνwindow,_hμfull,_hνfull,_hμseed,_hνseed,_hsupport,_hcomparison,
    hrecovery,_hcompact,_hfinite,hmoments,_hpressure,_hcontinuous,hhaar,_hlocal,
    hseparation,_hconditionalMoments⟩ := htail
  obtain ⟨δ,hδ,hsep,_hcoefficient,_hbounded⟩ := hseparation
  obtain ⟨gap,hgap,hdist,hsepCommon⟩ := exists_original_common_physical_conditional_gap
    u a (μ.map a) μ ν hA hB hAB hδ hsep
  let vP := fun j ↦ populationChartVolumeExtension v ((P j).toManifold (P j).center)
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  refine ⟨a,P,κ,b,vP,gap,Metric.diam (A ∪ B),hκ,hu,ha,hb,hbinv,hhaar,hmoments,hgap,hdist,hsepCommon,?_⟩
  intro hreverse
  exact exists_original_same_atlas_final_inputs_of_focal_reverse
    (hhaar 0) hrecovery hF hcomplete hu ha hinj hκ horder hbalance hA hB hAB hμ hν hνreg hμreg
    hface hgap hdist hdim hsepCommon hmoments hb hreverse
    (hμreg.mono fun x hx ↦ hbinv x hx) (hνreg.mono fun y hy ↦ hbinv y hy)
    R X Y hX hY hXi hYi hXlaw hYlaw hXY

end OTSelector.Reconstruction
