import OTSelector.Reconstruction.FinslerOriginalWindowRetainedPairKernel
import OTSelector.Reconstruction.FinslerOriginalRetainedPressureNullRoots

/-! Actual finite original coefficient-window factories produce the retained
laws, loss rates and deterministic original-root pressure integral upper. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual finite original cores/windows internally produce every retained
kernel and normalization input. Original zero retained masses are allowed. The
result uses the unchanged original root and the same canonical physical p0. -/
theorem eventually_exists_originalWindow_pressure_root_cutoff
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hdim : 6 ≤ finrank ℝ E)
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ]
    (hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z)
      (condDistrib u a μ z) (condDistrib u a ν z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    (hb : Measurable b)
    (rn : ℕ → ℝ) (δn lossn : ℕ → ℝ≥0∞)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (width : ∀ n, Fin (D n).haar.continuous.count → ℝ)
    (Q : ∀ n i, FiniteScalarBins range (width n i))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0)) (hη : ∀ n, 0 ≤ η n ∧ η n ≤ 1)
    (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0) (μ.map a))
    (j : ℕ) (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    let χ := fun n ↦ (D n).originalWindowRetainedPairKernel hcomplete (Q n) γ
    ∀ᶠ n in atTop, ∃ K : Set (ℚ → M), MeasurableSet K ∧
      ((μ.map a).restrict (populationSeedRootPiece P a κ (μ.map a) j)).real Kᶜ < budget ∧
      IntegrableOn (originalRetainedSeedPhysicalPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f j n t)
        K ((μ.map a).restrict (populationSeedRootPiece P a κ (μ.map a) j)) ∧
      (∫ z in K, originalRetainedSeedPhysicalPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f j n t z
        ∂(μ.map a).restrict (populationSeedRootPiece P a κ (μ.map a) j)) <
      (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t z
        ∂(μ.map a).restrict (populationSeedRootPiece P a κ (μ.map a) j)) + tolerance := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  have hactual := originalWindowRetainedPairKernel_ae_mass_recovery hrange γ gap hgap.le rn δn lossn
    D hcomplete width Q hδ hδ1 hδlim hloss
  exact eventually_exists_originalRetainedSeedPhysicalPressure_cutoff_of_mass_recovery hlaw hF hcomplete
    hu ha hinj hdim hgap hsep γ hγ
    (fun n ↦ (D n).originalWindowRetainedPairKernel hcomplete (Q n) γ)
    (Filter.Eventually.of_forall fun z n ↦ hactual.1 n z) hactual.2 hb f hp0
    (fun n _ ↦ η n) (fun _ ↦ measurable_const)
    (Filter.Eventually.of_forall fun _ ↦ ⟨hηlim,hη⟩) j t budget tolerance hbudget htolerance

end OTSelector.Reconstruction
