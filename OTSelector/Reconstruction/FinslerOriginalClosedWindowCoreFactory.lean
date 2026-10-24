import OTSelector.Reconstruction.FinslerOriginalGapBoundLocalCore
import OTSelector.Reconstruction.FinslerOriginalClosedWindowPressureCutoffs
import OTSelector.Reconstruction.FinslerOriginalWindowCoreFactory

/-! Original geometric/moment data choose all gap-certified finite window
cores, canonical retained kernels, and pressure cutoffs before fine bins. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
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
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M} {r : ℝ}

/-- All original finite local cores are chosen with the existing support-gap
certificate. Their canonical retained law and full-mass recovery are produced
before any fine bins, reference roots, or original samples are chosen. -/
theorem PopulationFinitePressureCoreLaw.exists_originalClosedWindow_kernel_recovery
    (hcore : PopulationFinitePressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (hcover : ∀ᵐ z ∂μ.map a, z ∈ ⋃ j, populationSeedRootPiece P a κ (μ.map a) j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ]
    (hGood : ∀ᵐ z ∂μ.map a,
      originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range z) :
    let δn := fun n ↦ ENNReal.ofReal (originalWindowStageAccuracy n)
    ∃ D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      r (δn n) (originalWindowStageRootLoss n),
      (∀ n i, ((D n).haar.continuous.coefficient i).roots.Nonempty →
        (((D n).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap) ∧
      (∀ n z, (D n).originalClosedWindowPairKernel hcomplete γ z ≤ γ z) ∧
      ∀ᵐ z ∂μ.map a, Tendsto
        (fun n ↦ ((D n).originalClosedWindowPairKernel hcomplete γ z).real univ)
        atTop (𝓝 1) := by
  dsimp only
  have hacc := originalWindowStageAccuracy_properties
  have hroot := originalWindowStageRootLoss_properties
  let δn := fun n ↦ ENNReal.ofReal (originalWindowStageAccuracy n)
  have hδ0 n : δn n ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (hacc.1 n).1)
  have hex n := hcore.exists_local_core_with_original_gap hrecovery hlaw hcover
    hF hcomplete hu ha hinj (fun _ ↦ inferInstance) hgap hsep
    (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
    hGood (δn n) (hδ0 n) (originalWindowStageRootLoss n) (hroot.1 n) (r := r)
  let D := fun n ↦ (hex n).choose
  have hδreal n : (δn n).toReal = originalWindowStageAccuracy n :=
    ENNReal.toReal_ofReal (hacc.1 n).1.le
  have hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0) := by
    simpa only [hδreal] using hacc.2
  refine ⟨D,fun n ↦ (hex n).choose_spec,?_⟩
  exact originalClosedWindowPairKernel_ae_mass_recovery γ gap hgap.le
    (fun _ ↦ r) δn originalWindowStageRootLoss D hcomplete
    (fun _ ↦ ENNReal.ofReal_ne_top) hδlim (by rw [hroot.2]; norm_num)

/-- The same internally produced gap-certified cores and canonical original
kernels recover the corrected physical pressure integral on actual finite
root cores. Fine class bins are free to be selected afterwards. -/
theorem PopulationFinitePressureCoreLaw.exists_originalClosedWindow_pressure_recovery
    (hcore : PopulationFinitePressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (hcover : ∀ᵐ z ∂μ.map a, z ∈ ⋃ j, populationSeedRootPiece P a κ (μ.map a) j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hdim : 6 ≤ finrank ℝ E)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a (μ.map a) μ ν gap diameter)
    {range : Set ℝ} (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ]
    (hGood : ∀ᵐ z ∂μ.map a,
      originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range z)
    (hb : Measurable b) (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0) (μ.map a)) :
    let δn := fun n ↦ ENNReal.ofReal (originalWindowStageAccuracy n)
    ∃ D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      r (δn n) (originalWindowStageRootLoss n),
      (∀ n i, ((D n).haar.continuous.coefficient i).roots.Nonempty →
        (((D n).haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap) ∧
      let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
      (∀ n z, χ n z ≤ γ z) ∧
      (∀ᵐ z ∂μ.map a, Tendsto (fun n ↦ (χ n z).real univ) atTop (𝓝 1)) ∧
      ∀ t budget tolerance : ℝ, 0 < budget → 0 < tolerance →
        ∀ᶠ n in atTop, ∃ K : Set (ℚ → M), MeasurableSet K ∧
          K ⊆ (D n).haar.continuous.population.roots ∧
          (μ.map a).real Kᶜ < budget + (originalWindowStageRootLoss n).toReal ∧
          IntegrableOn (originalRetainedFinslerRootPressure P a κ (μ.map a) χ
            (fun n _ ↦ originalWindowStageAccuracy n) b f n t) K (μ.map a) ∧
          (∫ z in K, originalRetainedFinslerRootPressure P a κ (μ.map a) χ
            (fun n _ ↦ originalWindowStageAccuracy n) b f n t z ∂μ.map a) <
            (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t z ∂μ.map a) +
              tolerance := by
  dsimp only
  obtain ⟨D,hgapD,hχ,hmass⟩ := hcore.exists_originalClosedWindow_kernel_recovery
    hrecovery hlaw hcover hF hcomplete hu ha hinj hgap hsep γ hGood (r := r)
  refine ⟨D,hgapD,hχ,hmass,?_⟩
  intro t budget tolerance hbudget htolerance
  have hacc := originalWindowStageAccuracy_properties
  have hroot := originalWindowStageRootLoss_properties
  have hγ : ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (γ z)
      (condDistrib u a μ z) (condDistrib u a ν z) ∧ ∀ᵐ p ∂γ z, p.1 ≤ p.2 :=
    hGood.mono (fun _ h ↦ ⟨h.1,h.2.1.mono (fun _ hg ↦ sub_nonneg.mp (hgap.le.trans hg))⟩)
  exact eventually_exists_originalClosedWindow_global_pressure_cutoff_on_core hlaw hF hcomplete hu
    ha hinj hdim γ hγ hgap hsep hb (fun _ ↦ r)
    (fun n ↦ ENNReal.ofReal (originalWindowStageAccuracy n)) originalWindowStageRootLoss D
    (fun _ ↦ ENNReal.ofReal_ne_top)
    (by simpa only [ENNReal.toReal_ofReal (hacc.1 _).1.le] using hacc.2)
    (by rw [hroot.2]; norm_num) originalWindowStageAccuracy hacc.2
    (fun n ↦ ⟨(hacc.1 n).1.le,(hacc.1 n).2.le⟩) f hp0
    t budget tolerance hbudget htolerance

end OTSelector.Reconstruction
