import OTSelector.Reconstruction.FinslerOriginalRetainedGlobalPressure
import OTSelector.Reconstruction.FinslerOriginalClosedWindowPairKernel

/-! Canonical original closed-window kernels give a whole-atlas pressure
integral upper on actual finite cores, before choosing any fine cost bins. -/
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

/-- One original-root cutoff controls the pressure integral of the complete
actual atlas. All retained kernels/loss rates are produced by actual original
finite cores. At every stage the pressure vanishes outside that finite core. -/
theorem eventually_exists_originalClosedWindow_global_pressure_cutoff
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hdim : 6 ≤ finrank ℝ E)
    {range : Set ℝ}
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
    (hδ : ∀ n, δn n ≠ ⊤)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0)) (hη : ∀ n, 0 ≤ η n ∧ η n ≤ 1)
    (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0) (μ.map a))
    (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
    (∀ n z, z ∉ (D n).haar.continuous.population.roots →
      originalRetainedFinslerRootPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f n t z = 0) ∧
    ∀ᶠ n in atTop, ∃ K : Set (ℚ → M), MeasurableSet K ∧ (μ.map a).real Kᶜ < budget ∧
      IntegrableOn (originalRetainedFinslerRootPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f n t)
        K (μ.map a) ∧
      (∫ z in K, originalRetainedFinslerRootPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f n t z
        ∂μ.map a) < (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t z
        ∂μ.map a) + tolerance := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
  have hactual := originalClosedWindowPairKernel_ae_mass_recovery γ gap hgap.le rn δn lossn
    D hcomplete hδ hδlim hloss
  refine ⟨?_,?_⟩
  · intro n z hz
    have hnot : z ∉ ⋃ i, ((D n).haar.continuous.coefficient i).roots := by
      rw [(D n).haar.continuous.union_eq]
      exact hz
    have hk : χ n z = 0 := finiteCellPairKernel_eq_zero _ _ _ hnot
    exact originalRetainedFinslerRootPressure_eq_zero_of_kernel_eq_zero P a κ (μ.map a)
      χ (fun n _ ↦ η n) b f hdim n t z hk
  · exact eventually_exists_originalRetainedFinslerRootPressure_global_cutoff hlaw hF hcomplete
      hu ha hinj hdim hgap hsep γ hγ χ
      (Filter.Eventually.of_forall fun z n ↦ hactual.1 n z) hactual.2 hb f hp0
      (fun n _ ↦ η n) (fun _ ↦ measurable_const)
      (Filter.Eventually.of_forall fun _ ↦ ⟨hηlim,hη⟩) t budget tolerance hbudget htolerance

/-- The single global cutoff can be kept inside the ACTUAL finite original
core, without changing its pressure integral. The additional discarded
original root mass is charged exactly once to that core's stored loss. -/
theorem eventually_exists_originalClosedWindow_global_pressure_cutoff_on_core
    (hlaw : PopulationSeedPieceMomentLaw P a κ (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hdim : 6 ≤ finrank ℝ E)
    {range : Set ℝ}
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
    (hδ : ∀ n, δn n ≠ ⊤)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (hloss : (∑' n, lossn n) ≠ ⊤)
    (η : ℕ → ℝ) (hηlim : Tendsto η atTop (𝓝 0)) (hη : ∀ n, 0 ≤ η n ∧ η n ≤ 1)
    (f : M × M →ᵇ ℝ)
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f 0) (μ.map a))
    (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
    ∀ᶠ n in atTop, ∃ K : Set (ℚ → M), MeasurableSet K ∧
      K ⊆ (D n).haar.continuous.population.roots ∧
      (μ.map a).real Kᶜ < budget + (lossn n).toReal ∧
      IntegrableOn (originalRetainedFinslerRootPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f n t)
        K (μ.map a) ∧
      (∫ z in K, originalRetainedFinslerRootPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f n t z
        ∂μ.map a) < (∫ z, originalPhysicalFinslerRootPressure P a κ (μ.map a) μ ν b f t z
        ∂μ.map a) + tolerance := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let χ := fun n ↦ (D n).originalClosedWindowPairKernel hcomplete γ
  have hactual := eventually_exists_originalClosedWindow_global_pressure_cutoff hlaw hF hcomplete hu
    ha hinj hdim γ hγ hgap hsep hb rn δn lossn D hδ hδlim hloss
    η hηlim hη f hp0 t budget tolerance hbudget htolerance
  filter_upwards [hactual.2] with n hn
  obtain ⟨K,hK,hmass,hI,hupper⟩ := hn
  let roots := (D n).haar.continuous.population.roots
  let p := originalRetainedFinslerRootPressure P a κ (μ.map a) χ (fun n _ ↦ η n) b f n t
  have hroots : MeasurableSet roots := (D n).haar.continuous.population.compact.measurableSet
  have hG : MeasurableSet (K ∩ roots) := hK.inter hroots
  have hlossn : lossn n ≠ ⊤ := ENNReal.ne_top_of_tsum_ne_top hloss n
  have hrootmass : (μ.map a).real rootsᶜ < (lossn n).toReal :=
    (ENNReal.toReal_lt_toReal (measure_ne_top _ _) hlossn).mpr
      (D n).haar.continuous.population.complement_small
  have hmassG : (μ.map a).real (K ∩ roots)ᶜ < budget + (lossn n).toReal := by
    have hh := measureReal_union_le (μ := μ.map a) Kᶜ rootsᶜ
    rw [compl_inter]
    linarith only [hh,hmass,hrootmass]
  have hfun : (K ∩ roots).indicator p = K.indicator p := by
    funext z
    by_cases hzK : z ∈ K
    · by_cases hzR : z ∈ roots
      · have hzG : z ∈ K ∩ roots := ⟨hzK,hzR⟩
        rw [indicator_of_mem hzG,indicator_of_mem hzK]
      · rw [indicator_of_notMem (fun hz ↦ hzR hz.2),indicator_of_mem hzK]
        exact (hactual.1 n z hzR).symm
    · rw [indicator_of_notMem (fun hz ↦ hzK hz.1),indicator_of_notMem hzK]
  have hIntegral : (∫ z in K ∩ roots, p z ∂μ.map a) = ∫ z in K, p z ∂μ.map a := by
    rw [← integral_indicator hG,← integral_indicator hK,hfun]
  refine ⟨K ∩ roots,hG,inter_subset_right,hmassG,hI.mono_set inter_subset_left,?_⟩
  change (∫ z in K ∩ roots, p z ∂μ.map a) < _
  rw [hIntegral]
  exact hupper

end OTSelector.Reconstruction
