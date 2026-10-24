import OTSelector.Probability.PositiveRetainedKernelCompletion
import OTSelector.Reconstruction.FinslerOriginalRetainedPressureRootCutoffs

/-! Null original retained roots are normalized without changing the actual
weighted original pair measure or its physical pressure. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Canonical retained pressure depends only on the actual retained measure
at the original root; no values at other roots or measure version are changed. -/
theorem originalSeedRetainedRootPressure_congr_at_root
    (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (χ ψ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] [∀ z, IsFiniteMeasure (ψ z)]
    (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (z : Z) (hχ : χ z = ψ z) (t : ℝ) :
    originalSeedRetainedRootPressure S a χ b f z t =
      originalSeedRetainedRootPressure S a ψ b f z t := by
  have hpair : originalNormalizedRetainedPairKernel χ z = originalNormalizedRetainedPairKernel ψ z := by
    change (if χ z univ = 0 then Measure.dirac (0,0) else (χ z univ)⁻¹ • (χ z).restrict univ) =
      (if ψ z univ = 0 then Measure.dirac (0,0) else (ψ z univ)⁻¹ • (ψ z).restrict univ)
    rw [hχ]
  unfold originalSeedRetainedRootPressure
  congr 1
  funext R
  simp only [originalSeedRetainedScalePressure,Kernel.map_apply _ measurable_fst,
    Kernel.map_apply _ measurable_snd,hpair]

/-- The null-root positive normalization and exact scalar compensation leave
EVERY actual retained physical pressure unchanged, before samples or limits. -/
theorem originalRetainedSeedPhysicalPressure_positiveCompletion_eq
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z) (χ : ℕ → Kernel Z (ℝ × ℝ)) [∀ n z, IsFiniteMeasure (χ n z)]
    (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
    (η : ℕ → Z → ℝ) (b : Z × ℝ → M) (f : M × M →ᵇ ℝ)
    (hdim : 6 ≤ finrank ℝ E) (j n : ℕ) (t : ℝ) (z : Z) :
    originalRetainedSeedPhysicalPressure P a κ lambda
      (fun n ↦ originalPositiveRetainedPairKernel (χ n) γ)
      (fun n ↦ originalPositiveRetention (χ n) (η n)) b f j n t z =
      originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z := by
  have hq : 2 < (finrank ℝ (P j).seed.covector.ker : ℝ) := by
    have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    exact_mod_cast (show 2 < finrank ℝ (P j).seed.covector.ker by omega)
  have hexp : 1 - 2/(finrank ℝ (P j).seed.covector.ker : ℝ) ≠ 0 :=
    (sub_pos.mpr ((div_lt_one (by linarith only [hq])).mpr hq)).ne'
  by_cases hz : χ n z univ = 0
  · have hη : originalPositiveRetention (χ n) (η n) z = 1 := by
      simp only [originalPositiveRetention,hz,ite_true]
    have hm : (χ n z).real univ = 0 := by simp only [measureReal_def,hz,ENNReal.toReal_zero]
    simp only [originalRetainedSeedPhysicalPressure,originalRetainedNormalizedPressure,
      hη,hm,sub_self,zero_mul,mul_zero,Real.zero_rpow hexp]
  · have hk : originalPositiveRetainedPairKernel (χ n) γ z = χ n z := by
      simp only [originalPositiveRetainedPairKernel_apply,hz,ite_false]
    have hη : originalPositiveRetention (χ n) (η n) z = η n z := by
      simp only [originalPositiveRetention,hz,ite_false]
    have hp := originalSeedRetainedRootPressure_congr_at_root (P j).seed a
      (originalPositiveRetainedPairKernel (χ n) γ) (χ n) b f z hk
    simp only [originalRetainedSeedPhysicalPressure,originalRetainedNormalizedPressure,hk,hη,hp]

variable {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, (κ j).IsAddHaarMeasure]
  {lambda : Measure Z} {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
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
  (χ : ℕ → Kernel Z (ℝ × ℝ)) [∀ n z, IsFiniteMeasure (χ n z)]
  (hχ : ∀ᵐ z ∂lambda, ∀ n, χ n z ≤ γ z)
  (hmass : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ (χ n z).real univ) atTop (𝓝 1))
  {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ)
include hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ χ hχ hmass hb

/-- Arbitrary null stages of the original retained conditional laws are
allowed. Exact same weighted retained populations produce deterministic root
cutoffs, with no supplied positive-mass or loss-rate normalization hypothesis. -/
theorem eventually_exists_originalRetainedSeedPhysicalPressure_cutoff_of_mass_recovery
    [IsFiniteMeasure lambda]
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0) lambda)
    (η : ℕ → Z → ℝ) (hηM : ∀ n, Measurable (η n))
    (hη : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ η n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ η n z ∧ η n z ≤ 1)
    (j : ℕ) (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    ∀ᶠ n in atTop, ∃ K : Set Z, MeasurableSet K ∧
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)).real Kᶜ < budget ∧
      IntegrableOn (originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t) K
        (lambda.restrict (populationSeedRootPiece P a κ lambda j)) ∧
      (∫ z in K, originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z
        ∂lambda.restrict (populationSeedRootPiece P a κ lambda j)) <
      (∫ z, originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z
        ∂lambda.restrict (populationSeedRootPiece P a κ lambda j)) + tolerance := by
  let χ' := fun n ↦ originalPositiveRetainedPairKernel (χ n) γ
  let η' := fun n ↦ originalPositiveRetention (χ n) (η n)
  let δ' := fun n z ↦ 1 - (χ' n z).real univ
  have hlaw' := ae_originalPositiveRetainedPairKernel_lost_mass_law lambda χ γ hχ hmass
  have hχ' : ∀ᵐ z ∂lambda, ∀ n, χ' n z ≤ γ z := hlaw'.mono (fun _ h ↦ h.1)
  have hδ' : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ δ' n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ δ' n z ∧ δ' n z < 1 ∧ 1 - δ' n z ≤ (χ' n z).real univ :=
    hlaw'.mono (fun _ h ↦ h.2)
  have hη'M n : Measurable (η' n) := measurable_originalPositiveRetention (χ n) (hηM n)
  have hη' : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ η' n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ η' n z ∧ η' n z ≤ 1 := by
    filter_upwards [hmass,hη] with z hmassz hηz
    have heq := eventually_originalPositiveRetainedPairKernel_eq χ γ η z hmassz
    refine ⟨hηz.1.congr' (heq.mono fun n hn ↦ ?_),?_⟩
    · change η n z = originalPositiveRetention (χ n) (η n) z
      exact hn.2.symm
    · intro n
      change 0 ≤ originalPositiveRetention (χ n) (η n) z ∧
        originalPositiveRetention (χ n) (η n) z ≤ 1
      unfold originalPositiveRetention
      split_ifs
      · norm_num
      · exact hηz.2 n
  have hcut := eventually_exists_originalRetainedSeedPhysicalPressure_cutoff hlaw hF hcomplete
    hu ha hinj hdim hgap hsep γ hγ χ' hχ' δ' hδ' hb f hp0 η' hη'M hη'
    j t budget tolerance hbudget htolerance
  have heq n : originalRetainedSeedPhysicalPressure P a κ lambda χ' η' b f j n t =
      originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t := by
    funext z
    exact originalRetainedSeedPhysicalPressure_positiveCompletion_eq P a κ lambda χ γ η b f hdim j n t z
  simpa only [heq] using hcut

end OTSelector.Reconstruction
