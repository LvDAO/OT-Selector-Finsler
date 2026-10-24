import OTSelector.Reconstruction.FinslerOriginalRetainedPressureNullRoots
import OTSelector.MeasureTheory.Integral.DisjointPieceGluing

/-! One actual retained pressure on the unchanged original root law controls
the entire countable atlas by one deterministic original-root cutoff. -/
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

/-- The canonical retained physical pressure on the complete original root.
Every selected seed uses its own exact coordinate intensity Theta=cHaar*theta. -/
def originalRetainedFinslerRootPressure (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z) (χ : ℕ → Kernel Z (ℝ × ℝ)) [∀ n z, IsFiniteMeasure (χ n z)]
    (η : ℕ → Z → ℝ) (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (n : ℕ) (t : ℝ) : Z → ℝ :=
  disjointRootPressure (populationSeedRootPiece P a κ lambda)
    (fun j ↦ originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t)

/-- Every original selected seed piece reads exactly its actual retained pressure. -/
theorem originalRetainedFinslerRootPressure_eq_on_piece
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z) (χ : ℕ → Kernel Z (ℝ × ℝ)) [∀ n z, IsFiniteMeasure (χ n z)]
    (η : ℕ → Z → ℝ) (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (n j : ℕ) (t : ℝ) {z : Z}
    (hz : z ∈ populationSeedRootPiece P a κ lambda j) :
    originalRetainedFinslerRootPressure P a κ lambda χ η b f n t z =
      originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z :=
  disjointRootPressure_eq_on_piece _ (pairwiseDisjoint_populationSeedRootPiece P a κ lambda) _ j hz

/-- An original null conditional retained law contributes exactly zero pressure,
including outside an actual finite original coefficient core at a finite stage. -/
theorem originalRetainedFinslerRootPressure_eq_zero_of_kernel_eq_zero
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z) (χ : ℕ → Kernel Z (ℝ × ℝ)) [∀ n z, IsFiniteMeasure (χ n z)]
    (η : ℕ → Z → ℝ) (b : Z × ℝ → M) (f : M × M →ᵇ ℝ)
    (hdim : 6 ≤ finrank ℝ E) (n : ℕ) (t : ℝ) (z : Z) (hχ : χ n z = 0) :
    originalRetainedFinslerRootPressure P a κ lambda χ η b f n t z = 0 := by
  have hterm j : originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z = 0 := by
    have hq : 2 < (finrank ℝ (P j).seed.covector.ker : ℝ) := by
      have hh := (P j).seed.normalization.toLinearEquiv.finrank_eq
      simp only [Module.finrank_prod,Module.finrank_self] at hh
      exact_mod_cast (show 2 < finrank ℝ (P j).seed.covector.ker by omega)
    have hexp : 1 - 2/(finrank ℝ (P j).seed.covector.ker : ℝ) ≠ 0 :=
      (sub_pos.mpr ((div_lt_one (by linarith only [hq])).mpr hq)).ne'
    simp only [originalRetainedSeedPhysicalPressure,originalRetainedNormalizedPressure,
      hχ,measureReal_zero_apply,mul_zero,Real.zero_rpow hexp,zero_mul]
  have hind j : (populationSeedRootPiece P a κ lambda j).indicator
      (originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t) z = 0 := by
    by_cases hz : z ∈ populationSeedRootPiece P a κ lambda j
    · rw [indicator_of_mem hz,hterm]
    · exact indicator_of_notMem hz _
  simp only [originalRetainedFinslerRootPressure,disjointRootPressure,hind,tsum_zero]

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

/-- The SAME original retained kernels internally produce one globally AE
measurable physical pressure, a common physical lower bound, and its upper
recovery of the corrected original pressure, on the full countable atlas. -/
theorem originalRetainedFinslerRootPressure_measurable_lower_upper
    (η : ℕ → Z → ℝ) (hηM : ∀ n, Measurable (η n))
    (hη : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ η n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ η n z ∧ η n z ≤ 1) (t : ℝ) :
    (∀ n, AEStronglyMeasurable (originalRetainedFinslerRootPressure P a κ lambda χ η b f n t) lambda) ∧
    ∀ᵐ z ∂lambda,
      (∀ n, -(|t| * ‖f‖) ≤ originalRetainedFinslerRootPressure P a κ lambda χ η b f n t z) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        originalRetainedFinslerRootPressure P a κ lambda χ η b f n t z <
          originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z + ε := by
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
  have heq j n : originalRetainedSeedPhysicalPressure P a κ lambda χ' η' b f j n t =
      originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t := by
    funext z
    exact originalRetainedSeedPhysicalPressure_positiveCompletion_eq P a κ lambda χ γ η b f hdim j n t z
  have hmeas j n : AEStronglyMeasurable
      (originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t)
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)) := by
    have hh := aestronglyMeasurable_originalRetainedSeedPhysicalPressure hlaw hF hcomplete hu
      ha hinj hdim hgap hsep γ hγ χ' hχ' δ' hδ' hb f η' hη'M j n t
    rwa [heq] at hh
  have hpiece j : ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      (∀ n, -(|t| * ‖f‖) ≤ originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z <
          originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z + ε := by
    simpa only [heq] using ae_originalRetainedSeedPhysicalPressure_lower_upper hlaw hF hcomplete
      hu ha hinj hdim hgap hsep γ hγ χ' hχ' δ' hδ' hb f η' hη' j t
  refine ⟨fun n ↦ aestronglyMeasurable_disjointRootPressure lambda _
    (fun j ↦ measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)
    (pairwiseDisjoint_populationSeedRootPiece P a κ lambda) _ (fun j ↦ hmeas j n),?_⟩
  filter_upwards [ae_all_iff.mpr (fun j ↦ ae_imp_of_ae_restrict (hpiece j))] with z hz
  by_cases hactive : ∃ j, z ∈ populationSeedRootPiece P a κ lambda j
  · obtain ⟨j,hj⟩ := hactive
    have hvalue n := originalRetainedFinslerRootPressure_eq_on_piece P a κ lambda χ η b f n j t hj
    refine ⟨?_,?_⟩
    · intro n
      rw [hvalue n]
      exact (hz j hj).1 n
    · intro ε hε
      filter_upwards [(hz j hj).2 ε hε] with n hn
      rw [hvalue n]
      exact hn
  · have hnot : z ∉ ⋃ j, populationSeedRootPiece P a κ lambda j := by
      simpa only [mem_iUnion,not_exists] using hactive
    have hret n : originalRetainedFinslerRootPressure P a κ lambda χ η b f n t z = 0 :=
      disjointRootPressure_eq_zero_of_notMem _ _ hnot
    have hfull : originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z = 0 :=
      disjointRootPressure_eq_zero_of_notMem _ _ hnot
    refine ⟨?_,?_⟩
    · intro n
      rw [hret n]
      exact neg_nonpos.mpr (mul_nonneg (abs_nonneg t) (norm_nonneg f))
    · intro ε hε
      filter_upwards [] with n
      rw [hret n,hfull,zero_add]
      exact hε

/-- One deterministic original-root cutoff controls the complete atlas at
once. Actual retained pressure measurability/lower/upper are derived internally;
only genuine corrected physical p0 integrability is the global middle input. -/
theorem eventually_exists_originalRetainedFinslerRootPressure_global_cutoff
    [IsFiniteMeasure lambda]
    (hp0 : Integrable (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f 0) lambda)
    (η : ℕ → Z → ℝ) (hηM : ∀ n, Measurable (η n))
    (hη : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ η n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ η n z ∧ η n z ≤ 1)
    (t budget tolerance : ℝ) (hbudget : 0 < budget) (htolerance : 0 < tolerance) :
    ∀ᶠ n in atTop, ∃ K : Set Z, MeasurableSet K ∧ lambda.real Kᶜ < budget ∧
      IntegrableOn (originalRetainedFinslerRootPressure P a κ lambda χ η b f n t) K lambda ∧
      (∫ z in K, originalRetainedFinslerRootPressure P a κ lambda χ η b f n t z ∂lambda) <
      (∫ z, originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z ∂lambda) + tolerance := by
  have hactual := originalRetainedFinslerRootPressure_measurable_lower_upper hlaw hF hcomplete
    hu ha hinj hdim hgap hsep γ hγ χ hχ hmass hb f η hηM hη t
  have hphysical := integrable_originalPhysicalFinslerRootPressure_of_zero f hlaw hF hcomplete
    hu ha hinj hdim hgap hsep γ hγ hb hp0 t
  exact exists_original_pressure_cutoff_integral_upper_ae lambda
    (fun n ↦ originalRetainedFinslerRootPressure P a κ lambda χ η b f n t)
    (originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t) hactual.1 hphysical.1
    (mul_nonneg (abs_nonneg t) (norm_nonneg f))
    (fun n ↦ hactual.2.mono (fun _ h ↦ h.1 n)) (hactual.2.mono (fun _ h ↦ h.2))
    budget tolerance hbudget htolerance

end OTSelector.Reconstruction
