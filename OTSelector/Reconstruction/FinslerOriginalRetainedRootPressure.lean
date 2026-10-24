import OTSelector.Probability.NormalizedRetainedPairKernel
import OTSelector.Reconstruction.FinslerOriginalRootPressureMeasurability
import OTSelector.Reconstruction.OriginalFocalWindowPressureUpper

/-! Actual retained original conditional laws have canonical root pressures.
Their measurable kernel normalization retains the original clocks and coefficient. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual retained original finite pressure uses both marginals of the
SAME normalized original retained pair kernel, with literal original legality. -/
def originalSeedRetainedScalePressure (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (χ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] (b : Z × ℝ → M) (f : M × M →ᵇ ℝ)
    (R t : ℝ) (z : Z) : ℝ :=
  legalMarkedScalePressure (finrank ℝ S.covector.ker) id id
    ((originalNormalizedRetainedPairKernel χ).map Prod.fst z)
    ((originalNormalizedRetainedPairKernel χ).map Prod.snd z)
    (originalSeedRootKinetic S a z) (originalPhysicalRootProbe b f z) R t

/-- Canonical actual retained pressure, before any pressure or optimizer is selected. -/
def originalSeedRetainedRootPressure (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (χ : Kernel Z (ℝ × ℝ)) [∀ z, IsFiniteMeasure (χ z)] (b : Z × ℝ → M) (f : M × M →ᵇ ℝ)
    (z : Z) (t : ℝ) : ℝ :=
  limUnder atTop (fun R : ℝ ↦ originalSeedRetainedScalePressure S a χ b f R t z)

/-- The actual original moment/separation laws give true retained pressure
limits, a common physical lower/Lipschitz bound, and upper recovery of the
unchanged full original pressure. Conditional selections may vary with stage. -/
theorem PopulationSeedPieceMomentLaw.ae_originalSeedRetainedRootPressure_limits
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
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
    (δ : ℕ → Z → ℝ)
    (hδ : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ δ n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ δ n z ∧ δ n z < 1 ∧ 1 - δ n z ≤ (χ n z).real univ)
    {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ) (j : ℕ) :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      (∀ n, (∀ t, Tendsto (fun R : ℝ ↦
        originalSeedRetainedScalePressure (P j).seed a (χ n) b f R t z)
        atTop (𝓝 (originalSeedRetainedRootPressure (P j).seed a (χ n) b f z t))) ∧
        LipschitzWith ‖f‖₊ (originalSeedRetainedRootPressure (P j).seed a (χ n) b f z) ∧
        ∀ t, -(|t| * ‖f‖) ≤ originalSeedRetainedRootPressure (P j).seed a (χ n) b f z t) ∧
      ∀ t ε, 0 < ε → ∀ᶠ n in atTop,
        originalSeedRetainedRootPressure (P j).seed a (χ n) b f z t <
          originalSeedRootPressure (P j).seed a η₀ η₁ b f z t + ε := by
  filter_upwards [ae_restrict_of_ae hlaw,ae_restrict_of_ae hsep,ae_restrict_of_ae hγ,
    ae_restrict_of_ae hχ,ae_restrict_of_ae hδ,
    ae_restrict_mem (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)]
    with z hz hsz hγz hχz hδz hzpiece
  let w := populationSeedPieceLabel P a κ lambda j ⟨z,hzpiece⟩
  obtain ⟨D⟩ := hz j hzpiece
  let S := (P j).seed
  let g := originalPhysicalRootProbe b f z
  have hg : Measurable (uncurry g) :=
    (measurable_originalPhysicalRootProbe hcomplete hb f).comp measurable_prodMk_left
  have hgb x y : |g x y| ≤ ‖f‖ := f.norm_coe_le_norm (b (z,x),b (z,y))
  have hq : 4 < finrank ℝ S.covector.ker := by
    have h := S.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    omega
  obtain ⟨πret,hπret,pref,p,href,hpt,hLipref,hLip,hupper⟩ :=
    D.exists_original_retained_pressure_upper hF w.property hq hgap hsz
      (γ z) hγz.1 hγz.2 (fun n ↦ χ n z) hχz (fun n ↦ δ n z)
      hδz.1 (fun n ↦ (hδz.2 n).1) (fun n ↦ (hδz.2 n).2.1)
      (fun n ↦ (hδz.2 n).2.2) (norm_nonneg f) g hg hgb
  have hkin : originalSeedRootKinetic S a z =
      fun x y v ↦ matrixQuadratic (originalSeedPairCoefficient S w (x,y)) v := by
    funext x y v
    exact congrArg (fun A ↦ matrixQuadratic A v)
      (populationSeedRootCoefficient_eq_pieceCoefficient P a κ lambda hF hcomplete hu ha hinj
        j hzpiece (x,y))
  have hmass n : 0 < (χ n z).real univ := lt_of_lt_of_le
    (sub_pos.mpr (hδz.2 n).2.1) (hδz.2 n).2.2
  have hα n : (originalNormalizedRetainedPairKernel (χ n)).map Prod.fst z =
      ((πret n).map measurable_fst.aemeasurable : Measure ℝ) := by
    rw [Kernel.map_apply _ measurable_fst,originalNormalizedRetainedPairKernel_apply_eq _ z (hmass n)]
    simp only [ProbabilityMeasure.toMeasure_map,hπret n]
  have hβ n : (originalNormalizedRetainedPairKernel (χ n)).map Prod.snd z =
      ((πret n).map measurable_snd.aemeasurable : Measure ℝ) := by
    rw [Kernel.map_apply _ measurable_snd,originalNormalizedRetainedPairKernel_apply_eq _ z (hmass n)]
    simp only [ProbabilityMeasure.toMeasure_map,hπret n]
  have hscale n R t : originalSeedRetainedScalePressure S a (χ n) b f R t z =
      legalMarkedScalePressure (finrank ℝ S.covector.ker) id id
        ((πret n).map measurable_fst.aemeasurable : Measure ℝ)
        ((πret n).map measurable_snd.aemeasurable : Measure ℝ)
        (fun x y v ↦ matrixQuadratic (originalSeedPairCoefficient S w (x,y)) v) g R t := by
    simp only [originalSeedRetainedScalePressure,hα,hβ,hkin,g]
  have hlim n t : Tendsto (fun R : ℝ ↦ originalSeedRetainedScalePressure S a (χ n) b f R t z)
      atTop (𝓝 (p n t)) := (hpt n t).congr'
    (Filter.Eventually.of_forall fun R ↦ (hscale n R t).symm)
  have heq n t : originalSeedRetainedRootPressure S a (χ n) b f z t = p n t :=
    (hlim n t).limUnder_eq
  have hfull t : Tendsto (fun R : ℝ ↦ originalSeedRootScalePressure S a η₀ η₁ b f R t z)
      atTop (𝓝 (pref t)) := by
    apply (href t).congr'
    filter_upwards [] with R
    simp only [originalSeedRootScalePressure,hkin,g]
    rfl
  have hfullEq t : originalSeedRootPressure S a η₀ η₁ b f z t = pref t :=
    (hfull t).limUnder_eq
  have hac n : (πret n : Measure (ℝ × ℝ)) ≪ γ z := by
    rw [hπret n]
    exact (Measure.absolutelyContinuous_of_le (hχz n)).smul_left _
  have hαac n : ((πret n).map measurable_fst.aemeasurable : Measure ℝ) ≪
      condDistrib u a η₀ z := by
    rw [← hγz.1.1]
    exact (hac n).map measurable_fst
  have hβac n : ((πret n).map measurable_snd.aemeasurable : Measure ℝ) ≪
      condDistrib u a η₁ z := by
    rw [← hγz.1.2]
    exact (hac n).map measurable_snd
  obtain ⟨C,hC,hkb⟩ := D.exists_originalFocalKinetic_quadratic_bound hF w.property hgap hsz
  have hzero n : 0 ≤ p n 0 := by
    apply ge_of_tendsto (hpt n 0)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    rw [← D.original_focal_scalePressure_eq_actual_coefficient hsz
      ((πret n).map measurable_fst.aemeasurable : Measure ℝ)
      ((πret n).map measurable_snd.aemeasurable : Measure ℝ) (hαac n) (hβac n) g R 0]
    simpa only [abs_zero,zero_mul,neg_zero] using legalMarkedScalePressure_lower_bound
      (finrank ℝ S.covector.ker) measurable_id measurable_id
      ((πret n).map measurable_fst.aemeasurable : Measure ℝ)
      ((πret n).map measurable_snd.aemeasurable : Measure ℝ) hC (norm_nonneg f)
      (D.measurable_originalFocalKinetic hF w.property gap)
      (D.originalFocalKinetic_nonneg hF w.property hgap) hkb hg hgb 0 hR
  refine ⟨?_,?_⟩
  · intro n
    refine ⟨?_,?_,?_⟩
    · intro t
      change Tendsto _ atTop (𝓝 (originalSeedRetainedRootPressure S a (χ n) b f z t))
      rw [heq]
      exact hlim n t
    · have hh : originalSeedRetainedRootPressure S a (χ n) b f z = p n := funext (heq n)
      rw [hh]
      exact hLip n
    · intro t
      rw [heq]
      have hh := (hLip n).dist_le_mul t 0
      simp only [Real.dist_eq,sub_zero] at hh
      change |p n t - p n 0| ≤ ‖f‖ * |t| at hh
      nlinarith only [(abs_le.mp hh).1,hzero n]
  · intro t ε hε
    filter_upwards [hupper t ε hε] with n hn
    change originalSeedRetainedRootPressure S a (χ n) b f z t <
      originalSeedRootPressure S a η₀ η₁ b f z t + ε
    rw [heq,hfullEq]
    exact hn

end OTSelector.Reconstruction
