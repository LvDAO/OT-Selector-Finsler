import OTSelector.Reconstruction.FinslerOriginalRetainedRootPressureMeasurability
import OTSelector.Reconstruction.FinslerOriginalPhysicalRootPressure
import OTSelector.Reconstruction.OriginalRetainedPressureNormalization
import OTSelector.MeasureTheory.RetainedLawVariation

/-! Actual retained original pressures are normalized against the unchanged
original root law, including its exact coordinate Haar Jacobian. -/
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

/-- The actual retained pressure per unchanged original root mass. Its density
is the exact original coordinate intensity times actual scalar retention and
actual original conditional retained-pair mass. -/
def originalRetainedSeedPhysicalPressure (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z) (χ : ℕ → Kernel Z (ℝ × ℝ)) [∀ n z, IsFiniteMeasure (χ n z)]
    (η : ℕ → Z → ℝ) (b : Z × ℝ → M) (f : M × M →ᵇ ℝ)
    (j n : ℕ) (t : ℝ) (z : Z) : ℝ :=
  let theta := originalSeedCoordinateIntensity P a κ lambda j z
  originalRetainedNormalizedPressure (finrank ℝ (P j).seed.covector.ker) theta
    (((1 - η n z) * theta) * (χ n z).real univ)
    (originalSeedRetainedRootPressure (P j).seed a (χ n) b f z) t

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
  (δ : ℕ → Z → ℝ)
  (hδ : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ δ n z) atTop (𝓝 0) ∧
    ∀ n, 0 ≤ δ n z ∧ δ n z < 1 ∧ 1 - δ n z ≤ (χ n z).real univ)
  {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ)
include hlaw hF hcomplete hu ha hinj hdim hgap hsep γ hγ χ hχ δ hδ hb

/-- Actual retained physical pressures have measurable original-root versions.
No measurable pressure/optimizer or coefficient continuity premise occurs. -/
theorem aestronglyMeasurable_originalRetainedSeedPhysicalPressure
    (η : ℕ → Z → ℝ) (hηM : ∀ n, Measurable (η n)) (j n : ℕ) (t : ℝ) :
    AEStronglyMeasurable (originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t)
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)) := by
  let q : ℝ := finrank ℝ (P j).seed.covector.ker
  have hq : 2 < q := by
    have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    dsimp only [q]
    exact_mod_cast (show 2 < finrank ℝ (P j).seed.covector.ker by omega)
  let theta := originalSeedCoordinateIntensity P a κ lambda j
  let density := fun z ↦ ((1 - η n z) * theta z) * (χ n z).real univ
  have hmtheta : Measurable theta := measurable_const.mul
    (measurable_actual_populationAtlasTheta hF hcomplete hu ha hinj j)
  have hmdensity : Measurable density :=
    ((measurable_const.sub (hηM n)).mul hmtheta).mul (measurable_originalRetainedPairMass (χ n))
  have hmweight : Measurable (fun z ↦ density z ^ (1 - 2/q)) :=
    (Real.continuous_rpow_const (sub_nonneg.mpr
      ((div_le_one (by linarith only [hq] : 0 < q)).mpr hq.le))).measurable.comp hmdensity
  have hmtilt : Measurable (fun z ↦ t * density z ^ (2/q)) :=
    measurable_const.mul ((Real.continuous_rpow_const
      (div_nonneg (by norm_num) (by linarith only [hq] : 0 ≤ q))).measurable.comp hmdensity)
  have hread := aestronglyMeasurable_actual_originalRetainedRootPressure hlaw hF hcomplete
    hu ha hinj hdim hgap hsep γ hγ χ hχ δ hδ hb f j n
    (fun z ↦ t * density z ^ (2/q)) hmtilt
  exact (hmtheta.inv.mul hmweight).aestronglyMeasurable.mul hread

/-- The true retained family has one common physical lower bound and recovers
the corrected canonical full original pressure upper on the same original root.
The actual conditional selections and their rates may vary with the root. -/
theorem ae_originalRetainedSeedPhysicalPressure_lower_upper
    (η : ℕ → Z → ℝ)
    (hη : ∀ᵐ z ∂lambda, Tendsto (fun n ↦ η n z) atTop (𝓝 0) ∧
      ∀ n, 0 ≤ η n z ∧ η n z ≤ 1) (j : ℕ) (t : ℝ) :
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      (∀ n, -(|t| * ‖f‖) ≤ originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z) ∧
      ∀ ε > 0, ∀ᶠ n in atTop,
        originalRetainedSeedPhysicalPressure P a κ lambda χ η b f j n t z <
          originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z + ε := by
  let q : ℝ := finrank ℝ (P j).seed.covector.ker
  have hqdim : q = ((finrank ℝ E - 1 : ℕ) : ℝ) := by
    have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    dsimp only [q]
    exact_mod_cast (show finrank ℝ (P j).seed.covector.ker = finrank ℝ E - 1 by omega)
  have hq : 2 < q := by rw [hqdim]; exact_mod_cast (by omega : 2 < finrank ℝ E - 1)
  filter_upwards [hlaw.ae_originalSeedRetainedRootPressure_limits hF hcomplete hu ha hinj
    hdim hgap hsep γ hγ χ hχ δ hδ hb f j,ae_restrict_of_ae hχ,ae_restrict_of_ae hδ,
    ae_restrict_of_ae hη,
    ae_restrict_mem (measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj j)]
    with z hz hχz hδz hηz hzpiece
  let theta := originalSeedCoordinateIntensity P a κ lambda j z
  let density := fun n ↦ ((1 - η n z) * theta) * (χ n z).real univ
  let p := fun n ↦ originalSeedRetainedRootPressure (P j).seed a (χ n) b f z
  let pref := originalSeedRootPressure (P j).seed a η₀ η₁ b f z
  have htheta : 0 ≤ theta := mul_nonneg
    (originalSeedCoordinateHaarFactor_pos (P j).seed (κ j)).le
    (populationAtlasTheta_nonneg P a κ lambda j z)
  have hmass1 n : (χ n z).real univ ≤ 1 := by
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one] using
      ENNReal.toReal_mono (measure_ne_top (γ z) univ) (hχz n univ)
  have hfactor0 n : 0 ≤ (1 - η n z) * (χ n z).real univ :=
    mul_nonneg (sub_nonneg.mpr (hηz.2 n).2) measureReal_nonneg
  have hfactor1 n : (1 - η n z) * (χ n z).real univ ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hmass1 n) (sub_nonneg.mpr (hηz.2 n).2)
    nlinarith only [hh,(hηz.2 n).1]
  have hdensity0 n : 0 ≤ density n := by
    change 0 ≤ ((1 - η n z) * theta) * (χ n z).real univ
    nlinarith only [htheta,hfactor0 n]
  have hdensityle n : density n ≤ theta := by
    change ((1 - η n z) * theta) * (χ n z).real univ ≤ theta
    nlinarith only [htheta,hfactor1 n]
  have hmasslim : Tendsto (fun n ↦ (χ n z).real univ) atTop (𝓝 1) :=
    tendsto_submeasure_mass_of_lost_mass (γ z) (fun n ↦ χ n z) atTop (fun n ↦ δ n z)
      hδz.1 (Filter.Eventually.of_forall fun n ↦ ⟨hχz n,(hδz.2 n).2.2⟩)
  have hdensitylim : Tendsto density atTop (𝓝 theta) := by
    have hconst : Tendsto (fun _n : ℕ ↦ (1:ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have hh := ((hconst.sub hηz.1).mul_const theta).mul hmasslim
    simpa only [sub_zero,one_mul,mul_one] using hh
  have hLip n : LipschitzWith ‖f‖₊ (p n) := (hz.1 n).2.1
  have hzero n : 0 ≤ p n 0 := by
    simpa only [abs_zero,zero_mul,neg_zero] using (hz.1 n).2.2 0
  have hupper := eventually_originalRetainedNormalizedPressure_lt atTop hq htheta p pref ‖f‖₊
    hLip hz.2 density hdensitylim hdensity0 t
  have hreference : originalPhysicalFinslerRootPressure P a κ lambda η₀ η₁ b f t z =
      theta ^ (-2/q) * pref (t * theta ^ (2/q)) := by
    have hh := originalPhysicalFinslerRootPressure_eq_coordinate_on_piece
      (η₀ := η₀) (η₁ := η₁) (b := b) f j t hzpiece
    rw [← hqdim] at hh
    exact hh
  refine ⟨?_,?_⟩
  · intro n
    exact originalRetainedNormalizedPressure_lower_bound hq htheta (hdensity0 n)
      (hdensityle n) (hLip n) (hzero n) t
  · intro ε hε
    filter_upwards [hupper ε hε] with n hn
    rw [hreference]
    exact hn

end OTSelector.Reconstruction
