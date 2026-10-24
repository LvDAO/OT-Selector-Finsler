import OTSelector.Reconstruction.OriginalHaarPressureScaling
import OTSelector.Reconstruction.FinslerOriginalRootPressureMeasurability
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedSourceHaarReference

/-! The actual native seed Haar Jacobian converts literal coordinate-unit
pressure to the native-Haar pressure used by the original population atlas. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open MeasureTheory.Measure
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The exact positive Haar-to-standard-coordinate Jacobian of the same finite
basis used in the literal original inverse-compliance pressure. -/
def originalSeedCoordinateHaarFactor (S : F.CalibratedLevelSeedPatch u)
    (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure] : ℝ≥0 :=
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  letI : (κ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map κ
  addHaarScalarFactor (κ.map e) (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))

/-- The Jacobian is internally positive; it is not an imposed normalization. -/
theorem originalSeedCoordinateHaarFactor_pos (S : F.CalibratedLevelSeedPatch u)
    (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure] :
    0 < originalSeedCoordinateHaarFactor S κ := by
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  letI : (κ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map κ
  exact addHaarScalarFactor_pos_of_isAddHaarMeasure _ _

/-- Exact native seed Haar measure in the SAME original finite basis. -/
theorem map_originalSeedHaar_eq_coordinate_volume (S : F.CalibratedLevelSeedPatch u)
    (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure] :
    κ.map (Module.finBasis ℝ S.covector.ker).equivFunL =
      (originalSeedCoordinateHaarFactor S κ : ℝ≥0∞) •
        (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)) := by
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  letI : (κ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map κ
  change κ.map e =
    (addHaarScalarFactor (κ.map e)
      (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)) : ℝ≥0∞) •
      (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))
  simpa only [Measure.coe_nnreal_smul] using isAddLeftInvariant_eq_smul (κ.map e)
    (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))

/-- Any actual Haar factor exposed by an original finite-cloud factory is
exactly the canonical factor, provided its genuine pushforward identity is kept. -/
theorem originalSeedCoordinateHaarFactor_eq_of_map
    (S : F.CalibratedLevelSeedPatch u) (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure]
    (c : ℝ≥0)
    (hmap : κ.map (Module.finBasis ℝ S.covector.ker).equivFunL =
      (c : ℝ≥0∞) • (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) :
    originalSeedCoordinateHaarFactor S κ = c := by
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  letI : (κ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map κ
  have hm : κ.map e = c • (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)) := by
    simpa only [Measure.coe_nnreal_smul] using hmap
  change addHaarScalarFactor (κ.map e)
    (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)) = c
  simp only [hm,addHaarScalarFactor_smul,addHaarScalarFactor_self,smul_eq_mul,mul_one]

/-- Native-Haar unit pressure of the actual original coefficient. The positive
actual Haar Jacobian rescales both its kinetic value and physical probe tilt. -/
def originalSeedHaarPressure (S : F.CalibratedLevelSeedPatch u) (a : M → Z)
    (κ : Measure S.covector.ker) [κ.IsAddHaarMeasure]
    (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (z : Z) : ℝ → ℝ :=
  haarUnitPressure (finrank ℝ S.covector.ker) (originalSeedCoordinateHaarFactor S κ)
    (originalSeedRootPressure S a η₀ η₁ b f z)

/-- The actual density for standard-coordinate original Poisson cubes is the
native-Haar population density multiplied by the exact original Haar Jacobian. -/
def originalSeedCoordinateIntensity (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z) (j : ℕ) (z : Z) : ℝ :=
  originalSeedCoordinateHaarFactor (P j).seed (κ j) * populationAtlasTheta P a κ lambda j z

/-- The corrected native-Haar atlas expression equals the existing physical
original finite-cube convention with Theta=cHaar*theta, pointwise. -/
theorem populationAtlasIntegrand_originalSeedHaarPressure_eq_coordinate
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) [∀ j, (κ j).IsAddHaarMeasure]
    (lambda : Measure Z) (η₀ η₁ : Measure M) [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    (b : Z × ℝ → M) (f : M × M →ᵇ ℝ) (j : ℕ) (t : ℝ) (z : Z) :
    populationAtlasIntegrand P a κ lambda
      (originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f) j
      (finrank ℝ (P j).seed.covector.ker) t z =
      originalSeedCoordinateIntensity P a κ lambda j z ^
        (-2/(finrank ℝ (P j).seed.covector.ker : ℝ)) *
        originalSeedRootPressure (P j).seed a η₀ η₁ b f z
          (t * originalSeedCoordinateIntensity P a κ lambda j z ^
            (2/(finrank ℝ (P j).seed.covector.ker : ℝ))) :=
  normalized_haarUnitPressure_eq_coordinate (originalSeedCoordinateHaarFactor_pos (P j).seed (κ j)).le
    (populationAtlasTheta_nonneg P a κ lambda j z) _ t

/-- The corrected native-Haar pressure has measurable original population
normalization, the original physical lower bound and common probe Lipschitz.
All actual coordinate intensities include the genuine cHaar Jacobian. -/
theorem actual_originalHaarPressure_normalized_measurable_lower
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
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
    {b : Z × ℝ → M} (hb : Measurable b) (f : M × M →ᵇ ℝ) (j : ℕ) (t : ℝ) :
    let q : ℝ := finrank ℝ (P j).seed.covector.ker
    let I := originalSeedHaarPressure (P j).seed a (κ j) η₀ η₁ b f
    AEStronglyMeasurable (populationAtlasIntegrand P a κ lambda I j q t)
      (lambda.restrict (populationSeedRootPiece P a κ lambda j)) ∧
    ∀ᵐ z ∂lambda.restrict (populationSeedRootPiece P a κ lambda j),
      LipschitzWith ‖f‖₊ (fun s ↦ populationAtlasIntegrand P a κ lambda I j q s z) ∧
      -(|t| * ‖f‖) ≤ populationAtlasIntegrand P a κ lambda I j q t z := by
  let q : ℝ := finrank ℝ (P j).seed.covector.ker
  let Θ := originalSeedCoordinateIntensity P a κ lambda j
  have hq : 0 < q := by
    have h := (P j).seed.normalization.toLinearEquiv.finrank_eq
    simp only [Module.finrank_prod,Module.finrank_self] at h
    dsimp only [q]
    exact_mod_cast (show 0 < finrank ℝ (P j).seed.covector.ker by omega)
  have hΘ z : 0 ≤ Θ z := mul_nonneg (NNReal.coe_nonneg _)
    (populationAtlasTheta_nonneg P a κ lambda j z)
  have hmΘ : Measurable Θ :=
    (measurable_actual_populationAtlasTheta hF hcomplete hu ha hinj j).const_mul _
  have hpow : Measurable (fun z ↦ Θ z ^ (2/q)) :=
    (Real.continuous_rpow_const (div_nonneg (by norm_num) hq.le)).measurable.comp hmΘ
  have hnegpow : Measurable (fun z ↦ Θ z ^ (-2/q)) := by
    convert hpow.inv using 1
    funext z
    change Θ z ^ (-2/q) = (Θ z ^ (2/q))⁻¹
    rw [show (-2/q : ℝ) = -(2/q) by ring]
    exact Real.rpow_neg (hΘ z) (2/q)
  have hread := aestronglyMeasurable_actual_originalRootPressure hlaw hF hcomplete hu ha hinj
    hdim hgap hsep γ hγ hb f j (fun z ↦ t * Θ z ^ (2/q)) (hpow.const_mul t)
  have heq s z := populationAtlasIntegrand_originalSeedHaarPressure_eq_coordinate
    P a κ lambda η₀ η₁ b f j s z
  refine ⟨?_,?_⟩
  · apply (hnegpow.aestronglyMeasurable.mul hread).congr
    exact .of_forall (fun z ↦ (heq t z).symm)
  · filter_upwards [hlaw.ae_originalSeedRootPressure_limits hF hcomplete hu ha hinj hdim hgap hsep
      γ hγ hb f j] with z hz
    have hzero : 0 ≤ originalSeedRootPressure (P j).seed a η₀ η₁ b f z 0 := by
      simpa only [abs_zero,zero_mul,neg_zero] using hz.2.2 0
    refine ⟨?_,?_⟩
    · have hfun := funext (fun s ↦ heq s z)
      rw [hfun]
      exact lipschitz_normalized_pressure (hΘ z) hq hz.2.1
    · rw [heq]
      exact normalized_pressure_lower_bound (hΘ z) hq hz.2.1 hzero t

end OTSelector.Reconstruction
