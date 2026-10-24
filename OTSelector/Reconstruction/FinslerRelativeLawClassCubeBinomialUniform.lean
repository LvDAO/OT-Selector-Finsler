import OTSelector.Reconstruction.FinslerRelativeLawClassCubePhysicalBinomial
import OTSelector.Reconstruction.FinslerRelativeLawBinomialLegalTilt

/-! Uniform compact-tilt de-Poissonization of actual original finite class microcubes. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators
  BoundedContinuousFunction Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

/-- The actual full-cube binomial mean is bounded by the fixed microscopic
volume at every original sample size, including N=0. -/
theorem microscopicCubeProbability_mean_le {q : ℕ} (hq : 0 < q)
    (density : ℝ≥0) {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (N : ℝ) * (microscopicCubeProbability q density L N : ℝ) ≤ (density : ℝ) * L ^ q := by
  by_cases hN : N = 0
  · subst N
    simp only [Nat.cast_zero, zero_mul]
    positivity
  · have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    calc
      _ ≤ (N : ℝ) * ((density : ℝ) * microscopicGridSide q L N ^ q) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg N)
      _ = (density : ℝ) * ((N : ℝ) * microscopicGridSide q L N ^ q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (microscopicGrid_mass_le hq hL hNpos) density.coe_nonneg

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- The literal actual C/P0 full-cube means converge uniformly on every compact
tilt set. The common modulus comes from the true original binomial mean. -/
theorem OriginalPopulationCoefficientCore.tendstoUniformlyOn_clockClass_fullCube_binomial
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker)
    (density : ℝ≥0) (hdensity : 0 < density) {L : ℝ} (hL : 0 < L)
    {T : Set ℝ} (hT : IsCompact T) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
      ∫ cloud : TwoMarkedCloudSpace q (Fin Q.count) (Fin Q.count),
        finiteClassLegalTilted q (C.clockClassAllowed Q) 1
          (fun j k v ↦ (N : ℝ) ^ (2 / (q : ℝ)) * microscopicGridSide q L N ^ 2 *
            C.clockClassKinetic Q z₀ j k v) (C.clockClassProbe Q z₀ hz₀ f) tilt cloud
        ∂twoMarkedCountLaw q (α : Measure _) (β : Measure _)
          (ProbabilityTheory.binomial N (microscopicCubeProbability q density L N)))
      (fun tilt ↦ finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
        (density * ⟨L ^ q, pow_nonneg hL.le q⟩)
        (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt) atTop T := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  let V := fun N : ℕ ↦ fun tilt : ℝ ↦
    ∫ cloud : TwoMarkedCloudSpace q (Fin Q.count) (Fin Q.count),
      finiteClassLegalTilted q (C.clockClassAllowed Q) 1
        (fun j k v ↦ (N : ℝ) ^ (2 / (q : ℝ)) * microscopicGridSide q L N ^ 2 *
          C.clockClassKinetic Q z₀ j k v) (C.clockClassProbe Q z₀ hz₀ f) tilt cloud
      ∂twoMarkedCountLaw q (α : Measure _) (β : Measure _)
        (ProbabilityTheory.binomial N (microscopicCubeProbability q density L N))
  obtain ⟨source, target, hcode, _⟩ := C.exists_clockClass_strict_clocks Q
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  let A := (density : ℝ) * L ^ q * ‖f‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hlip (N : ℕ) : LipschitzWith ⟨A, hA⟩ (V N) := by
    apply LipschitzWith.of_dist_le_mul
    intro t u
    let pref := (N : ℝ) ^ (2 / (q : ℝ)) * microscopicGridSide q L N ^ 2
    have hpref : 0 ≤ pref := by dsimp [pref]; positivity
    have hki : ∀ j k v, |pref * C.clockClassKinetic Q z₀ j k v| ≤ (pref * K) * ∑ l, v l ^ 2 := by
      intro j k v
      rw [abs_mul, abs_of_nonneg hpref]
      exact (mul_le_mul_of_nonneg_left (hbound j k v) hpref).trans_eq (by ring)
    have hb := abs_integral_legalMarkedTilted_binomial_tilt_sub_le
      (kin := fun j k v ↦ pref * C.clockClassKinetic Q z₀ j k v)
      (probe := C.clockClassProbe Q z₀ hz₀ f) q
      (measurable_of_countable source) (measurable_of_countable target)
      (α : Measure _) (β : Measure _) N (microscopicCubeProbability q density L N)
      (by norm_num : (0:ℝ) ≤ 1) (mul_nonneg hpref hK) (norm_nonneg f)
      ((C.measurable_clockClassKinetic Q z₀).const_mul pref) hki
      (C.measurable_clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f) t u
    have hV (s : ℝ) : V N s = ∫ cloud, legalMarkedTilted q source target 1
        (fun j k v ↦ pref * C.clockClassKinetic Q z₀ j k v) (C.clockClassProbe Q z₀ hz₀ f) s cloud
        ∂twoMarkedCountLaw q (α : Measure _) (β : Measure _)
          (ProbabilityTheory.binomial N (microscopicCubeProbability q density L N)) := by
      apply integral_congr_ae
      filter_upwards [] with cloud
      exact finiteClassLegalTilted_eq_clock q _ source target hcode _ _ _ _ cloud
    rw [Real.dist_eq, hV t, hV u]
    exact hb.trans ((mul_le_mul_of_nonneg_right (microscopicCubeProbability_mean_le hq density hL N)
      (mul_nonneg (norm_nonneg f) (abs_nonneg _))).trans_eq (by
        simp only [Real.dist_eq]
        change (density : ℝ) * L ^ q * (‖f‖ * |t - u|) = A * |t - u|
        dsimp only [A]
        ring))
  let : CompactSpace T := isCompact_iff_compactSpace.mp hT
  let W : ℕ → T → ℝ := fun N t ↦ V N t
  have hlipT (N : ℕ) : LipschitzWith ⟨A, hA⟩ (W N) := by
    simpa only [mul_one, Function.comp_def, W] using (hlip N).comp (LipschitzWith.subtype_val T)
  have hequi : Equicontinuous W :=
    (LipschitzWith.uniformEquicontinuous W ⟨A, hA⟩ hlipT).equicontinuous
  have hpoint : Tendsto W atTop (𝓝 (fun t : T ↦
      finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
        (density * ⟨L ^ q, pow_nonneg hL.le q⟩)
        (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) t)) :=
    tendsto_pi_nhds.mpr (fun t ↦ C.tendsto_clockClass_fullCube_binomial Q z₀ hz₀ f P₀ hP₀ hmass
      hq density hdensity hL t)
  have hunif := (hequi.tendsto_uniformFun_iff_pi atTop _).mpr hpoint
  apply tendstoUniformlyOn_iff_restrict.mpr
  exact UniformFun.tendsto_iff_tendstoUniformly.mp hunif


/-- The same compact-tilt limit holds for the original untruncated affine finite
prefix value, uniformly for any prescribed sequence of microbox origins. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_fullCube_binomial_physical_uniform
    (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)
    {range : Set ℝ} {width : ℝ} (Q : FiniteScalarBins range width)
    (z₀ : Z) (hz₀ : z₀ ∈ C.roots) (f : M × M →ᵇ ℝ)
    (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmass : 0 < ∑ j, ∑ k, P₀ j k)
    (hq : 0 < Module.finrank ℝ (P C.seedIndex).seed.covector.ker) :
    let π := clockClassJointProbability P₀ hP₀ hmass
    let α := π.map measurable_fst.aemeasurable
    let β := π.map measurable_snd.aemeasurable
    let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
    ∃ source target : Fin Q.count → ℝ,
      (∀ j k, C.clockClassAllowed Q j k ↔ source j < target k) ∧
      ∀ (density : ℝ≥0) (_hdensity : 0 < density) (L : ℝ) (hL : 0 < L),
      ∀ (origin : ℕ → Fin q → ℝ) (T : Set ℝ), IsCompact T →
      TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
        affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
          (microscopicCubeProbability q density L N) (microscopicGridSide q L N) (origin N)
          (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt)
        (fun tilt ↦ finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
          (density * ⟨L ^ q, pow_nonneg hL.le q⟩)
          (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt) atTop T := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, _⟩ := C.exists_clockClass_strict_clocks Q
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  refine ⟨source, target, hcode, ?_⟩
  intro density hdensity L hL origin T hT
  have hlim := C.tendstoUniformlyOn_clockClass_fullCube_binomial Q z₀ hz₀ f P₀ hP₀ hmass
    hq density hdensity hL hT
  apply hlim.congr
  filter_upwards [] with N
  intro tilt _
  have hfinite := affineBinomialBlock_integrable_integral
    (kin := C.clockClassKinetic Q z₀) (probe := C.clockClassProbe Q z₀ hz₀ f)
    q hq (measurable_of_countable source) (measurable_of_countable target)
    (α : Measure _) (β : Measure _) N (microscopicCubeProbability q density L N)
    (microscopicGridSide_nonneg q L N) (origin N) hK (norm_nonneg f)
    (C.measurable_clockClassKinetic Q z₀) hbound
    (fun j k c _ v ↦ C.clockClassKinetic_homogeneous Q z₀ j k c v)
    (C.measurable_clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f) tilt
  exact (hfinite.2.trans (integral_congr_ae (.of_forall fun cloud ↦
    (finiteClassLegalTilted_eq_clock q _ source target hcode _ _ _ _ cloud).symm))).symm

end OTSelector.Reconstruction
