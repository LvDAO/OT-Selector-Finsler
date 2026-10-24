import OTSelector.Reconstruction.FinslerRelativeLawPositiveMicrogrid
import OTSelector.Reconstruction.FinslerRelativeLawClassCubeBinomialUniform
import OTSelector.Reconstruction.FinslerRelativeLawUniformVolumeWeight

/-! Summed original full-cube binomial means retain the actual filling volume. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators
  BoundedContinuousFunction Classical unitInterval
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-- Translating a finite affine cloud leaves every actual displacement and its
legal graph unchanged. No assertion about its law is needed for this identity. -/
theorem unclampedBlockLegalTilted_affine_origin_eq (q : ℕ)
    (source : A → ℝ) (target : B → ℝ) (r side : ℝ) (origin origin' : Fin q → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ)
    (dS : BlockData ((Fin q → ℝ) × A)) (dT : BlockData ((Fin q → ℝ) × B)) :
    unclampedBlockLegalTilted q source target r kin probe t
      (mapBlockData (affineMarkedPoint origin side) dS)
      (mapBlockData (affineMarkedPoint origin side) dT) =
    unclampedBlockLegalTilted q source target r kin probe t
      (mapBlockData (affineMarkedPoint origin' side) dS)
      (mapBlockData (affineMarkedPoint origin' side) dT) := by
  unfold unclampedBlockLegalTilted
  dsimp only [mapBlockData, affineMarkedPoint]
  congr 1
  funext i j
  have hd : (fun l ↦ (origin l + side * (dT.2 j).1 l) - (origin l + side * (dS.2 i).1 l)) =
      (fun l ↦ (origin' l + side * (dT.2 j).1 l) - (origin' l + side * (dS.2 i).1 l)) := by
    funext l
    ring
  change r ^ (2 / (q : ℝ)) * kin (dS.2 i).2 (dT.2 j).2 _ + _ = _
  rw [hd]

theorem affineBinomialCubeExpectation_indep_origin {q : ℕ}
    (source : A → ℝ) (target : B → ℝ)
    (α : Measure A) [IsProbabilityMeasure α] (β : Measure B) [IsProbabilityMeasure β]
    (N : ℕ) (p : I) (side : ℝ) (origin origin' : Fin q → ℝ)
    (kin : A → B → (Fin q → ℝ) → ℝ) (probe : A → B → ℝ) (t : ℝ) :
    affineBinomialCubeExpectation source target α β N p side origin kin probe t =
      affineBinomialCubeExpectation source target α β N p side origin' kin probe t := by
  apply integral_congr_ae
  filter_upwards [] with d
  exact unclampedBlockLegalTilted_affine_origin_eq q source target N side origin origin' kin probe t d.1 d.2

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

/-- At fixed microscopic L, the normalized sum over changing finite families
has vanishing de-Poissonization error relative to its own actual filling
volume. The original full cell volume is never substituted for that volume. -/
theorem OriginalPopulationCoefficientCore.exists_clockClass_fullCube_sum_error_tendstoUniformlyOn
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
      ∀ (density : ℝ≥0) (_hdensity : 0 < density) (L : ℝ) (hL : 0 < L)
      (J : ℕ → Type*) [∀ N, Fintype (J N)] (origin : ∀ N, J N → Fin q → ℝ)
      (T : Set ℝ), IsCompact T → ∀ (V : ℝ), 0 ≤ V →
      (∀ᶠ N in atTop, (Fintype.card (J N) : ℝ) * positiveMicroscopicGridSide q L N ^ q ≤ V) →
      TendstoUniformlyOn (fun N : ℕ ↦ fun tilt : ℝ ↦
        (∑ j : J N, affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
          (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N)
          (origin N j) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) / (N : ℝ) -
        ((Fintype.card (J N) : ℝ) * positiveMicroscopicGridSide q L N ^ q) *
          (finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
            (density * ⟨L ^ q, pow_nonneg hL.le q⟩) (C.densityClockClassKinetic Q z₀ density)
            (C.clockClassProbe Q z₀ hz₀ f) tilt / L ^ q)) (fun _ ↦ 0) atTop T := by
  let π := clockClassJointProbability P₀ hP₀ hmass
  let α := π.map measurable_fst.aemeasurable
  let β := π.map measurable_snd.aemeasurable
  let q := Module.finrank ℝ (P C.seedIndex).seed.covector.ker
  obtain ⟨source, target, hcode, hunif⟩ :=
    C.exists_clockClass_fullCube_binomial_physical_uniform Q z₀ hz₀ f P₀ hP₀ hmass hq
  obtain ⟨K, hK, hbound⟩ := C.exists_clockClassKinetic_bound Q z₀ hz₀
  refine ⟨source, target, hcode, ?_⟩
  intro density hdensity L hL J _ origin T hT V hV hvol
  let mean := fun N tilt ↦ affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
    (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N)
    (0 : Fin q → ℝ) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt
  let r : ℝ≥0 := density * ⟨L ^ q, pow_nonneg hL.le q⟩
  let pressure := fun tilt ↦ finiteClassLegalPressure q (C.clockClassAllowed Q) (α : Measure _) (β : Measure _)
    r (C.densityClockClassKinetic Q z₀ density) (C.clockClassProbe Q z₀ hz₀ f) tilt
  have hmean : TendstoUniformlyOn mean pressure atTop T := by
    apply (hunif density hdensity L hL (fun _ ↦ 0) T hT).congr
    filter_upwards [positiveMicroscopicGridSide_eventually_eq q hL,
      positiveMicroscopicCubeProbability_eventually_eq q density hL] with N hside hp
    intro tilt _
    dsimp only [mean]
    rw [hside, hp]
  obtain ⟨M₀, hM₀⟩ := hT.exists_bound_of_continuousOn (continuous_id : Continuous (id : ℝ → ℝ)).continuousOn
  let factor := (density : ℝ) ^ (-(2 / (q : ℝ)))
  have hfactor : 0 ≤ factor := Real.rpow_nonneg density.coe_nonneg _
  have hkin : ∀ j k v, |C.densityClockClassKinetic Q z₀ density j k v| ≤ (factor * K) * ∑ l, v l ^ 2 := by
    intro j k v
    simp only [OriginalPopulationCoefficientCore.densityClockClassKinetic, neg_div]
    change |factor * C.clockClassKinetic Q z₀ j k v| ≤ _
    rw [abs_mul, abs_of_nonneg hfactor]
    exact (mul_le_mul_of_nonneg_left (hbound j k v) hfactor).trans_eq (by ring)
  have hkinEq : C.densityClockClassKinetic Q z₀ density =
      (fun j k v ↦ factor * C.clockClassKinetic Q z₀ j k v) := by
    funext j k v
    simp only [OriginalPopulationCoefficientCore.densityClockClassKinetic, neg_div, q, factor]
  have hkMeas : Measurable (Function.uncurry (fun p : Fin Q.count × Fin Q.count ↦
      C.densityClockClassKinetic Q z₀ density p.1 p.2)) := by
    rw [hkinEq]
    exact (C.measurable_clockClassKinetic Q z₀).const_mul factor
  let Bnd := (r : ℝ) * ((r : ℝ) ^ (2 / (q : ℝ)) * (factor * K * q) + max M₀ 0 * ‖f‖)
  have hBnd : 0 ≤ Bnd := by dsimp only [Bnd]; positivity
  have hpressure : ∀ tilt ∈ T, |pressure tilt| ≤ Bnd := by
    intro tilt ht
    have htM : |tilt| ≤ M₀ := by simpa only [Real.norm_eq_abs, id_eq] using hM₀ tilt ht
    have htB : |tilt| ≤ max M₀ 0 := htM.trans (le_max_left _ _)
    have hb := abs_legalMarkedPressure_le
      (kin := C.densityClockClassKinetic Q z₀ density)
      (probe := C.clockClassProbe Q z₀ hz₀ f) q
      (measurable_of_countable source) (measurable_of_countable target) (α : Measure _) (β : Measure _) r
      (mul_nonneg hfactor hK) (norm_nonneg f)
      hkMeas hkin
      (C.measurable_clockClassProbe Q z₀ hz₀ f) (C.clockClassProbe_abs_le Q z₀ hz₀ f) tilt
    change |finiteClassLegalPressure q _ _ _ _ _ _ _| ≤ _
    rw [finiteClassLegalPressure_eq_clock q _ source target hcode]
    exact hb.trans (mul_le_mul_of_nonneg_left
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right htB (norm_nonneg f))) r.coe_nonneg)
  have hweight : ∀ᶠ N in atTop, |(Fintype.card (J N) : ℝ) * positiveMicroscopicGridSide q L N ^ q| ≤ V := by
    filter_upwards [hvol] with N hN
    rw [abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (positiveMicroscopicGridSide_nonneg q L N) q))]
    exact hN
  have hnorm := tendstoUniformlyOn_volume_weighted_normalization hmean
    (tendsto_positiveMicroscopicGrid_mass hq hL) (pow_ne_zero _ hL.ne') hV hBnd hweight hpressure
  apply hnorm.congr
  filter_upwards [eventually_ge_atTop 1] with N hN
  intro tilt _
  have hsum : (∑ j : J N, affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
      (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N)
      (origin N j) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) =
      (Fintype.card (J N) : ℝ) * mean N tilt := by
    calc
      _ = ∑ _j : J N, mean N tilt := Finset.sum_congr rfl fun j _ ↦
        affineBinomialCubeExpectation_indep_origin source target (α : Measure _) (β : Measure _) N _ _ _ _ _ _ _
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change ((Fintype.card (J N) : ℝ) * positiveMicroscopicGridSide q L N ^ q) *
      (mean N tilt / ((N : ℝ) * positiveMicroscopicGridSide q L N ^ q) - pressure tilt / L ^ q) =
    (∑ j : J N, affineBinomialCubeExpectation source target (α : Measure _) (β : Measure _) N
      (positiveMicroscopicCubeProbability q density L N) (positiveMicroscopicGridSide q L N)
      (origin N j) (C.clockClassKinetic Q z₀) (C.clockClassProbe Q z₀ hz₀ f) tilt) / (N : ℝ) -
      ((Fintype.card (J N) : ℝ) * positiveMicroscopicGridSide q L N ^ q) * (pressure tilt / L ^ q)
  rw [hsum]
  have hn0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hs0 : positiveMicroscopicGridSide q L N ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne _))
  field_simp [hn0, hs0]

end OTSelector.Reconstruction
