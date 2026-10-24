import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficCurrent
import OTSelector.Reconstruction.OriginalMinimizerPathClockCurrentLtwo
import OTSelector.Reconstruction.OriginalOmittedCurrentOrientedTrafficDensityLimit

/-! The actual original minimizer loses subextensive Euclidean current energy in the same physical frame. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators Matrix.Norms.Operator
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The original minimizer internally supplies a finite expected Euclidean omitted-current
square for every same-frame physical cube and clock restriction, and its volume-normalized mean tends to zero.
The same genuine original path traffic controls all clocks, including restrictions that
vary with the cube scale; no completed current-energy or long-path rate is assumed. -/
theorem original_minimizer_canonical_oriented_omittedCurrent_euclidean_sq_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 2≤qdim)
    (b : OrthonormalBasis (Fin qdim) ℝ (EuclideanSpace ℝ (Fin qdim)))
    {densityμ densityν : M→ℝ} {v : M→E→ℝ} (cμ cν : ℝ≥0∞)
    (hρμ : Continuous densityμ) (hρμ0 : ∀x,0≤densityμ x)
    (hρν : Continuous densityν) (hρν0 : ∀x,0≤densityν x)
    (hv : ∀old,ContinuousOn (v old) (extChartAt 𝓘(ℝ,E) old).target)
    (hv0 : ∀old,∀y∈(extChartAt 𝓘(ℝ,E) old).target,0≤v old y)
    (hdensityμ : PopulationSeedClockDensity S w
      (μ.map (fun x : ℝ↦x-S.level)) densityμ v cμ.toReal)
    (hdensityν : PopulationSeedClockDensity S w
      (ν.map (fun x : ℝ↦x-S.level)) densityν v cν.toReal)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hgap : 0<gap)
    {g : ℝ→ℝ→ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀x y,|g x y|≤gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) (A : ℝ → Set ℝ) :
    let η := originalEuclideanMollifier qdim
    let energy := fun R : ℝ ↦ ∫⁻ scene, ∫⁻ z in originalCenteredPhysicalCubeRegion b (2 * R),
      ENNReal.ofReal (‖(EuclideanSpace.equiv (Fin qdim) ℝ).symm
        (originalSeedPathClockSetCurrent S w (fun x ↦ η (x-z)) (A R) scene -
          originalPairRestrictedSeedPathClockSetCurrent S w
            (originalOrientedPathLengthRetained S w b R (ell R))
            (fun x ↦ η (x-z)) (A R) scene)‖^2)
      ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))
    (∀ R, energy R ≠ (∞ : ℝ≥0∞)) ∧
    Tendsto (fun R : ℝ ↦ (energy R).toReal / volume.real (originalCenteredPhysicalCubeRegion b (2 * R)))
      atTop (𝓝 0) := by
  obtain ⟨radius,hrad,hrspan,GLeft,GRight,RemLeft,RemRight,hGLeft,hGRight,
    hRemLeft,hRemRight,hpoleLeft,hpoleRight,_hcomparison⟩ :=
    D.exists_original_both_poles_common_radius hF hw
  have hsupport : ∀ x : Fin qdim → ℝ, 1 < ‖x‖ → originalEuclideanMollifier qdim x = 0 :=
    fun x hx ↦ raw_unit_range_of_euclidean_unit_range
      (originalEuclideanMollifier_unit_range qdim) x hx.le
  have hupper : ∀ x : Fin qdim → ℝ,
      originalEuclideanMollifier qdim x ≤ originalEuclideanMollifierBound qdim :=
    fun x ↦ (le_abs_self _).trans (abs_originalEuclideanMollifier_le qdim x)
  have hfull := D.original_minimizer_completePathAbsoluteTraffic_memLp_two
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hrad hrspan hrad hrspan hGLeft hGRight hRemLeft.continuousOn hRemRight.continuousOn
    hpoleLeft hpoleRight hg hgb τ Q hmin
    (contDiff_originalEuclideanMollifier qdim).continuous.measurable
    (integrable_originalEuclideanMollifier qdim) (originalEuclideanMollifier_nonneg qdim)
    (by norm_num : (0:ℝ) ≤ 1) (originalEuclideanMollifierBound_nonneg qdim) hupper hsupport
  let η := originalEuclideanMollifier qdim
  let traffic := fun R : ℝ ↦ ∫⁻ scene, ∫⁻ z in originalCenteredPhysicalCubeRegion b (2 * R),
    originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z))
      (originalOrientedPathLengthRetained S w b R (ell R))ᶜ scene ^ 2
      ∂volume ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))
  let full := ∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2
    ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))
  have hfullfin : full ≠ (∞ : ℝ≥0∞) :=
    (D.original_longPathTraffic_sq_finite_and_tendsto_zero hF hw hbounds Q
      (contDiff_originalEuclideanMollifier qdim).continuous.measurable
      (integrable_originalEuclideanMollifier qdim) hfull.2).1
  have htrafficfin (R : ℝ) : traffic R ≠ (∞ : ℝ≥0∞) := by
    have hm := (measurable_original_restrictedPathTraffic_shift_joint hF hw
      (contDiff_originalEuclideanMollifier qdim).continuous.measurable
      (measurableSet_originalOrientedPathLengthRetained S hF hw b R (ell R)).compl).pow_const 2
    have hb : traffic R ≤ volume (originalCenteredPhysicalCubeRegion b (2 * R)) * full := by
      change (∫⁻ scene, ∫⁻ z in originalCenteredPhysicalCubeRegion b (2 * R),
        originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x-z))
          (originalOrientedPathLengthRetained S w b R (ell R))ᶜ scene ^ 2 ∂volume ∂(Q.law : Measure _)) ≤ _
      rw [← lintegral_lintegral_swap hm.aemeasurable]
      calc
        _ ≤ ∫⁻ z in originalCenteredPhysicalCubeRegion b (2 * R), ∫⁻ scene,
            originalSeedCompletePathAbsoluteTraffic S w (fun x ↦ η (x-z)) scene ^ 2
              ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)) := by
          apply lintegral_mono
          intro z
          apply lintegral_mono
          intro scene
          exact pow_le_pow_left' (originalSeedRestrictedPathAbsoluteTraffic_le_full S w
            (fun x ↦ η (x-z)) _ scene) 2
        _ = _ := by
          simp_rw [Q.lintegral_original_fullTraffic_sq_shift (η := η) hF hw
            (contDiff_originalEuclideanMollifier qdim).continuous.measurable]
          simp only [lintegral_const, Measure.restrict_apply_univ, full]
          exact mul_comm _ _
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top
      (by rw [volume_originalOrientedTraffic_cube]; exact isCompact_Icc.measure_ne_top) hfullfin) hb
  have hcmp (R : ℝ) := D.lintegral_originalPairComplementCurrent_euclidean_sq_le_traffic_sq
    hF hw hbounds Q (originalOrientedPathLengthRetained S w b R (ell R))
    (measurableSet_originalOrientedPathLengthRetained S hF hw b R (ell R)) (A R)
    (originalCenteredPhysicalCubeRegion b (2 * R))
  dsimp only
  refine ⟨fun R ↦ ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htrafficfin R)) (hcmp R), ?_⟩
  have hlim := (D.tendsto_original_oriented_wholeCube_omittedTraffic_sq_density_zero hF hw b hbounds Q
    (contDiff_originalEuclideanMollifier qdim).continuous.measurable
    (integrable_originalEuclideanMollifier qdim) (by norm_num : (0:ℝ) ≤ 1)
    hsupport hfull.2 hell hlarge hsmall).const_mul (qdim:ℝ)
  simp only [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ div_nonneg ENNReal.toReal_nonneg measureReal_nonneg) ?_ hlim
  apply Eventually.of_forall
  intro R
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htrafficfin R)) (hcmp R)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg qdim)] at hreal
  exact (div_le_div_of_nonneg_right hreal measureReal_nonneg).trans_eq (by rw [mul_div_assoc])

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
