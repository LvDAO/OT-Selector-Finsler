import OTSelector.Reconstruction.OriginalWholeCubeOmittedTraffic
import OTSelector.Reconstruction.OriginalTrafficSquareTail
import OTSelector.Reconstruction.NormalizedShellBulkEnergy
import OTSelector.Reconstruction.NormalizedHaarCubeCount

/-! # The actual omitted complete-path square energy is subextensive -/
open Set Function Filter MeasureTheory ProbabilityTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Restricting the same original matching to its measurable path-retained
core loses vanishing absolute-current square energy per original cube volume.
The full-traffic square estimate is the sole analytic input, with no tail rate,
no endpoint-square moment and no boundary-flux-square premise. -/
theorem tendsto_original_wholeCube_omittedTraffic_sq_density_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ}
    (hηm : Measurable η) (hηi : Integrable η volume)
    {radius : ℝ} (hradius : 0 ≤ radius) (hηsupport : ∀ x, radius < ‖x‖ → η x = 0)
    (hfullI : Integrable (fun scene ↦
      (originalSeedCompletePathAbsoluteTraffic S w η scene).toReal ^ 2)
        (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))))
    {ell : ℝ → ℝ} (hell : ∀ᶠ R in atTop, 0 ≤ ell R)
    (hlarge : Tendsto ell atTop atTop)
    (hsmall : Tendsto (fun R ↦ ell R / R) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ ↦
      (∫⁻ scene, ∫⁻ z in haarRootCube (Fin (finrank ℝ S.covector.ker)) R,
        originalSeedRestrictedPathAbsoluteTraffic S w (fun x ↦ η (x - z))
          (originalPathLengthRetained S w R (ell R))ᶜ scene ^ 2 ∂volume
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))).toReal /
          volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) atTop (𝓝 0) := by
  obtain ⟨hfullfin, htailfin, htaillim⟩ :=
    D.original_longPathTraffic_sq_finite_and_tendsto_zero hF hw hbounds Q hηm hηi hfullI
  let full := ∫⁻ scene, originalSeedCompletePathAbsoluteTraffic S w η scene ^ 2
    ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
  let tail := fun ell : ℝ ↦ ∫⁻ scene, originalSeedLongPathAbsoluteTraffic S w η ell scene ^ 2
    ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))
  let delta := fun R : ℝ ↦ 3 * ell R + radius
  have hdelta : ∀ᶠ R in atTop, 0 ≤ delta R := hell.mono fun R hR ↦ by dsimp [delta]; positivity
  have hdeltaSmall : Tendsto (fun R ↦ delta R / R) atTop (𝓝 0) := by
    have h₁ : Tendsto (fun R ↦ 3 * (ell R / R)) atTop (𝓝 (0 : ℝ)) := by
      simpa using tendsto_const_nhds.mul hsmall
    have h₂ : Tendsto (fun R : ℝ ↦ radius / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    simpa only [delta, add_div, mul_div_assoc, zero_add, add_zero] using h₁.add h₂
  have hcollar : Tendsto (fun R : ℝ ↦
      volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R \
        haarRootCube (Fin (finrank ℝ S.covector.ker)) (R - delta R)) /
      volume.real (haarRootCube (Fin (finrank ℝ S.covector.ker)) R)) atTop (𝓝 0) := by
    simpa only [one_mul] using tendsto_haarRootCube_innerCollar_ratio
      (Fin (finrank ℝ S.covector.ker)) hdelta (k := 1) zero_le_one hdeltaSmall
  have htailReal : Tendsto (fun R ↦ (tail (ell R)).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [ENNReal.toReal_zero, Function.comp_def] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (htaillim.comp hlarge)
  have hupper := (tendsto_const_nhds (x := full.toReal)).mul hcollar |>.add htailReal
  simp only [mul_zero, zero_add] at hupper
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ div_nonneg ENNReal.toReal_nonneg measureReal_nonneg) _ hupper
  filter_upwards [hell, eventually_gt_atTop (0 : ℝ),
    eventually_collar_mul_le_radius (k := (1 : ℝ)) hdeltaSmall] with R hellR hR hdeltaR
  have hRfit : 3 * ell R + radius ≤ R := by simpa only [one_mul, delta] using hdeltaR
  have hbound := D.lintegral_original_wholeCube_omittedTraffic_sq_le hF hw Q hηm
    hellR hradius hRfit hηsupport
  have hdeltaeq : R - delta R = R - 3 * ell R - radius := by dsimp [delta]; ring
  have hnorm := finite_and_normalized_shell_bulk_energy_le
    (Fin (finrank ℝ S.covector.ker)) (delta := delta R) hR hfullfin (htailfin (ell R))
    (by simpa only [hdeltaeq] using hbound)
  exact hnorm.2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
