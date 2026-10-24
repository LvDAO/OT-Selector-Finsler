import OTSelector.Reconstruction.OriginalMinimizerCompletePathTrafficLtwo
import OTSelector.Reconstruction.OriginalMinimizerPrefixCurrentCentering

/-! The actual whole-path traffic controls every clock-set current, including
signed kernels dominated by a compact nonnegative kernel. Its proved L2 bound
therefore supplies vector and arbitrary continuous-linear current readouts. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators Classical Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

/-- Every literal clock restriction of the actual signed current is dominated
by its full original absolute traffic in a dominating spatial kernel. -/
theorem original_pathClockSetCurrent_enorm_le_traffic
    (S : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    {w : S.covector.ker} (hw : w∈S.labels)
    {ψ ξ : (Fin (finrank ℝ S.covector.ker)→ℝ)→ℝ} (hψ : Measurable ψ)
    (hdom : ∀x,|ψ x|≤ξ x) (A : Set ℝ)
    (scene : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)) :
    ENNReal.ofReal ‖originalSeedPathClockSetCurrent S w ψ A scene‖ ≤
      originalSeedCompletePathAbsoluteTraffic S w ξ scene := by
  let f := fun c : ℝ↦legalMarkedPathWindowReadout (finrank ℝ S.covector.ker)
    (originalSeedPathOffset S w c) ψ (originalSeedClockOccupation S w c) scene
  calc
    _ ≤ ∫⁻c in A,ENNReal.ofReal ‖f c‖ := by
      simpa only [originalSeedPathClockSetCurrent,ofReal_norm,f] using
        (enorm_integral_le_lintegral_enorm (μ := (volume : Measure ℝ).restrict A) f)
    _ ≤ ∫⁻c : ℝ,ENNReal.ofReal ‖f c‖ :=
      lintegral_mono' Measure.restrict_le_self (fun _↦le_rfl)
    _ ≤ originalSeedCompletePathAbsoluteTraffic S w (fun x↦|ψ x|) scene :=
      lintegral_original_pathClockWindowReadout_norm_le_traffic S hF hw hψ scene
    _ ≤ _ := by
      unfold originalSeedCompletePathAbsoluteTraffic legalMarkedCompletePathTraffic
      apply lintegral_mono
      intro p
      apply lintegral_mono
      intro c
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hdom _)) le_rfl

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The same original minimizer supplies L2 of every clock-set current and
any continuous-linear readout. Signed kernels need only a measurable
pointwise domination by the given nonnegative compact integrable kernel. -/
theorem original_minimizer_pathClockSetCurrent_memLp_two
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) (hq : 2≤qdim)
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
    {ξ : (Fin qdim→ℝ)→ℝ} (hξ : Measurable ξ) (hξI : Integrable ξ volume)
    (hξ0 : ∀x,0≤ξ x) {physicalRadius M₀ : ℝ}
    (hRadius : 0≤physicalRadius) (hM : 0≤M₀)
    (hξM : ∀x,ξ x≤M₀) (hξR : ∀x,physicalRadius<‖x‖→ξ x=0)
    {ψ : (Fin qdim→ℝ)→ℝ} (hψ : Measurable ψ) (hdom : ∀x,|ψ x|≤ξ x)
    (A : Set ℝ) (C : (Fin qdim→ℝ)→L[ℝ] Y) :
    MemLp (originalSeedPathClockSetCurrent S w ψ A) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
    MemLp (C ∘ originalSeedPathClockSetCurrent S w ψ A) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
    ∀ᵐscene∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      ‖C (originalSeedPathClockSetCurrent S w ψ A scene)‖ ≤
        ‖C‖*(originalSeedCompletePathAbsoluteTraffic S w ξ scene).toReal := by
  obtain ⟨radius,hrad,hrspan,GLeft,GRight,RemLeft,RemRight,hGLeft,hGRight,
    hRemLeft,hRemRight,hpoleLeft,hpoleRight,_hcomparison⟩ :=
    D.exists_original_both_poles_common_radius hF hw
  have htraffic := (D.original_minimizer_completePathAbsoluteTraffic_memLp_two
    hF hw hq cμ cν hρμ hρμ0 hρν hρν0 hv hv0 hdensityμ hdensityν hbounds hgap
    hrad hrspan hrad hrspan hGLeft hGRight hRemLeft.continuousOn hRemRight.continuousOn hpoleLeft hpoleRight
    hg hgb τ Q hmin hξ hξI hξ0 hRadius hM hξM hξR).1
  have hψI : Integrable ψ volume := hξI.mono' hψ.aestronglyMeasurable
    (Eventually.of_forall fun x↦by simpa only [Real.norm_eq_abs] using hdom x)
  have hbound : ∀ᵐscene∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      ‖originalSeedPathClockSetCurrent S w ψ A scene‖ ≤
        (originalSeedCompletePathAbsoluteTraffic S w ξ scene).toReal := by
    filter_upwards [D.ae_original_completePathAbsoluteTraffic_lt_top hF hw hbounds Q hξ hξI]
      with scene hs
    have h := ENNReal.toReal_mono hs.ne
      (original_pathClockSetCurrent_enorm_le_traffic S hF hw hψ hdom A scene)
    simpa only [ENNReal.toReal_ofReal (norm_nonneg _)] using h
  have hcurrent : MemLp (originalSeedPathClockSetCurrent S w ψ A) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) :=
    htraffic.mono' (D.integrable_original_pathClockSetCurrent hF hw hbounds Q hψ hψI A).aestronglyMeasurable hbound
  refine ⟨hcurrent,hcurrent.continuousLinearMap_comp C,?_⟩
  filter_upwards [hbound] with scene hs
  exact (C.le_opNorm _).trans (mul_le_mul_of_nonneg_left hs (norm_nonneg C))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
