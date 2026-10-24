import OTSelector.Reconstruction.OriginalMinimizerTargetCommonScaleWindow
import OTSelector.Reconstruction.OriginalMinimizerDyadicTrafficBudget
import OTSelector.Reconstruction.OriginalCompactClockWeightedOccupation
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Finite coarse regular windows use the same original experiment and its
actual short compliance leg. Their count and Palm moments are produced internally. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
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
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- Every original source or target determinant carrier has finite unit-cell
intensity at its actual fixed frame; its original clock law is retained. -/
theorem exists_original_regular_phaseCell_finite_unit_intensity
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    (side : Fin 2) (T : Matrix (Fin qdim) (Fin qdim) ℝ) [Invertible T]
    {cut Ddet : ℝ} (hcut : cut∈Ioo D.lo D.hi) :
    ∃ Λ : ℝ,0≤Λ ∧
      (if side=0 then
        ((volume:Measure (Fin qdim→ℝ)).prod μ)
          (D.commonScaleOriginalSourcePhaseCell T cut 1
            (D.originalBirthSourceDetCarrier T cut univ Ddet) 0 0 1)
      else
        ((volume:Measure (Fin qdim→ℝ)).prod ν)
          (D.commonScaleOriginalTargetPhaseCell T cut 1
            (D.originalBirthTargetDetCarrier T cut univ Ddet) 0 0 1))≤ENNReal.ofReal Λ := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  let bound := (ENNReal.ofReal |T⁻¹.det| *
    volume (Metric.closedBall (0:Fin qdim→ℝ) (phaseSourceCellRadius (Fin qdim) 1))) *
      ENNReal.ofReal Ddet * ENNReal.ofReal 1
  have hfin : bound≠(∞:ℝ≥0∞) := phaseBandIntensity_bound_ne_top T⁻¹ 1 Ddet 1
  refine ⟨bound.toReal,ENNReal.toReal_nonneg,?_⟩
  rw [ENNReal.ofReal_toReal hfin]
  fin_cases side
  · have hB:=D.measurableSet_originalBirthSourceDetCarrier hF hw T hcut MeasurableSet.univ Ddet
    have h:=prod_volume_markedPhaseSourceCell_le_of_band_det_bound
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
      (D.measurable_normalizedSourcePhaseLeg hF hw T hcut)
      (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut)
      (D.measurable_commonScaleOriginalSourcePhaseCenter hF hw T hcut 1 0 0) hB μ 1 (D:=Ddet) (m:=1)
      (fun a ha↦ha.2) (by simpa only [ENNReal.ofReal_one] using (prob_le_one
        (μ:=μ) (s:=D.originalBirthSourceDetCarrier T cut univ Ddet)))
    simpa only [commonScaleOriginalSourcePhaseCell,one_smul,bound,Fin.mk_zero,ite_true] using h
  · have hB:=D.measurableSet_originalBirthTargetDetCarrier hF hw T hcut MeasurableSet.univ Ddet
    have h:=prod_volume_markedPhaseSourceCell_le_of_band_det_bound
      (T.isUnit_nonsing_inv_det (Matrix.isUnit_det_of_invertible T))
      (D.measurable_normalizedTargetPhaseLeg hF hw T hcut)
      (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut)
      (D.measurable_commonScaleOriginalTargetPhaseCenter hF hw T hcut 1 0 0) hB ν 1 (D:=Ddet) (m:=1)
      (fun a ha↦ha.2) (by simpa only [ENNReal.ofReal_one] using (prob_le_one
        (μ:=ν) (s:=D.originalBirthTargetDetCarrier T cut univ Ddet)))
    simpa only [commonScaleOriginalTargetPhaseCell,one_smul,bound,show (⟨1,by decide⟩:Fin 2)≠0 by decide,ite_false] using h

/-- True original phase geometry and a bounded physical one-edge occupation
make every fixed compact regular window L2. No small elapsed-scale condition or
Palm-energy premise is required; source and target use their own original counts. -/
theorem original_regular_compactWindow_traffic_memLp_two_of_phase_geometry
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels)
    {gap diameter : ℝ} (hgap : 0<gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ→ℝ→ℝ} {G : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀a b,|g a b|≤G) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    (side : Fin 2) (T : Matrix (Fin qdim) (Fin qdim) ℝ) [Invertible T]
    {cut h ell ρ A U₀ : ℝ} (hcut : cut∈Ioo D.lo D.hi) (hh : 0<h) (hA : 0≤A)
    (hclockRange : ∀r∈Icc (0:ℝ) 1,cut+ell*r∈Ioo D.lo D.hi)
    (hR : ∀r∈Icc (0:ℝ) 1,‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖≤ρ)
    (hRLip : ∀r∈Icc (0:ℝ) 1,∀v∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r-
        originalNormalizedClockMobility S w T (cut+S.level) ell v‖≤A*|r-v|)
    (hsmall : ∀r∈Icc (0:ℝ) 1,
      ‖originalNormalizedClockMobility S w T (cut+S.level) ell r‖*
        Real.sqrt ((qdim:ℝ)/h^2)≤(1/2:ℝ))
    {J : Set ℝ} (hJ : IsCompact J) (hJI : ∀c∈J,c-S.level∈Ioo D.lo D.hi)
    (mask : MarkClock→ℝ≥0∞) (hm : Measurable mask) (hm1 : ∀z,mask z≤1)
    (hz : ∀m c,c∉J→mask (m,c)=0)
    (hclock : ∀m c,ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖*mask (m,c)≠0→∃r∈Icc (0:ℝ) 1,c=cut+S.level+ell*r)
    (helig : ∀(e:LegalMarkedPhysicalEdge qdim) c,
      ENNReal.ofReal ‖originalSeedClockOccupation S w c (physicalPairAnchor e).2‖*
        mask ((physicalPairAnchor e).2,c)≠0→
      e∈D.normalizedMomentumPhaseEligibleEdges T cut h ∧
        (U₀ • 1-(if side=0 then T*D.sourcePhaseLeg cut e.1.2*Tᵀ
          else T*D.targetPhaseLeg cut e.2.2*Tᵀ)).PosSemidef)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    {R Bedge : ℝ} (hRad : 0≤R) (hBedge : 0≤Bedge)
    (hηR : ∀x,ENNReal.ofReal (η x)≠0→‖x‖≤R)
    (hsingle : ∀x m,(∫⁻c:ℝ,ENNReal.ofReal (η (x+originalSeedPathOffset S w c m))*
      (ENNReal.ofReal ‖originalSeedClockOccupation S w c m‖*mask (m,c)))≤ENNReal.ofReal Bedge) :
    MemLp (fun scene:LegalMarkedOptimalInputScene qdim↦
      (legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x))
        (fun z↦ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖*mask z) scene).toReal)
      2 (Q.law:Measure (LegalMarkedOptimalInputScene qdim)) := by
  let f:=fun z:MarkClock↦ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖*mask z
  have hf : Measurable f := (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hm
  have hηfinite : (∫⁻x,ENNReal.ofReal (η x)∂(volume:Measure (Fin qdim→ℝ)))≠(∞:ℝ≥0∞) :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hηI.2).ne
  have hffinite : (∫⁻m,∫⁻c:ℝ,f (m,c)∂volume∂legalMarkedJointPalm qdim Q.law)≠(∞:ℝ≥0∞) := by
    have ho := (hasFiniteIntegral_iff_norm _).mp
      (D.integrable_original_clockOccupation_prod hF hw hbounds Q).hasFiniteIntegral
    rw [lintegral_prod _ (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.aemeasurable] at ho
    apply ne_top_of_le_ne_top ho.ne
    apply lintegral_mono
    intro m
    apply lintegral_mono
    intro c
    exact mul_le_of_le_one_right (by positivity) (hm1 (m,c))
  have hpfinite := (D.lintegral_original_compactClock_maskedWeightedOccupation_lt_top
    hF hw hgap hbounds Q (Tᵀ)⁻¹ hJ hJI mask hm1 hz).ne
  have hclock' : ∀m c,f (m,c)≠0→∃r∈Icc (0:ℝ) 1,c=cut+S.level+ell*r :=
    fun m c hc↦hclock m c hc
  have hwindow : ∀x,ENNReal.ofReal (η x)≠0→‖T*ᵥx‖≤(‖T‖*R)*1 := by
    intro x hx
    simpa only [mul_one] using (Matrix.linfty_opNorm_mulVec T x).trans
      (mul_le_mul_of_nonneg_left (hηR x hx) (norm_nonneg _))
  have hbound : ∀e∈legalMarkedCompletePathContributors qdim
      (fun z↦originalSeedPathOffset S w z.2 z.1) (fun x↦ENNReal.ofReal (η x)) f,
      (legalMarkedCompletePathEdgeTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
        (fun x↦ENNReal.ofReal (η x)) f e).toReal≤Bedge := by
    intro e _
    simpa only [legalMarkedCompletePathEdgeTraffic,physicalPairAnchor,f,ENNReal.toReal_ofReal hBedge] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hsingle e.1.1 (physicalPairAnchor e).2)
  obtain ⟨Ddet,hDdet,hdet⟩:=exists_det_bound_of_posSemidef_scalar_upper (ι:=Fin qdim) U₀
  obtain ⟨Λ,hΛ,hunit⟩:=D.exists_original_regular_phaseCell_finite_unit_intensity hF hw side T hcut (Ddet:=Ddet)
  fin_cases side
  · have hmasks : ∀(e:LegalMarkedPhysicalEdge qdim) c,f ((physicalPairAnchor e).2,c)≠0→
        e∈D.normalizedMomentumPhaseEligibleEdges T cut h ∧
          e.1.2∈D.originalBirthSourceDetCarrier T cut univ Ddet := by
      intro e c hc
      obtain ⟨he,hu⟩:=helig e c hc
      refine ⟨he,Set.mem_univ _,?_⟩
      exact hdet _ (D.normalizedSourcePhaseLeg_posSemidef hF hw T hcut e.1.2) (by simpa using hu)
    exact (D.original_minimizer_commonScale_fullWindow_traffic_memLp_two_le
      hF hw hgap hbounds T le_rfl hg hgb τ Q hmin hcut hh (mul_nonneg (norm_nonneg _) hRad)
      hclockRange hsmall hA hR hRLip hη.ennreal_ofReal hf hclock' hwindow
      (D.measurableSet_originalBirthSourceDetCarrier hF hw T hcut MeasurableSet.univ Ddet)
      hmasks hηfinite hffinite hBedge hΛ hbound (by simpa using hunit) le_rfl hpfinite).1
  · have hmasks : ∀(e:LegalMarkedPhysicalEdge qdim) c,f ((physicalPairAnchor e).2,c)≠0→
        e∈D.normalizedMomentumPhaseEligibleEdges T cut h ∧
          e.2.2∈D.originalBirthTargetDetCarrier T cut univ Ddet := by
      intro e c hc
      obtain ⟨he,hu⟩:=helig e c hc
      refine ⟨he,Set.mem_univ _,?_⟩
      exact hdet _ (D.normalizedTargetPhaseLeg_posSemidef hF hw T hcut e.2.2) (by simpa using hu)
    exact (D.original_minimizer_commonScale_target_fullWindow_traffic_memLp_two_le
      hF hw hgap hbounds T le_rfl hg hgb τ Q hmin hcut hh (mul_nonneg (norm_nonneg _) hRad)
      hclockRange hsmall hA hR hRLip hη.ennreal_ofReal hf hclock' hwindow
      (D.measurableSet_originalBirthTargetDetCarrier hF hw T hcut MeasurableSet.univ Ddet)
      hmasks hηfinite hffinite hBedge hΛ hbound (by simpa using hunit) le_rfl hpfinite).1

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
