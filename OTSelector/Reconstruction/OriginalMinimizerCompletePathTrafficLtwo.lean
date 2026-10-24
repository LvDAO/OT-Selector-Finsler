import OTSelector.Reconstruction.OriginalMinimizerFullBirthTrafficLtwo
import OTSelector.Reconstruction.OriginalMinimizerRightFullBirthTrafficLtwo
import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficLtwo
import OTSelector.Reconstruction.OriginalMinimizerRightOldTrafficLtwo
import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularMiddle
import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthLtwo
import OTSelector.Reconstruction.OriginalMinimizerRightRegularLtwo
import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficClockReadout
import Mathlib.MeasureTheory.Function.L2Space

/-! The actual original minimizer has square-integrable whole-clock absolute
traffic. All eight literal regions are proved internally from the same original
matching, its two original intensities and its two focal matrix residues. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Topology BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The same original minimizer's entire original absolute path traffic is L2,
and its literal real square is integrable. The actual eight-region estimates
are produced internally, with one common positive collar chosen only after
all four focal producers have fixed their auxiliary geometry. -/
theorem original_minimizer_completePathAbsoluteTraffic_memLp_two
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
    {poleηLeft poleηRight : ℝ} (hηLeft : 0<poleηLeft) (hηLeftspan : poleηLeft<D.hi-D.lo)
    (hηRight : 0<poleηRight) (hηRightspan : poleηRight<D.hi-D.lo)
    {GLeft GRight : Matrix (Fin qdim) (Fin qdim) ℝ}
    (hGLeft : GLeft.PosSemidef) (hGRight : GRight.PosSemidef)
    {RemLeft RemRight : ℝ→Matrix (Fin qdim) (Fin qdim) ℝ}
    (hRemLeft : ContinuousOn RemLeft (Ioo (-poleηLeft) poleηLeft))
    (hRemRight : ContinuousOn RemRight (Ioo (-poleηRight) poleηRight))
    (hpoleLeft : ∀r∈Ioo 0 poleηLeft,originalSeedKernel S w (D.lo+r)=(r^2)⁻¹•GLeft+RemLeft r)
    (hpoleRight : ∀r∈Ioo 0 poleηRight,originalSeedKernel S w (D.hi-r)=(r^2)⁻¹•GRight+RemRight r)
    {g : ℝ→ℝ→ℝ} {gBound : ℝ} (hg : Measurable (Function.uncurry g))
    (hgb : ∀x y,|g x y|≤gBound) (τ : ℝ)
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (hmin : ∀P : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g,
      Q.value τ≤P.value τ)
    {η : (Fin qdim→ℝ)→ℝ} (hη : Measurable η) (hηI : Integrable η volume)
    (hη0 : ∀x,0≤η x) {physicalRadius M₀ : ℝ}
    (hRadius : 0≤physicalRadius) (hM : 0≤M₀)
    (hηM : ∀x,η x≤M₀) (hηR : ∀x,physicalRadius<‖x‖→η x=0) :
    MemLp (fun scene↦(originalSeedCompletePathAbsoluteTraffic S w η scene).toReal)
      2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
    Integrable (fun scene↦(originalSeedCompletePathAbsoluteTraffic S w η scene).toReal^2)
      (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) := by
  have hq0 : 0<qdim := by omega
  obtain ⟨capL,εLB,hcapL,_hcapL1,hεLB,hLB⟩ :=
    D.exists_original_left_full_birth_totalTraffic_memLp_two_on_collar hF hw hq0
      cμ hρμ hρμ0 hv hv0 hdensityμ hbounds hgap hηLeft hηLeftspan hGLeft hRemLeft hpoleLeft
      hg hgb τ Q hmin hη hη0 hRadius (by norm_num : (0:ℝ)<1) hηR hM hηM
  obtain ⟨capR,εRB,hcapR,_hcapR1,hεRB,hRB⟩ :=
    D.exists_original_right_full_birth_totalTraffic_memLp_two_on_collar hF hw hq0
      cν hρν hρν0 hv hv0 hdensityν hbounds hgap hηRight hηRightspan hGRight hRemRight hpoleRight
      hg hgb τ Q hmin hη hη0 hRadius (by norm_num : (0:ℝ)<1) hηR hM hηM
  obtain ⟨εLO,hεLO,_hεLO1,hLO⟩ :=
    D.exists_original_left_full_old_traffic_memLp_two_on_collar hF hw hq
      cμ hρμ hρμ0 hv hv0 hdensityμ hbounds hgap hηLeft hηLeftspan hGLeft hRemLeft hpoleLeft
      hg hgb τ Q hmin hη hηI hη0 hRadius (by norm_num : (0:ℝ)<1) hηR hM hηM
  obtain ⟨εRO,hεRO,_hεRO1,hRO⟩ :=
    D.exists_original_right_full_old_traffic_memLp_two_on_collar hF hw hq
      cν hρν hρν0 hv hv0 hdensityν hbounds hgap hηRight hηRightspan hGRight hRemRight hpoleRight
      hg hgb τ Q hmin hη hηI hη0 hRadius (by norm_num : (0:ℝ)<1) hηR hM hηM
  let ε₀ := min εLB (min εRB (min εLO εRO))
  have hε₀ : 0<ε₀ := lt_min hεLB (lt_min hεRB (lt_min hεLO hεRO))
  let ε := ε₀/2
  have hε : 0<ε := half_pos hε₀
  have hεsmall : ε<ε₀ := half_lt_self hε₀
  have heLB : ε<εLB := hεsmall.trans_le (min_le_left _ _)
  have heRB : ε<εRB := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heLO : ε<εLO := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heRO : ε<εRO := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let P : Measure (LegalMarkedOptimalInputScene qdim) := Q.law
  have hbirthL := (hLB hε heLB).1
  have hbirthR := (hRB hε heRB).1
  have hbirthLeq (scene : LegalMarkedOptimalInputScene qdim) :
      (∑ell : Fin (birthPhysicalClockWindowCount capL),∑'nj : ℕ×ℕ,
        ∑i∈Finset.range (dyadicBirthBandCount nj.2),
          legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedLeftBirthPhysicalClockWeight ε capL nj.1 nj.2 i ell) scene) =
      D.originalSupportedClockRegionAbsoluteTraffic η ε 0 scene := by
    exact D.sum_tsum_originalSupportedBirthWindowTraffic_eq_region hF hw hη hε hcapL 0 scene
  have hbirthReq (scene : LegalMarkedOptimalInputScene qdim) :
      (∑ell : Fin (birthPhysicalClockWindowCount capR),∑'nj : ℕ×ℕ,
        ∑i∈Finset.range (dyadicBirthBandCount nj.2),
          legalMarkedCompletePathTraffic qdim (fun z↦originalSeedPathOffset S w z.2 z.1)
            (fun x↦ENNReal.ofReal (η x))
            (D.originalSupportedRightBirthPhysicalClockWeight ε capR nj.1 nj.2 i ell) scene) =
      D.originalSupportedClockRegionAbsoluteTraffic η ε 4 scene := by
    exact D.sum_tsum_originalSupportedBirthWindowTraffic_eq_region hF hw hη hε hcapR 1 scene
  have h0 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 0 scene).toReal) 2 P := by
    simpa only [hbirthLeq] using hbirthL
  have h4 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 4 scene).toReal) 2 P := by
    simpa only [hbirthReq] using hbirthR
  have hold0 : originalFocalOldRegionIndex (0:Fin 2)=(2:Fin 8) := by decide
  have hold1 : originalFocalOldRegionIndex (1:Fin 2)=(6:Fin 8) := by decide
  have hregular0 : originalRegularRegionIndex (0:Fin 4)=(1:Fin 8) := by decide
  have hregular1 : originalRegularRegionIndex (1:Fin 4)=(3:Fin 8) := by decide
  have hregular2 : originalRegularRegionIndex (2:Fin 4)=(5:Fin 8) := by decide
  have hregular3 : originalRegularRegionIndex (3:Fin 4)=(7:Fin 8) := by decide
  have h2 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 2 scene).toReal) 2 P := by
    simpa only [D.tsum_originalFocalOldPieceAbsoluteTraffic_eq_region hF hw hη hε,hold0,P] using (hLO hε heLO).1
  have h6 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 6 scene).toReal) 2 P := by
    simpa only [D.tsum_originalFocalOldPieceAbsoluteTraffic_eq_region hF hw hη hε,hold1,P] using (hRO hε heRO).1
  have h1 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 1 scene).toReal) 2 P := by
    simpa only [D.originalRegularPieceAbsoluteTraffic_eq_region,hregular0,P] using
      (D.original_minimizer_regularBirth_leftPiece_memLp_two hF hw hq0 hε hgap hbounds
        hg hgb τ Q hmin hη hηI hη0 hRadius hM hηM hηR).1
  have h5 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 5 scene).toReal) 2 P := by
    simpa only [D.originalRegularPieceAbsoluteTraffic_eq_region,hregular2,P] using
      (D.original_minimizer_regularBirth_rightPiece_memLp_two hF hw hq0 hε hgap hbounds
        hg hgb τ Q hmin hη hηI hη0 hRadius hM hηM hηR).1
  have h3 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 3 scene).toReal) 2 P := by
    simpa only [D.originalRegularPieceAbsoluteTraffic_eq_region,hregular1,P] using
      D.original_minimizer_regularOldPiece_memLp_two hF hw hε hgap hbounds
        hg hgb τ Q hmin hRadius hM hη hηI hη0 hηM hηR (i:=1) (Or.inl rfl)
  have h7 : MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε 7 scene).toReal) 2 P := by
    simpa only [D.originalRegularPieceAbsoluteTraffic_eq_region,hregular3,P] using
      D.original_minimizer_regularOldPiece_memLp_two hF hw hε hgap hbounds
        hg hgb τ Q hmin hRadius hM hη hηI hη0 hηM hηR (i:=3) (Or.inr rfl)
  have hregions (i : Fin 8) :
      MemLp (fun scene↦(D.originalSupportedClockRegionAbsoluteTraffic η ε i scene).toReal) 2 P := by
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
  have hsum : MemLp (fun scene↦∑i : Fin 8,
      (D.originalSupportedClockRegionAbsoluteTraffic η ε i scene).toReal) 2 P :=
    memLp_finsetSum Finset.univ (fun i _↦hregions i)
  have hreal : (fun scene↦(originalSeedCompletePathAbsoluteTraffic S w η scene).toReal) =ᵐ[P]
      (fun scene↦∑i : Fin 8,(D.originalSupportedClockRegionAbsoluteTraffic η ε i scene).toReal) :=
    D.ae_toReal_original_completePathAbsoluteTraffic_eq_sum_supportedRegions hF hw hbounds Q hη hηI hε
  have hfull := hsum.ae_eq (Filter.EventuallyEq.symm hreal)
  exact ⟨hfull,hfull.integrable_sq⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
