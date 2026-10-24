import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthWindows
import OTSelector.Reconstruction.OriginalRegularBirthOppositeLeg

/-! Actual regular birth masks supply canonical scalar phase eligibility and a
uniform original short-leg upper bound on the unchanged original clocks. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker

/-- The literal regular source birth window produces its canonical eligibility
and bounded short source leg, uniformly over all original elapsed scales. -/
theorem exists_original_regularBirth_left_phaseEligibility_shortLegUpper
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ h U₀ : ℝ, 0 < h ∧ 0 < U₀ ∧ ∀ {cap : ℝ}, 0 < cap →
      ∀ n j i ell : ℕ, ell < birthPhysicalClockWindowCount cap →
      ∀ e : LegalMarkedPhysicalEdge qdim, ∀ clock : ℝ,
      D.originalRegularBirthWindowMask H ε cap 0 n j i ell ((physicalPairAnchor e).2,clock) ≠ 0 →
      let s := birthDyadicElapsedScale H n j
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
      let cut := D.originalLeftBirthPhysicalClockReference H cap n j i ell-S.level
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ∧
        (U₀ • 1 - T*D.sourcePhaseLeg cut e.1.2*Tᵀ).PosSemidef := by
  let d := min ε (min (gap/2) ((D.hi-D.lo)/4))
  have hd : 0 < d := lt_min hε (lt_min (half_pos hgap) (by linarith [D.support.lt]))
  have hdε : d ≤ ε := min_le_left _ _
  have hdgap : d ≤ gap/2 := (min_le_right _ _).trans (min_le_left _ _)
  let J := Icc (D.lo+d/2) (D.hi-d/2)
  have hJI : J ⊆ Ioo D.lo D.hi := by intro x hx; constructor <;> dsimp [J] at hx <;> linarith [hx.1,hx.2]
  obtain ⟨κ,C,hκ,hC,hshort⟩ := D.exists_original_regular_birth_shortLeg_bounds hF hw isCompact_Icc hJI
  obtain ⟨κopp,hκopp,hopp⟩ := D.exists_original_regular_birth_oppositeLeg_lower hF hw (half_pos hgap) hH
  let h := min (κ/2) κopp
  have hh : 0 < h := lt_min (half_pos hκ) hκopp
  refine ⟨h,4*C,hh,by positivity,?_⟩
  intro cap hcap n j i ell hell e clock hz
  dsimp only
  let z := ((physicalPairAnchor e).2,clock)
  change originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 1 z *
    D.originalSupportedLeftBirthPhysicalClockMask H cap n j i ell z ≠ 0 at hz
  have hr := left_ne_zero_of_mul hz
  have hm := right_ne_zero_of_mul hz
  have hsupport := D.originalSupportedLeftBirthPhysicalClockMask_support H cap n j i ell z hm
  have hbirth := (D.originalSupportedLeftBirthPhysicalClockMask_birth H cap n j i ell z hm).1
  have hbase := birthDyadicClockBand_base_bounds hH n j i
    (D.originalSupportedLeftBirthPhysicalClockMask_birth H cap n j i ell z hm).2
  let t := birthDyadicShellScale H n
  let s := birthDyadicElapsedScale H n j
  let ref := D.originalLeftBirthPhysicalClockReference H cap n j i ell
  let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
  have hs : 0 < s := hbase.1
  have hshorttime := D.originalSupportedLeftBirthPhysicalClockMask_reference_bounds hH hcap n j i ell z hm hell
  have hfar := D.originalSupportedLeftBirthPhysicalClockMask_opposite_gap hbounds H cap n j i ell z hm
  have hreg := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hr
  have hregular := (originalClockTrafficRegionIndex_eq_one_iff _ _ _ z).mp hreg.2.2.2.2
  have hsep := hbounds.separated _ hsupport.1 _ hsupport.2.1
  have hgaplen : gap ≤ z.1.1.2-z.1.1.1 := by
    simpa only [Real.dist_eq,abs_of_neg (sub_neg.mpr (hreg.2.2.1.trans hreg.2.2.2.1)),neg_sub] using hsep
  have hstrip := source_birthRegular_clock_strip hreg.2.1 hreg.2.2.1 hregular.1 hregular.2.2 hgaplen
  have haI : z.1.1.1-(S.level:ℝ) ∈ Ioo D.lo D.hi := by constructor <;> linarith [hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1]
  have hbI : z.1.1.2-(S.level:ℝ) ∈ Ioo D.lo D.hi := by constructor <;> linarith [hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1]
  have hrefI : ref-(S.level:ℝ) ∈ Ioo D.lo D.hi := by
    constructor <;> linarith [haI.1,hbI.2,hshorttime.2.1,hfar]
  have har : z.1.1.1 ≤ ref := by linarith [hshorttime.2.1]
  have hsub : Icc (z.1.1.1-(S.level:ℝ)) (ref-(S.level:ℝ)) ⊆ J := by
    intro v hv
    constructor <;> dsimp [J] at * <;> linarith [hv.1,hv.2,hstrip.2,hregular.2.2,hshorttime.1.1]
  have hshort' := hshort hs har hsub (by linarith [hshorttime.2.1]) (by linarith [hshorttime.2.2])
  have hsH : s ≤ H := by
    have htH : 2*t ≤ H := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hH.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [hbase.2.1]
  have hlong := hopp hs hsH hfar hrefI hbI
  have hleft := scalar_identity_lower_bound_mono (min_le_left (κ/2) κopp) hshort'.1
  have hright := scalar_identity_lower_bound_mono (min_le_right (κ/2) κopp) hlong
  have hasource : e.1.2 ∈ D.sourcePhaseClocks (ref-S.level) := by
    change e.1.2-(S.level:ℝ) ∈ Ioo D.lo (ref-S.level)
    change e.1.2-(S.level:ℝ) ∈ Ioo D.lo D.hi at haI
    have hshortL := hshorttime.2.1
    change 7/8*s ≤ ref-e.1.2 at hshortL
    exact ⟨haI.1,by linarith⟩
  have hbtarget : e.2.2 ∈ D.targetPhaseClocks (ref-S.level) := by
    change e.2.2-(S.level:ℝ) ∈ Ioo (ref-S.level) D.hi
    change e.2.2-(S.level:ℝ) ∈ Ioo D.lo D.hi at hbI
    change gap/2 ≤ e.2.2-ref at hfar
    exact ⟨by linarith,hbI.2⟩
  refine ⟨D.mem_normalizedMomentumPhaseEligibleEdges_of_clockCompliance T ref h e
    hasource hbtarget hsupport.1 hsupport.2.1 hleft hright,?_⟩
  change ((4*C) • 1 - T*D.sourcePhaseLeg (ref-S.level) e.1.2*Tᵀ).PosSemidef
  rw [sourcePhaseLeg,indicator_of_mem hasource]
  exact hshort'.2

/-- The reflected literal regular death window uses the original target
short leg and the unchanged forward physical clock in its canonical frame. -/
theorem exists_original_regularBirth_right_phaseEligibility_shortLegUpper
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {H ε gap diameter : ℝ} (hH : 0 < H) (hε : 0 < ε) (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) :
    ∃ h U₀ : ℝ, 0 < h ∧ 0 < U₀ ∧ ∀ {cap : ℝ}, 0 < cap →
      ∀ n j i ell : ℕ, ell < birthPhysicalClockWindowCount cap →
      ∀ e : LegalMarkedPhysicalEdge qdim, ∀ clock : ℝ,
      D.originalRegularBirthWindowMask H ε cap 1 n j i ell ((physicalPairAnchor e).2,clock) ≠ 0 →
      let s := birthDyadicElapsedScale H n j
      let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
      let cut := D.originalRightBirthPhysicalClockReference H cap n j i ell-S.level
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut h ∧
        (U₀ • 1 - T*D.targetPhaseLeg cut e.2.2*Tᵀ).PosSemidef := by
  let d := min ε (min (gap/2) ((D.hi-D.lo)/4))
  have hd : 0 < d := lt_min hε (lt_min (half_pos hgap) (by linarith [D.support.lt]))
  have hdε : d ≤ ε := min_le_left _ _
  have hdgap : d ≤ gap/2 := (min_le_right _ _).trans (min_le_left _ _)
  let J := Icc (D.lo+d/2) (D.hi-d/2)
  have hJI : J ⊆ Ioo D.lo D.hi := by intro x hx; constructor <;> dsimp [J] at hx <;> linarith [hx.1,hx.2]
  obtain ⟨κ,C,hκ,hC,hshort⟩ := D.exists_original_regular_birth_shortLeg_bounds hF hw isCompact_Icc hJI
  obtain ⟨κopp,hκopp,hopp⟩ := D.exists_original_regular_birth_oppositeLeg_lower hF hw (half_pos hgap) hH
  let h := min (κ/2) κopp
  have hh : 0 < h := lt_min (half_pos hκ) hκopp
  refine ⟨h,4*C,hh,by positivity,?_⟩
  intro cap hcap n j i ell hell e clock hz
  dsimp only
  let z := ((physicalPairAnchor e).2,clock)
  change originalClockTrafficRegionMask (D.lo+S.level) (D.hi+S.level) ε 5 z *
    D.originalSupportedRightBirthPhysicalClockMask H cap n j i ell z ≠ 0 at hz
  have hr := left_ne_zero_of_mul hz
  have hm := right_ne_zero_of_mul hz
  have hsupport := D.originalSupportedRightBirthPhysicalClockMask_support H cap n j i ell z hm
  have hbirth := (D.originalSupportedRightBirthPhysicalClockMask_birth H cap n j i ell z hm).1
  have hbase := birthDyadicClockBand_base_bounds hH n j i
    (D.originalSupportedRightBirthPhysicalClockMask_birth H cap n j i ell z hm).2
  let t := birthDyadicShellScale H n
  let s := birthDyadicElapsedScale H n j
  let ref := D.originalRightBirthPhysicalClockReference H cap n j i ell
  let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
  have hs : 0 < s := hbase.1
  have hshorttime := D.originalSupportedRightBirthPhysicalClockMask_reference_bounds hH hcap n j i ell z hm hell
  have hfar := D.originalSupportedRightBirthPhysicalClockMask_opposite_gap hbounds H cap n j i ell z hm
  have hreg := (originalClockTrafficRegionMask_ne_zero_iff _ _ _ _ _).mp hr
  have hregular := (originalClockTrafficRegionIndex_eq_five_iff _ _ _ z).mp hreg.2.2.2.2
  have hsep := hbounds.separated _ hsupport.1 _ hsupport.2.1
  have hgaplen : gap ≤ z.1.1.2-z.1.1.1 := by
    simpa only [Real.dist_eq,abs_of_neg (sub_neg.mpr (hreg.2.2.1.trans hreg.2.2.2.1)),neg_sub] using hsep
  have hstrip := target_birthRegular_clock_strip hreg.1 hreg.2.2.2.1 hregular.1.le hregular.2.2 hgaplen
  have haI : z.1.1.1-(S.level:ℝ) ∈ Ioo D.lo D.hi := by constructor <;> linarith [hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1]
  have hbI : z.1.1.2-(S.level:ℝ) ∈ Ioo D.lo D.hi := by constructor <;> linarith [hreg.1,hreg.2.1,hreg.2.2.1,hreg.2.2.2.1]
  have hrefI : ref-(S.level:ℝ) ∈ Ioo D.lo D.hi := by
    constructor <;> linarith [haI.1,hbI.2,hshorttime.2.1,hfar]
  have hrb : ref ≤ z.1.1.2 := by linarith [hshorttime.2.1]
  have hsub : Icc (ref-(S.level:ℝ)) (z.1.1.2-(S.level:ℝ)) ⊆ J := by
    intro v hv
    constructor <;> dsimp [J] at * <;> linarith [hv.1,hv.2,hstrip.1,hregular.2.2,hshorttime.1.2]
  have hshort' := hshort hs hrb hsub (by linarith [hshorttime.2.1]) (by linarith [hshorttime.2.2])
  have hsH : s ≤ H := by
    have htH : 2*t ≤ H := by
      rw [two_mul_birthDyadicShellScale]
      exact div_le_self hH.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
    linarith [hbase.2.1]
  have hlong := hopp hs hsH hfar haI hrefI
  have hleft := scalar_identity_lower_bound_mono (min_le_right (κ/2) κopp) hlong
  have hright := scalar_identity_lower_bound_mono (min_le_left (κ/2) κopp) hshort'.1
  have hasource : e.1.2 ∈ D.sourcePhaseClocks (ref-S.level) := by
    change e.1.2-(S.level:ℝ) ∈ Ioo D.lo (ref-S.level)
    change e.1.2-(S.level:ℝ) ∈ Ioo D.lo D.hi at haI
    change gap/2 ≤ ref-e.1.2 at hfar
    exact ⟨haI.1,by linarith⟩
  have hbtarget : e.2.2 ∈ D.targetPhaseClocks (ref-S.level) := by
    change e.2.2-(S.level:ℝ) ∈ Ioo (ref-S.level) D.hi
    change e.2.2-(S.level:ℝ) ∈ Ioo D.lo D.hi at hbI
    have hshortL := hshorttime.2.1
    change 7/8*s ≤ e.2.2-ref at hshortL
    exact ⟨by linarith,hbI.2⟩
  refine ⟨D.mem_normalizedMomentumPhaseEligibleEdges_of_clockCompliance T ref h e
    hasource hbtarget hsupport.1 hsupport.2.1 hleft hright,?_⟩
  change ((4*C) • 1 - T*D.targetPhaseLeg (ref-S.level) e.2.2*Tᵀ).PosSemidef
  rw [targetPhaseLeg,indicator_of_mem hbtarget]
  exact hshort'.2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
