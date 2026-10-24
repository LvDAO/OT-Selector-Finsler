import OTSelector.Reconstruction.OriginalOldFocalLegs
import OTSelector.Reconstruction.FinslerOriginalOldWindowTraffic
import OTSelector.Reconstruction.FinslerOriginalNormalizedMomentumEligibleNodes

/-! Genuine occupied old-focal windows internally give the original two clock
supports and both positive full compliance legs in the same focal frame. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped ENNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- Nonzero original occupied old windows retain their actual supported masks. -/
theorem originalSupportedOldPhysicalClockWeight_mask_ne_zero
    (ε cap : ℝ) (side : Fin 2) (n ell : ℕ)
    (z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ)
    (hz : D.originalSupportedOldPhysicalClockWeight ε cap side n ell z ≠ 0) :
    D.originalSupportedOldPhysicalClockMask ε cap side n ell z ≠ 0 :=
  (mul_ne_zero_iff.mp hz).2

/-- The actual occupied old left window supplies normalized node eligibility. -/
theorem originalSupportedLeftOldPhysicalClockWeight_eligible_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {ε cap geoε lower upper gap diameter : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap) (hcapU : cap ≤ 1 / 4)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hsmall : 8 * ε ≤ gap)
    (hgeo : geoε < D.hi - D.lo) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hcomp : ∀ v ∈ Ioo 0 geoε,
      (originalSeedKernel S w (D.lo + v) - lower • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
      (upper • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.lo + v)).PosSemidef)
    (n ell : ℕ) (hscale : 8 * birthDyadicShellScale ε n < geoε)
    (hell : ell < birthPhysicalClockWindowCount cap)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ)
    (hz : D.originalSupportedOldPhysicalClockWeight ε cap 0 n ell
      ((physicalPairAnchor e).2, clock) ≠ 0) :
    let T := positiveMatrixNormalizer (focalResidueScale G (birthDyadicShellScale ε n))
    let cut := D.originalOldPhysicalClockReference ε cap 0 n ell - S.level
    IsUnit T.det ∧ cut ∈ Ioo D.lo D.hi ∧
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut (lower / 64) := by
  let t := birthDyadicShellScale ε n
  let ref := D.originalOldPhysicalClockReference ε cap 0 n ell
  let T := positiveMatrixNormalizer (focalResidueScale G t)
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hwidth := (oldPhysicalClockWindow_spec hcap ht).2.1
  have hm := D.originalSupportedOldPhysicalClockWeight_mask_ne_zero ε cap 0 n ell _ hz
  have hs := D.originalSupportedOldPhysicalClockMask_support
    ε cap 0 n ell ((physicalPairAnchor e).2, clock) hm
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 2 _).mp hs.2.2.1
  have hn := D.originalSupportedOldPhysicalClockMask_left_nearLeg hε hcap hcapU
    n ell hell ((physicalPairAnchor e).2, clock) hm
  have hc := D.originalSupportedOldPhysicalClockMask_left_clock_mem
    ε cap n ell ((physicalPairAnchor e).2, clock) hm
  have hg := D.originalSupportedOldPhysicalClockMask_left_opposite_gap hbounds
    ε cap n ell ((physicalPairAnchor e).2, clock) hm
  dsimp only [physicalPairAnchor] at hs hr hn hc hg
  have href := D.originalOldPhysicalClockWindow_left_inward hε hcap n ell hell
    (c := ref) ⟨le_rfl, by linarith⟩
  have ha : e.1.2 - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith [hr.1], by linarith [hr.2.1, hr.2.2.1, hr.2.2.2.1]⟩
  have hb : e.2.2 - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith [hr.1, hr.2.2.1, hr.2.2.2.1], by linarith [hr.2.1]⟩
  have hhalf : 2 * t ≤ ε := by
    rw [show t = birthDyadicShellScale ε n from rfl, two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hfar : (S.level : ℝ) + D.lo + 8 * t ≤ e.2.2 := by
    change gap / 2 ≤ e.2.2 - ref at hg
    linarith [href.1]
  have hleg := D.original_left_old_focal_normalizedLegs_of_comparison hF hw hG hgeo
    hlower hupper hcomp ht hscale ha hb href hn.1 hfar
  have hsrc : e.1.2 ∈ D.sourcePhaseClocks (ref - S.level) := by
    exact ⟨ha.1, by change e.1.2 - S.level < ref - S.level; linarith [hn.1]⟩
  have htgt : e.2.2 ∈ D.targetPhaseClocks (ref - S.level) :=
    ⟨by change ref - S.level < e.2.2 - S.level; linarith [hc.1, hr.2.2.2.1], hb.2⟩
  refine ⟨hleg.1, ⟨hsrc.1.trans hsrc.2, htgt.1.trans htgt.2⟩,
    ⟨hsrc, htgt, hs.1, hs.2.1, ?_, ?_⟩⟩
  · change (T * D.sourcePhaseLeg (ref - S.level) e.1.2 * Tᵀ -
      (lower / 64) • 1).PosSemidef
    simpa only [sourcePhaseLeg, indicator_of_mem hsrc, originalSeedClockCompliance]
      using hleg.2.1
  · change (T * D.targetPhaseLeg (ref - S.level) e.2.2 * Tᵀ -
      (lower / 64) • 1).PosSemidef
    simpa only [targetPhaseLeg, indicator_of_mem htgt, originalSeedClockCompliance]
      using hleg.2.2

/-- The reflected original occupied old window supplies the same eligibility. -/
theorem originalSupportedRightOldPhysicalClockWeight_eligible_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {ε cap geoε lower upper gap diameter : ℝ}
    (hε : 0 < ε) (hcap : 0 < cap) (hcapU : cap ≤ 1 / 4)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) (hsmall : 8 * ε ≤ gap)
    (hgeo : geoε < D.hi - D.lo) (hlower : 0 ≤ lower) (hupper : 0 ≤ upper)
    (hcomp : ∀ v ∈ Ioo 0 geoε,
      (originalSeedKernel S w (D.hi - v) - lower • ((v ^ 2)⁻¹ • G + 1)).PosSemidef ∧
      (upper • ((v ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.hi - v)).PosSemidef)
    (n ell : ℕ) (hscale : 8 * birthDyadicShellScale ε n < geoε)
    (hell : ell < birthPhysicalClockWindowCount cap)
    (e : LegalMarkedPhysicalEdge (finrank ℝ S.covector.ker)) (clock : ℝ)
    (hz : D.originalSupportedOldPhysicalClockWeight ε cap 1 n ell
      ((physicalPairAnchor e).2, clock) ≠ 0) :
    let T := positiveMatrixNormalizer (focalResidueScale G (birthDyadicShellScale ε n))
    let cut := D.originalOldPhysicalClockReference ε cap 1 n ell - S.level
    IsUnit T.det ∧ cut ∈ Ioo D.lo D.hi ∧
      e ∈ D.normalizedMomentumPhaseEligibleEdges T cut (lower / 64) := by
  let t := birthDyadicShellScale ε n
  let ref := D.originalOldPhysicalClockReference ε cap 1 n ell
  let T := positiveMatrixNormalizer (focalResidueScale G t)
  have ht : 0 < t := birthDyadicShellScale_pos hε n
  have hwidth := (oldPhysicalClockWindow_spec hcap ht).2.1
  have hm := D.originalSupportedOldPhysicalClockWeight_mask_ne_zero ε cap 1 n ell _ hz
  have hs := D.originalSupportedOldPhysicalClockMask_support
    ε cap 1 n ell ((physicalPairAnchor e).2, clock) hm
  have hr := (originalClockTrafficRegionMask_ne_zero_iff _ _ ε 6 _).mp hs.2.2.1
  have hn := D.originalSupportedOldPhysicalClockMask_right_nearLeg hε hcap hcapU
    n ell hell ((physicalPairAnchor e).2, clock) hm
  have hc := D.originalSupportedOldPhysicalClockMask_right_clock_mem
    ε cap n ell ((physicalPairAnchor e).2, clock) hm
  have hg := D.originalSupportedOldPhysicalClockMask_right_opposite_gap hbounds
    ε cap n ell ((physicalPairAnchor e).2, clock) hm
  dsimp only [physicalPairAnchor] at hs hr hn hc hg
  have href := D.originalOldPhysicalClockWindow_right_inward hε hcap n ell hell
    (c := ref) ⟨by linarith, le_rfl⟩
  have ha : e.1.2 - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith [hr.1], by linarith [hr.2.1, hr.2.2.1, hr.2.2.2.1]⟩
  have hb : e.2.2 - S.level ∈ Ioo D.lo D.hi :=
    ⟨by linarith [hr.1, hr.2.2.1, hr.2.2.2.1], by linarith [hr.2.1]⟩
  have hhalf : 2 * t ≤ ε := by
    rw [show t = birthDyadicShellScale ε n from rfl, two_mul_birthDyadicShellScale]
    exact div_le_self hε.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
  have hfar : e.1.2 ≤ (S.level : ℝ) + D.hi - 8 * t := by
    change gap / 2 ≤ ref - e.1.2 at hg
    linarith [href.1]
  have hleg := D.original_right_old_focal_normalizedLegs_of_comparison hF hw hG hgeo
    hlower hupper hcomp ht hscale ha hb href hn.1 hfar
  have hsrc : e.1.2 ∈ D.sourcePhaseClocks (ref - S.level) :=
    ⟨ha.1, by change e.1.2 - S.level < ref - S.level; linarith [hr.2.2.1, hc.2]⟩
  have htgt : e.2.2 ∈ D.targetPhaseClocks (ref - S.level) := by
    exact ⟨by change ref - S.level < e.2.2 - S.level; linarith [hn.1], hb.2⟩
  refine ⟨hleg.1, ⟨hsrc.1.trans hsrc.2, htgt.1.trans htgt.2⟩,
    ⟨hsrc, htgt, hs.1, hs.2.1, ?_, ?_⟩⟩
  · change (T * D.sourcePhaseLeg (ref - S.level) e.1.2 * Tᵀ -
      (lower / 64) • 1).PosSemidef
    simpa only [sourcePhaseLeg, indicator_of_mem hsrc, originalSeedClockCompliance]
      using hleg.2.1
  · change (T * D.targetPhaseLeg (ref - S.level) e.2.2 * Tᵀ -
      (lower / 64) • 1).PosSemidef
    simpa only [targetPhaseLeg, indicator_of_mem htgt, originalSeedClockCompliance]
      using hleg.2.2

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
