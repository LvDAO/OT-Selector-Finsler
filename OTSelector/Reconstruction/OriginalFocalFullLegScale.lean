import OTSelector.Reconstruction.FocalPoleComplianceLegs
import OTSelector.Reconstruction.RegularClockLegLowerBound

/-!
# Original full focal legs inherit the actual residue scale

The actual short inward-distance legs are identified with the unchanged original physical
clock compliances. Genuine positivity of the removed end pieces then gives the same scale
for the entire original legs, even when their other endpoints lie outside the focal collar.
All pole, comparison and leg constants are internally produced from the original geometry.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

/-- Translation to the original left inward clock preserves the actual compliance. -/
theorem originalSeedClockCompliance_leftFocal_integral
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (lo a b : ℝ) :
    (∫r in a..b, originalSeedKernel S w (lo+r)) =
      originalSeedClockCompliance S w ((S.level:ℝ)+lo+a) ((S.level:ℝ)+lo+b) := by
  unfold originalSeedClockCompliance
  rw [intervalIntegral.integral_comp_add_left (originalSeedKernel S w)]
  congr 1 <;> ring

/-- Reversal to the original right inward clock preserves the forward actual compliance. -/
theorem originalSeedClockCompliance_rightFocal_integral
    (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker) (hi a b : ℝ) :
    (∫r in a..b, originalSeedKernel S w (hi-r)) =
      originalSeedClockCompliance S w ((S.level:ℝ)+hi-b) ((S.level:ℝ)+hi-a) := by
  unfold originalSeedClockCompliance
  rw [intervalIntegral.integral_comp_sub_left (originalSeedKernel S w)]
  congr 1 <;> ring

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The true full original legs across a left focal cut internally share the actual
scale `tI+t⁻¹G`, with no added normalized-leg or endpoint nondegeneracy hypothesis. -/
theorem exists_original_left_focal_fullLeg_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧
      (∀s∈Ioo 0 ε,
        (originalSeedKernel S w (D.lo+s)-c•((s^2)⁻¹•G+1)).PosSemidef ∧
        (C•((s^2)⁻¹•G+1)-originalSeedKernel S w (D.lo+s)).PosSemidef) ∧
      ∀{t a b : ℝ}, 0<t → 2*t<ε →
        a-(S.level:ℝ)∈Ioo D.lo D.hi → b-(S.level:ℝ)∈Ioo D.lo D.hi →
        a≤(S.level:ℝ)+D.lo+t/2 → (S.level:ℝ)+D.lo+2*t≤b →
        (originalSeedClockCompliance S w a ((S.level:ℝ)+D.lo+t)-
          (c/2)•(t•1+t⁻¹•G)).PosSemidef ∧
        (originalSeedClockCompliance S w ((S.level:ℝ)+D.lo+t) b-
          (c/2)•(t•1+t⁻¹•G)).PosSemidef := by
  obtain ⟨ε,hε,hεh,G,R,hG,hR,hpole,c,hc,C,hC,hcomp⟩ :=
    D.exists_original_kernel_left_pole_loewner_comparison hF hw
  have hW : ContinuousOn (fun s ↦ originalSeedKernel S w (D.lo+s)) (Ioo 0 ε) :=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_const.add continuousOn_id)
      (fun s hs ↦ ⟨by linarith [hs.1],by linarith [hs.2]⟩)
  refine ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,fun {t a b} ht htε ha hb hac hcb ↦ ?_⟩
  obtain ⟨hL,hR⟩ := focal_positivePole_two_shortLeg_lower hc hG ht htε hW
    (fun s hs ↦ (hcomp s hs).1)
  rw [originalSeedClockCompliance_leftFocal_integral] at hL hR
  have hcut : ((S.level:ℝ)+D.lo+t)-(S.level:ℝ)∈Ioo D.lo D.hi :=
    ⟨by linarith,by linarith⟩
  have hdiffL := D.original_compliance_subsegment_posSemidef hF hw ha hcut hac
    (show (S.level:ℝ)+D.lo+t/2≤(S.level:ℝ)+D.lo+t by linarith) le_rfl
  have hdiffR := D.original_compliance_subsegment_posSemidef hF hw hcut hb le_rfl
    (show (S.level:ℝ)+D.lo+t≤(S.level:ℝ)+D.lo+2*t by linarith) hcb
  constructor
  · convert hdiffL.add hL using 1
    abel
  · convert hdiffR.add hR using 1
    abel

/-- The corresponding right focal cut uses its actual inward distance and the same
positive scale on the unchanged original forward source and target legs. -/
theorem exists_original_right_focal_fullLeg_scale
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧
      (∀s∈Ioo 0 ε,
        (originalSeedKernel S w (D.hi-s)-c•((s^2)⁻¹•G+1)).PosSemidef ∧
        (C•((s^2)⁻¹•G+1)-originalSeedKernel S w (D.hi-s)).PosSemidef) ∧
      ∀{t a b : ℝ}, 0<t → 2*t<ε →
        a-(S.level:ℝ)∈Ioo D.lo D.hi → b-(S.level:ℝ)∈Ioo D.lo D.hi →
        a≤(S.level:ℝ)+D.hi-2*t → (S.level:ℝ)+D.hi-t/2≤b →
        (originalSeedClockCompliance S w a ((S.level:ℝ)+D.hi-t)-
          (c/2)•(t•1+t⁻¹•G)).PosSemidef ∧
        (originalSeedClockCompliance S w ((S.level:ℝ)+D.hi-t) b-
          (c/2)•(t•1+t⁻¹•G)).PosSemidef := by
  obtain ⟨ε,hε,hεh,G,R,hG,hR,hpole,c,hc,C,hC,hcomp⟩ :=
    D.exists_original_kernel_right_pole_loewner_comparison hF hw
  have hW : ContinuousOn (fun s ↦ originalSeedKernel S w (D.hi-s)) (Ioo 0 ε) :=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_const.sub continuousOn_id)
      (fun s hs ↦ ⟨by linarith [hs.2],by linarith [hs.1]⟩)
  refine ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,fun {t a b} ht htε ha hb hac hcb ↦ ?_⟩
  obtain ⟨hR,hL⟩ := focal_positivePole_two_shortLeg_lower hc hG ht htε hW
    (fun s hs ↦ (hcomp s hs).1)
  rw [originalSeedClockCompliance_rightFocal_integral] at hL hR
  have hcut : ((S.level:ℝ)+D.hi-t)-(S.level:ℝ)∈Ioo D.lo D.hi :=
    ⟨by linarith,by linarith⟩
  have hdiffL := D.original_compliance_subsegment_posSemidef hF hw ha hcut hac
    (show (S.level:ℝ)+D.hi-2*t≤(S.level:ℝ)+D.hi-t by linarith) le_rfl
  have hdiffR := D.original_compliance_subsegment_posSemidef hF hw hcut hb le_rfl
    (show (S.level:ℝ)+D.hi-t≤(S.level:ℝ)+D.hi-t/2 by linarith) hcb
  constructor
  · convert hdiffL.add hL using 1
    abel
  · convert hdiffR.add hR using 1
    abel

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
