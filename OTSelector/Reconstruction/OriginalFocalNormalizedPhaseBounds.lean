import OTSelector.Reconstruction.OriginalFocalNormalizedLegs
import OTSelector.Reconstruction.FocalNormalizedMobility

/-!
# Coherent original focal full-leg and mobility estimates

The original Finsler data produces one actual residue and one phase frame at each inward
scale. True full source/target legs have a uniform positive lower bound in that frame,
and the actual kernel has a uniform scaled norm bound throughout the same dyadic band.
-/
open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M→ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual left Finsler endpoint supplies one coherent normalized phase frame. -/
theorem exists_original_left_focal_normalizedPhaseBounds
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧
      (∀s∈Ioo 0 ε,
        (originalSeedKernel S w (D.lo+s)-c•((s^2)⁻¹•G+1)).PosSemidef ∧
        (C•((s^2)⁻¹•G+1)-originalSeedKernel S w (D.lo+s)).PosSemidef) ∧
      ∃ B : ℝ, B≥0 ∧
      (∀{t s : ℝ}, 0<t → 2*t<ε → s∈Icc (t/2) (2*t) →
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         ‖t•(T*originalSeedKernel S w (D.lo+s)*Tᵀ)‖≤B ∧
         ‖s•(T*originalSeedKernel S w (D.lo+s)*Tᵀ)‖≤2*B)) ∧
      ∀{t a b : ℝ}, 0<t → 2*t<ε →
        a-(S.level:ℝ)∈Ioo D.lo D.hi → b-(S.level:ℝ)∈Ioo D.lo D.hi →
        a≤(S.level:ℝ)+D.lo+t/2 → (S.level:ℝ)+D.lo+2*t≤b →
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         IsUnit T.det ∧
          (T*originalSeedClockCompliance S w a ((S.level:ℝ)+D.lo+t)*Tᵀ-(c/2)•1).PosSemidef ∧
          (T*originalSeedClockCompliance S w ((S.level:ℝ)+D.lo+t) b*Tᵀ-(c/2)•1).PosSemidef) := by
  obtain ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,hlegs⟩ :=
    D.exists_original_left_focal_normalizedLegs hF hw
  obtain ⟨B,hB,hbound⟩ := exists_norm_bound_focal_normalized_mobility
    (ι:=Fin (finrank ℝ S.covector.ker)) C
  refine ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,B,hB,?_,hlegs⟩
  intro t s ht htε hs
  have hsε : s∈Ioo 0 ε := ⟨lt_of_lt_of_le (half_pos ht) hs.1,hs.2.trans_lt htε⟩
  have hW := ((D.original_kernel_regular hF hw).2 (D.lo+s)
    (show D.lo+s∈Ioo D.lo D.hi from ⟨by linarith [hs.1],by linarith [hs.2]⟩)).posSemidef
  have hb := hbound hG hW ht hs.1 hC.le (hcomp s hsε).2
  exact ⟨hb,norm_smul_le_two_mul_of_dyadic_band ht hsε.1.le hs.2 hb⟩


/-- The actual right Finsler endpoint supplies one coherent normalized phase frame. -/
theorem exists_original_right_focal_normalizedPhaseBounds
    (hF : F.IsSmoothStronglyConvex) (hw : w∈S.labels) :
    ∃ ε : ℝ, ε>0 ∧ ε<D.hi-D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ c : ℝ, c>0 ∧ ∃ C : ℝ, C>0 ∧
      (∀s∈Ioo 0 ε,
        (originalSeedKernel S w (D.hi-s)-c•((s^2)⁻¹•G+1)).PosSemidef ∧
        (C•((s^2)⁻¹•G+1)-originalSeedKernel S w (D.hi-s)).PosSemidef) ∧
      ∃ B : ℝ, B≥0 ∧
      (∀{t s : ℝ}, 0<t → 2*t<ε → s∈Icc (t/2) (2*t) →
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         ‖t•(T*originalSeedKernel S w (D.hi-s)*Tᵀ)‖≤B ∧
         ‖s•(T*originalSeedKernel S w (D.hi-s)*Tᵀ)‖≤2*B)) ∧
      ∀{t a b : ℝ}, 0<t → 2*t<ε →
        a-(S.level:ℝ)∈Ioo D.lo D.hi → b-(S.level:ℝ)∈Ioo D.lo D.hi →
        a≤(S.level:ℝ)+D.hi-2*t → (S.level:ℝ)+D.hi-t/2≤b →
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         IsUnit T.det ∧
          (T*originalSeedClockCompliance S w a ((S.level:ℝ)+D.hi-t)*Tᵀ-(c/2)•1).PosSemidef ∧
          (T*originalSeedClockCompliance S w ((S.level:ℝ)+D.hi-t) b*Tᵀ-(c/2)•1).PosSemidef) := by
  obtain ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,hlegs⟩ :=
    D.exists_original_right_focal_normalizedLegs hF hw
  obtain ⟨B,hB,hbound⟩ := exists_norm_bound_focal_normalized_mobility
    (ι:=Fin (finrank ℝ S.covector.ker)) C
  refine ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,B,hB,?_,hlegs⟩
  intro t s ht htε hs
  have hsε : s∈Ioo 0 ε := ⟨lt_of_lt_of_le (half_pos ht) hs.1,hs.2.trans_lt htε⟩
  have hW := ((D.original_kernel_regular hF hw).2 (D.hi-s)
    (show D.hi-s∈Ioo D.lo D.hi from ⟨by linarith [hs.2],by linarith [hs.1]⟩)).posSemidef
  have hb := hbound hG hW ht hs.1 hC.le (hcomp s hsε).2
  exact ⟨hb,norm_smul_le_two_mul_of_dyadic_band ht hsε.1.le hs.2 hb⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
