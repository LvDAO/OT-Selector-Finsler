import OTSelector.Reconstruction.FocalResidueScaleNormalization

/-!
# Actual original focal phase legs need no extra matrix lower-bound premise

The original endpoint residue scale supplies its own invertible square-root normalizer.
The actual whole original source/target legs then have a fixed positive identity lower
bound in those same phase coordinates. The kernel comparison is retained with the same
actual residue so the subsequent mobility estimate uses one coherent geometric witness.
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

/-- The actual original left focal phase has internally normalized full legs, with the
same true residue retained in its original kernel comparison. -/
theorem exists_original_left_focal_normalizedLegs
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
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         IsUnit T.det ∧
          (T*originalSeedClockCompliance S w a ((S.level:ℝ)+D.lo+t)*Tᵀ-(c/2)•1).PosSemidef ∧
          (T*originalSeedClockCompliance S w ((S.level:ℝ)+D.lo+t) b*Tᵀ-(c/2)•1).PosSemidef) := by
  obtain ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,hlegs⟩ :=
    D.exists_original_left_focal_fullLeg_scale hF hw
  refine ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,fun {t a b} ht htε ha hb hac hcb ↦ ?_⟩
  obtain ⟨hL,hR⟩ := hlegs ht htε ha hb hac hcb
  have hscale := focalResidueScale_posDef hG ht
  exact ⟨(positiveMatrixNormalizer_spec hscale).1,
    posSemidef_positiveMatrixNormalizer_congruence_lower hscale hL,
    posSemidef_positiveMatrixNormalizer_congruence_lower hscale hR⟩

/-- The actual original right focal phase has internally normalized full legs, with the
same true residue retained in its original kernel comparison. -/
theorem exists_original_right_focal_normalizedLegs
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
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         IsUnit T.det ∧
          (T*originalSeedClockCompliance S w a ((S.level:ℝ)+D.hi-t)*Tᵀ-(c/2)•1).PosSemidef ∧
          (T*originalSeedClockCompliance S w ((S.level:ℝ)+D.hi-t) b*Tᵀ-(c/2)•1).PosSemidef) := by
  obtain ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,hlegs⟩ :=
    D.exists_original_right_focal_fullLeg_scale hF hw
  refine ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,fun {t a b} ht htε ha hb hac hcb ↦ ?_⟩
  obtain ⟨hL,hR⟩ := hlegs ht htε ha hb hac hcb
  have hscale := focalResidueScale_posDef hG ht
  exact ⟨(positiveMatrixNormalizer_spec hscale).1,
    posSemidef_positiveMatrixNormalizer_congruence_lower hscale hL,
    posSemidef_positiveMatrixNormalizer_congruence_lower hscale hR⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
