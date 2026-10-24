import OTSelector.Reconstruction.OriginalRegularBirthGeometry

/-! The actual original Finsler kernel supplies scalar birth geometry on every
compact regular clock strip. Short legs may shrink to zero; only their elapsed
scale is normalized, and the original kernel and compliance stay unchanged. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual opposite leg has a uniform positive bound in the same scalar
birth frame, even at a focal source or target endpoint. Original separation
and the finite support span supply the constants internally. -/
theorem exists_original_regular_birth_oppositeLeg_lower
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap L : ℝ} (hgap : 0 < gap) (hL : 0 < L) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {a b s : ℝ}, 0 < s → s ≤ L → gap ≤ b - a →
      a - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      b - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      let T := positiveMatrixNormalizer (s • (1 : Matrix (Fin (finrank ℝ S.covector.ker))
        (Fin (finrank ℝ S.covector.ker)) ℝ))
      (T * originalSeedClockCompliance S w a b * Tᵀ - κ • 1).PosSemidef := by
  obtain ⟨c, hc, hwhole⟩ := D.exists_original_compliance_wholeSpan_length_lower hF hw
  refine ⟨c * gap / L, by positivity, ?_⟩
  intro a b s hs hsL hlen ha hb
  have hab : a ≤ b := by linarith
  have hcoef : (c * gap / L) * s ≤ (b - a) * c := by
    calc
      _ = (c * gap * s) / L := by ring
      _ ≤ _ := by
        apply (div_le_iff₀ hL).mpr
        have hgs : gap * s ≤ (b - a) * L :=
          (mul_le_mul_of_nonneg_left hsL hgap.le).trans
            (mul_le_mul_of_nonneg_right hlen hL.le)
        have h := mul_le_mul_of_nonneg_left hgs hc.le
        nlinarith only [h]
  have hleg := scalar_identity_lower_bound_mono hcoef (hwhole hab ha hb)
  have hleg' : (originalSeedClockCompliance S w a b -
      (c * gap / L) • (s • (1 : Matrix (Fin (finrank ℝ S.covector.ker))
        (Fin (finrank ℝ S.covector.ker)) ℝ))).PosSemidef := by
    convert hleg using 1
    module
  exact posSemidef_positiveMatrixNormalizer_congruence_lower
    (Matrix.PosDef.one.smul hs) hleg'

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
