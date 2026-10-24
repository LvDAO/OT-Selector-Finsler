import OTSelector.Reconstruction.FinslerOriginalNormalizedCompletePathContributors
import OTSelector.Reconstruction.FinslerNormalizedPhaseCurveWindowMeasurability
import OTSelector.Reconstruction.CommonPhysicalNormalizedPhaseWindow

/-! Genuine original Finsler endpoint data determines a contractive normalized
clock window and its jointly Borel same-scene canonical phase curve. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original left endpoint chooses its actual frame, short clock fraction,
contractivity certificate, and Borel canonical curve internally. -/
theorem exists_original_left_contractive_normalized_phaseWindow
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧
      ∃ A : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      A.PosSemidef ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ {a h : ℝ}, 0 < a → 2 * a < ε → 0 < h →
        (let T := positiveMatrixNormalizer (focalResidueScale A a)
         let cut := D.lo + a
         let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
         let σ := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
         let R := originalNormalizedClockMobility S w T (cut + S.level) (σ * a)
         ∃ hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ),
           (∀ r ∈ Icc (0 : ℝ) 1, cut + (σ * a) * r ∈ Ioo D.lo D.hi) ∧
           R 0 = 0 ∧
           (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ σ * B) ∧
           (∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
             ‖R r - R r'‖ ≤ (σ * B) * |r - r'|) ∧
           Measurable (fun b : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
             D.normalizedMomentumPhaseCurvePair T cut h L R hsmall b.1 b.2)) := by
  obtain ⟨ε, hε, hεh, A, hA, B, hB, hmob⟩ :=
    D.exists_original_left_focal_complianceCurve_bounds hF hw
  refine ⟨ε, hε, hεh, A, hA, B, hB, ?_⟩
  intro a h ha haε hh
  dsimp only
  let T := positiveMatrixNormalizer (focalResidueScale A a)
  let cut := D.lo + a
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let σ := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
  let R := originalNormalizedClockMobility S w T (cut + S.level) (σ * a)
  have hσ := commonPhysicalNormalizedWindowFraction_spec hcap hB L.coe_nonneg
  have hscale : cut + S.level = S.level + D.lo + a := by dsimp [cut]; ring
  have hm : R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ σ * B) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
        ‖R r - R r'‖ ≤ (σ * B) * |r - r'| := by
    simpa only [R, T, hscale] using hmob ha haε hσ.1.le hσ.2.1
  have hs : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ) :=
    commonPhysicalNormalizedWindowFraction_contractive hcap hB L.coe_nonneg hm.2.1
  have hcut : cut ∈ Ioo D.lo D.hi := by dsimp [cut]; constructor <;> linarith
  refine ⟨hs, ?_, hm.1, hm.2.1, hm.2.2, ?_⟩
  · intro r hr
    have hlo : 0 ≤ σ * a * r := mul_nonneg (mul_nonneg hσ.1.le ha.le) hr.1
    have hhi : σ * a * r ≤ a / 2 := by
      calc
        σ * a * r ≤ σ * a := mul_le_of_le_one_right (mul_nonneg hσ.1.le ha.le) hr.2
        _ ≤ a / 2 := by nlinarith [hσ.2.1]
    constructor <;> linarith
  · exact D.measurable_normalizedMomentumPhaseCurvePair_of_lipschitzOn T hF hw hcut h L R
      (mul_nonneg hσ.1.le hB) hm.2.2 hs

/-- The actual right endpoint has the same internal construction, with the
physical clock reversed and the original normalized momentum unchanged. -/
theorem exists_original_right_contractive_normalized_phaseWindow
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {cap : ℝ} (hcap : 0 < cap) :
    ∃ ε : ℝ, 0 < ε ∧ ε < D.hi - D.lo ∧
      ∃ A : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      A.PosSemidef ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ {a h : ℝ}, 0 < a → 2 * a < ε → 0 < h →
        (let T := positiveMatrixNormalizer (focalResidueScale A a)
         let cut := D.hi - a
         let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
         let σ := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
         let R := originalNormalizedClockMobility S w T (cut + S.level) (-σ * a)
         ∃ hsmall : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ),
           (∀ r ∈ Icc (0 : ℝ) 1, cut + (-σ * a) * r ∈ Ioo D.lo D.hi) ∧
           R 0 = 0 ∧
           (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ σ * B) ∧
           (∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
             ‖R r - R r'‖ ≤ (σ * B) * |r - r'|) ∧
           Measurable (fun b : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) × ℝ ↦
             D.normalizedMomentumPhaseCurvePair T cut h L R hsmall b.1 b.2)) := by
  obtain ⟨ε, hε, hεh, A, hA, B, hB, hmob⟩ :=
    D.exists_original_right_focal_complianceCurve_bounds hF hw
  refine ⟨ε, hε, hεh, A, hA, B, hB, ?_⟩
  intro a h ha haε hh
  dsimp only
  let T := positiveMatrixNormalizer (focalResidueScale A a)
  let cut := D.hi - a
  let L : ℝ≥0 := ⟨Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2), Real.sqrt_nonneg _⟩
  let σ := commonPhysicalNormalizedWindowFraction cap B (L : ℝ)
  let R := originalNormalizedClockMobility S w T (cut + S.level) (-σ * a)
  have hσ := commonPhysicalNormalizedWindowFraction_spec hcap hB L.coe_nonneg
  have hscale : cut + S.level = S.level + D.hi - a := by dsimp [cut]; ring
  have hm : R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ σ * B) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ r' ∈ Icc (0 : ℝ) 1,
        ‖R r - R r'‖ ≤ (σ * B) * |r - r'| := by
    simpa only [R, T, hscale] using hmob ha haε hσ.1.le hσ.2.1
  have hs : ∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ * (L : ℝ) ≤ (1 / 2 : ℝ) :=
    commonPhysicalNormalizedWindowFraction_contractive hcap hB L.coe_nonneg hm.2.1
  have hcut : cut ∈ Ioo D.lo D.hi := by dsimp [cut]; constructor <;> linarith
  refine ⟨hs, ?_, hm.1, hm.2.1, hm.2.2, ?_⟩
  · intro r hr
    have hlo : 0 ≤ σ * a * r := mul_nonneg (mul_nonneg hσ.1.le ha.le) hr.1
    have hhi : σ * a * r ≤ a / 2 := by
      calc
        σ * a * r ≤ σ * a := mul_le_of_le_one_right (mul_nonneg hσ.1.le ha.le) hr.2
        _ ≤ a / 2 := by nlinarith [hσ.2.1]
    constructor <;> nlinarith
  · exact D.measurable_normalizedMomentumPhaseCurvePair_of_lipschitzOn T hF hw hcut h L R
      (mul_nonneg hσ.1.le hB) hm.2.2 hs

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
