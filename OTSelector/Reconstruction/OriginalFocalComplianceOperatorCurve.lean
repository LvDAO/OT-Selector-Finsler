import OTSelector.Reconstruction.NormalizedComplianceOperatorCurve

/-!
# Actual Finsler focal compliance curves

The original Finsler geometry internally supplies a single focal residue and its
normalizing frame. In this same frame the unchanged physical compliance on any
short relative clock window is uniformly small and Lipschitz.
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
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The actual physical-clock compliance in one fixed normalized phase frame. -/
def originalNormalizedClockMobility (S : CalibratedLevelSeedPatch F u) (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (c ell r : ℝ) : (Fin (finrank ℝ S.covector.ker) → ℝ) →L[ℝ]
      (Fin (finrank ℝ S.covector.ker) → ℝ) :=
  matrixPhaseOperator (T * originalSeedClockCompliance S w c (c + ell * r) * Tᵀ)

/-- This is exactly the original kernel integral; translating the clock changes no cost. -/
theorem originalNormalizedClockMobility_eq (S : CalibratedLevelSeedPatch F u)
    (w : S.covector.ker)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    (c ell r : ℝ) :
    originalNormalizedClockMobility S w T c ell r =
      normalizedComplianceOperatorCurve (originalSeedKernel S w) T (c - S.level) ell r := by
  unfold originalNormalizedClockMobility normalizedComplianceOperatorCurve
    normalizedComplianceCurve originalSeedClockCompliance
  rw [show c + ell * r - S.level = (c - S.level) + ell * r by ring]

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Actual original regularity transfers the scaled kernel bound to the whole physical curve. -/
theorem originalNormalizedClockMobility_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {c ell t B : ℝ} (ht : 0 < t) (hB : 0 ≤ B)
    (hclock : uIcc (c - S.level) (c - S.level + ell) ⊆ Ioo D.lo D.hi)
    (hbound : ∀ v ∈ uIcc (c - S.level) (c - S.level + ell),
      ‖t • (T * originalSeedKernel S w v * Tᵀ)‖ ≤ B) :
    originalNormalizedClockMobility S w T c ell 0 = 0 ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ‖originalNormalizedClockMobility S w T c ell r‖ ≤
        B * |ell| / t) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
        ‖originalNormalizedClockMobility S w T c ell r -
          originalNormalizedClockMobility S w T c ell s‖ ≤
            (B * |ell| / t) * |r - s| := by
  simp_rw [originalNormalizedClockMobility_eq]
  exact normalizedComplianceOperatorCurve_bounds _ T ht hB
    ((D.original_kernel_regular hF hw).1.mono hclock) hbound

/-- The original left endpoint supplies actual physical mobility curves with uniform speed. -/
theorem exists_original_left_focal_complianceCurve_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ ε : ℝ, ε > 0 ∧ ε < D.hi - D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ B : ℝ, B ≥ 0 ∧
      ∀ {t σ : ℝ}, 0 < t → 2 * t < ε → 0 ≤ σ → σ ≤ 1 / 2 →
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         let R := originalNormalizedClockMobility S w T (S.level + D.lo + t) (σ * t)
         R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ σ * B) ∧
           ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
             ‖R r - R s‖ ≤ (σ * B) * |r - s|) := by
  obtain ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,B,hB,hbound,hlegs⟩ :=
    D.exists_original_left_focal_normalizedPhaseBounds hF hw
  refine ⟨ε,hε,hεh,G,hG,B,hB,?_⟩
  intro t σ ht htε hσ hσhalf
  let T := positiveMatrixNormalizer (focalResidueScale G t)
  have hσt : 0 ≤ σ * t := mul_nonneg hσ ht.le
  have hclock : uIcc ((S.level + D.lo + t) - S.level)
      ((S.level + D.lo + t) - S.level + σ * t) ⊆ Ioo D.lo D.hi := by
    rw [uIcc_of_le (by linarith)]
    intro v hv
    constructor <;> nlinarith [hv.1, hv.2]
  have hmob : ∀ v ∈ uIcc ((S.level + D.lo + t) - S.level)
      ((S.level + D.lo + t) - S.level + σ * t),
      ‖t • (T * originalSeedKernel S w v * Tᵀ)‖ ≤ B := by
    intro v hv
    rw [uIcc_of_le (by linarith)] at hv
    have hvband : v - D.lo ∈ Icc (t / 2) (2 * t) := by
      constructor <;> nlinarith [hv.1, hv.2]
    have hh := (hbound ht htε hvband).1
    simpa only [T, add_sub_cancel] using hh
  have hh := D.originalNormalizedClockMobility_bounds hF hw T ht hB hclock hmob
  have hscale : B * |σ * t| / t = σ * B := by
    rw [abs_of_nonneg hσt]
    field_simp
  simpa only [hscale] using hh

/-- The original right endpoint gives the same bound with its actual reversed clock. -/
theorem exists_original_right_focal_complianceCurve_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ ε : ℝ, ε > 0 ∧ ε < D.hi - D.lo ∧
      ∃ G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ,
      G.PosSemidef ∧ ∃ B : ℝ, B ≥ 0 ∧
      ∀ {t σ : ℝ}, 0 < t → 2 * t < ε → 0 ≤ σ → σ ≤ 1 / 2 →
        (let T := positiveMatrixNormalizer (focalResidueScale G t)
         let R := originalNormalizedClockMobility S w T (S.level + D.hi - t) (-σ * t)
         R 0 = 0 ∧ (∀ r ∈ Icc (0 : ℝ) 1, ‖R r‖ ≤ σ * B) ∧
           ∀ r ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1,
             ‖R r - R s‖ ≤ (σ * B) * |r - s|) := by
  obtain ⟨ε,hε,hεh,G,hG,c,hc,C,hC,hcomp,B,hB,hbound,hlegs⟩ :=
    D.exists_original_right_focal_normalizedPhaseBounds hF hw
  refine ⟨ε,hε,hεh,G,hG,B,hB,?_⟩
  intro t σ ht htε hσ hσhalf
  let T := positiveMatrixNormalizer (focalResidueScale G t)
  have hσt : 0 ≤ σ * t := mul_nonneg hσ ht.le
  have hclock : uIcc ((S.level + D.hi - t) - S.level)
      ((S.level + D.hi - t) - S.level + -σ * t) ⊆ Ioo D.lo D.hi := by
    rw [uIcc_of_ge (by nlinarith)]
    intro v hv
    constructor <;> nlinarith [hv.1, hv.2]
  have hmob : ∀ v ∈ uIcc ((S.level + D.hi - t) - S.level)
      ((S.level + D.hi - t) - S.level + -σ * t),
      ‖t • (T * originalSeedKernel S w v * Tᵀ)‖ ≤ B := by
    intro v hv
    rw [uIcc_of_ge (by nlinarith)] at hv
    have hvband : D.hi - v ∈ Icc (t / 2) (2 * t) := by
      constructor <;> nlinarith [hv.1, hv.2]
    have hh := (hbound ht htε hvband).1
    simpa only [T, sub_sub_cancel] using hh
  have hh := D.originalNormalizedClockMobility_bounds hF hw T ht hB hclock hmob
  have hscale : B * |-σ * t| / t = σ * B := by
    rw [neg_mul, abs_neg, abs_of_nonneg hσt]
    field_simp
  simpa only [hscale] using hh

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
