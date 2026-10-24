import OTSelector.Reconstruction.OriginalBirthNormalizedRightLegs
import OTSelector.Reconstruction.OriginalFocalComplianceOperatorCurve

/-! # Birth-normalized original physical mobility and its whole clock curve -/
open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- A fixed actual residue comparison produces one uniform norm bound in all
canonical birth frames at the true left endpoint. -/
theorem original_left_birth_mobility_bound_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {ε C : ℝ} (hεspan : ε < D.hi - D.lo) (hC : 0 ≤ C)
    (hupper : ∀ r ∈ Ioo 0 ε,
      (C • ((r ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.lo + r)).PosSemidef) :
    ∃ B ≥ 0, ∀ {t s r : ℝ}, 0 < t → 0 < s → 4 * t < ε →
      r ∈ Icc (t / 2) (4 * t) →
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      ‖s • (T * originalSeedKernel S w (D.lo + r) * Tᵀ)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_birth_normalized_mobility
    (ι := Fin (finrank ℝ S.covector.ker)) C
  refine ⟨B, hB, fun {t s r} ht hs htε hr ↦ ?_⟩
  have hrε : r ∈ Ioo 0 ε := ⟨lt_of_lt_of_le (half_pos ht) hr.1, hr.2.trans_lt htε⟩
  have hrspan : D.lo + r ∈ Ioo D.lo D.hi := ⟨by linarith [hrε.1], by linarith [hrε.2]⟩
  exact hbound hG ((D.original_kernel_regular hF hw).2 _ hrspan).posSemidef
    ht hs hr hC (hupper r hrε)

/-- The same original bound holds in the canonical right-endpoint birth frames. -/
theorem original_right_birth_mobility_bound_of_comparison
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    (hG : G.PosSemidef) {ε C : ℝ} (hεspan : ε < D.hi - D.lo) (hC : 0 ≤ C)
    (hupper : ∀ r ∈ Ioo 0 ε,
      (C • ((r ^ 2)⁻¹ • G + 1) - originalSeedKernel S w (D.hi - r)).PosSemidef) :
    ∃ B ≥ 0, ∀ {t s r : ℝ}, 0 < t → 0 < s → 4 * t < ε →
      r ∈ Icc (t / 2) (4 * t) →
      let T := positiveMatrixNormalizer (birthResidueScale G t s)
      ‖s • (T * originalSeedKernel S w (D.hi - r) * Tᵀ)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ := exists_norm_bound_birth_normalized_mobility
    (ι := Fin (finrank ℝ S.covector.ker)) C
  refine ⟨B, hB, fun {t s r} ht hs htε hr ↦ ?_⟩
  have hrε : r ∈ Ioo 0 ε := ⟨lt_of_lt_of_le (half_pos ht) hr.1, hr.2.trans_lt htε⟩
  have hrspan : D.hi - r ∈ Ioo D.lo D.hi := ⟨by linarith [hrε.2], by linarith [hrε.1]⟩
  exact hbound hG ((D.original_kernel_regular hF hw).2 _ hrspan).posSemidef
    ht hs hr hC (hupper r hrε)

/-- Every actual left physical clock window inside the enlarged band inherits
its true compliance-curve norm and two-parameter speed bound at elapsed scale s. -/
theorem original_left_birth_complianceCurve_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {ε t s B cut ell : ℝ} (hεspan : ε < D.hi - D.lo) (ht : 0 < t)
    (hs : 0 < s) (htε : 4 * t < ε) (hB : 0 ≤ B)
    (hwindow : uIcc (cut - S.level) (cut - S.level + ell) ⊆
      Icc (D.lo + t / 2) (D.lo + 4 * t))
    (hbound : ∀ r ∈ Icc (t / 2) (4 * t),
      ‖s • (positiveMatrixNormalizer (birthResidueScale G t s) *
        originalSeedKernel S w (D.lo + r) *
        (positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)‖ ≤ B) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    originalNormalizedClockMobility S w T cut ell 0 = 0 ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ‖originalNormalizedClockMobility S w T cut ell r‖ ≤
        B * |ell| / s) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        ‖originalNormalizedClockMobility S w T cut ell r -
          originalNormalizedClockMobility S w T cut ell v‖ ≤ (B * |ell| / s) * |r - v| := by
  apply D.originalNormalizedClockMobility_bounds hF hw _ hs hB
  · intro r hr
    have hx := hwindow hr
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro r hr
    have hx := hwindow hr
    have hd : r - D.lo ∈ Icc (t / 2) (4 * t) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    simpa only [add_sub_cancel] using hbound (r - D.lo) hd

/-- Right physical clock windows have the same birth-scale operator bounds;
the clock orientation remains the original forward orientation. -/
theorem original_right_birth_complianceCurve_bounds
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {G : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ}
    {ε t s B cut ell : ℝ} (hεspan : ε < D.hi - D.lo) (ht : 0 < t)
    (hs : 0 < s) (htε : 4 * t < ε) (hB : 0 ≤ B)
    (hwindow : uIcc (cut - S.level) (cut - S.level + ell) ⊆
      Icc (D.hi - 4 * t) (D.hi - t / 2))
    (hbound : ∀ r ∈ Icc (t / 2) (4 * t),
      ‖s • (positiveMatrixNormalizer (birthResidueScale G t s) *
        originalSeedKernel S w (D.hi - r) *
        (positiveMatrixNormalizer (birthResidueScale G t s))ᵀ)‖ ≤ B) :
    let T := positiveMatrixNormalizer (birthResidueScale G t s)
    originalNormalizedClockMobility S w T cut ell 0 = 0 ∧
      (∀ r ∈ Icc (0 : ℝ) 1, ‖originalNormalizedClockMobility S w T cut ell r‖ ≤
        B * |ell| / s) ∧
      ∀ r ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        ‖originalNormalizedClockMobility S w T cut ell r -
          originalNormalizedClockMobility S w T cut ell v‖ ≤ (B * |ell| / s) * |r - v| := by
  apply D.originalNormalizedClockMobility_bounds hF hw _ hs hB
  · intro r hr
    have hx := hwindow hr
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · intro r hr
    have hx := hwindow hr
    have hd : D.hi - r ∈ Icc (t / 2) (4 * t) := ⟨by linarith [hx.2], by linarith [hx.1]⟩
    simpa only [sub_sub_cancel] using hbound (D.hi - r) hd

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
