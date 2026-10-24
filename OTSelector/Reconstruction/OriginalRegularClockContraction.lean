import OTSelector.Reconstruction.OriginalFocalComplianceOperatorCurve

/-! The original supported old/regular clock mask internally supplies the exact
canonical phase eligibility used by the actual minimizer field. Original
source/target support separation gives the clock gap, and both compliance legs
are the unchanged original legs in the identity frame. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- Compact regular geometry internally supplies one physical clock-window
size for the actual canonical phase contraction, uniformly over reference
clocks. The original compliance curve is used without a model replacement. -/
theorem exists_original_regular_identityClock_contraction
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) (h : ℝ) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ ∀ {cut ell : ℝ}, |ell| ≤ δ →
      uIcc cut (cut + ell) ⊆ J →
      originalNormalizedClockMobility S w 1 (cut + S.level) ell 0 = 0 ∧
      (∀ r ∈ Icc (0 : ℝ) 1, cut + ell * r ∈ Ioo D.lo D.hi) ∧
      (∀ r ∈ Icc (0 : ℝ) 1,
        ‖originalNormalizedClockMobility S w 1 (cut + S.level) ell r‖ ≤ ρ) ∧
      ∀ r ∈ Icc (0 : ℝ) 1,
        ‖originalNormalizedClockMobility S w 1 (cut + S.level) ell r‖ *
          Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2) ≤ (1 / 2 : ℝ) := by
  have hW := (D.original_kernel_regular hF hw).1.mono hJI
  obtain ⟨C, hC⟩ := hJ.exists_bound_of_continuousOn hW
  let B := max C 1
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let L := Real.sqrt ((finrank ℝ S.covector.ker : ℝ) / h ^ 2)
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  let ρ := 1 / (2 * (L + 1))
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρL : ρ * L ≤ (1 / 2 : ℝ) := by
    dsimp [ρ]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (show 0 < 2 * (L + 1) by positivity)).mpr
    nlinarith
  refine ⟨ρ / B, ρ, div_pos hρ hB, hρ, ?_⟩
  intro cut ell hell hsub
  have hclock : uIcc ((cut + (S.level : ℝ)) - S.level)
      ((cut + S.level) - S.level + ell) ⊆ Ioo D.lo D.hi := by
    simpa only [add_sub_cancel_right] using hsub.trans hJI
  have hbound : ∀ v ∈ uIcc ((cut + (S.level : ℝ)) - S.level)
      ((cut + S.level) - S.level + ell),
      ‖(1 : ℝ) • ((1 : Matrix (Fin (finrank ℝ S.covector.ker))
        (Fin (finrank ℝ S.covector.ker)) ℝ) * originalSeedKernel S w v * 1ᵀ)‖ ≤ B := by
    intro v hv
    simp only [one_smul, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]
    exact (hC v (hsub (by simpa only [add_sub_cancel_right] using hv))).trans (le_max_left _ _)
  have hcurve := D.originalNormalizedClockMobility_bounds hF hw 1
    (t := 1) zero_lt_one hB.le hclock hbound
  have hsize : B * |ell| / 1 ≤ ρ := by
    have hh := mul_le_mul_of_nonneg_left hell hB.le
    rw [mul_div_cancel₀ _ hB.ne'] at hh
    simpa only [div_one] using hh
  refine ⟨hcurve.1, ?_, ?_, ?_⟩
  · intro r hr
    apply hsub.trans hJI
    by_cases he : 0 ≤ ell
    · rw [uIcc_of_le (by linarith)]
      have hm := mul_le_mul_of_nonneg_left hr.2 he
      exact ⟨by nlinarith [mul_nonneg he hr.1], by nlinarith⟩
    · rw [uIcc_of_ge (by linarith)]
      have hm := mul_le_mul_of_nonpos_left hr.2 (le_of_not_ge he)
      have hn := mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge he) hr.1
      exact ⟨by nlinarith, by nlinarith⟩
  · intro r hr
    exact (hcurve.2.1 r hr).trans hsize
  · intro r hr
    exact (mul_le_mul_of_nonneg_right ((hcurve.2.1 r hr).trans hsize) hL).trans hρL

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
