import OTSelector.Reconstruction.RegularClockLegLowerBound
import OTSelector.Reconstruction.OriginalKernelInverseUniformBound
import OTSelector.Reconstruction.OriginalRegularOneEdgeTraffic

/-! Uniform actual geometry on compact regular physical-clock strips, and
whole-span length lower bounds, with focal endpoints still allowed. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- One actual global positive mobility bound gives length-scaled compliance
lower bounds for every original interior leg, including legs near focal ends. -/
theorem exists_original_compliance_wholeSpan_length_lower
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ {a b : ℝ}, a ≤ b →
      a - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      b - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      (originalSeedClockCompliance S w a b - ((b - a) * κ) • 1).PosSemidef := by
  obtain ⟨κ, hκ, hK⟩ := D.exists_original_kernel_wholeSpan_uniform_lower hF hw
  refine ⟨κ, hκ, ?_⟩
  intro a b hab ha hb
  have h := intervalIntegral_scalar_identity_lower_bound
    (sub_le_sub_right hab (S.level : ℝ))
    ((D.original_kernel_regular hF hw).1.mono (Icc_subset_Ioo ha.1 hb.2))
    (fun t ht ↦ hK t (Icc_subset_Ioo ha.1 hb.2 ht))
  have heq : (b - (S.level : ℝ)) - (a - (S.level : ℝ)) = b - a := by ring
  simpa only [originalSeedClockCompliance, heq] using h

/-- A compact regular physical-clock strip has an internally produced common
mobility norm bound and quarter-cone radius. The original whole-span inverse
bound makes the cone estimate uniform across every clock in the strip. -/
theorem exists_original_regular_strip_uniformCone
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {a b : ℝ}
    (ha : a - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : b - (S.level : ℝ) ∈ Ioo D.lo D.hi) :
    ∃ C δ : ℝ, 0 < C ∧ 0 < δ ∧
      (∀ c ∈ Icc a b, ‖originalSeedKernel S w (c - S.level)‖ ≤ C) ∧
      ∀ c ∈ Icc a b, ∀ r : ℝ, |r - c| ≤ δ →
        r - S.level ∈ Ioo D.lo D.hi ∧
        ∀ p : Fin (finrank ℝ S.covector.ker) → ℝ,
          ‖originalSeedKernel S w (r - S.level) *ᵥ p -
            originalSeedKernel S w (c - S.level) *ᵥ p‖ ≤
              ‖originalSeedKernel S w (c - S.level) *ᵥ p‖ / 4 := by
  let d := min (a - (S.level : ℝ) - D.lo) (D.hi - (b - (S.level : ℝ))) / 2
  have hd : 0 < d := by dsimp [d]; exact half_pos (lt_min (by linarith [ha.1]) (by linarith [hb.2]))
  have hleft : d ≤ (a - (S.level : ℝ) - D.lo) / 2 := by dsimp [d]; gcongr; exact min_le_left _ _
  have hright : d ≤ (D.hi - (b - (S.level : ℝ))) / 2 := by dsimp [d]; gcongr; exact min_le_right _ _
  let J : Set ℝ := Icc (a - d) (b + d)
  have hJI : ∀ r ∈ J, r - (S.level : ℝ) ∈ Ioo D.lo D.hi := by
    intro r hr
    constructor <;> dsimp only [J, mem_Icc] at hr <;> linarith [hr.1, hr.2]
  let W := fun r : ℝ ↦ originalSeedKernel S w (r - (S.level : ℝ))
  have hW : ContinuousOn W J :=
    (D.original_kernel_regular hF hw).1.comp (continuousOn_id.sub continuousOn_const) hJI
  obtain ⟨C₀, hC₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hW
  obtain ⟨H, hH, hInv⟩ := D.exists_original_kernel_inverse_wholeSpan_bound hF hw
  let η : ℝ := 1 / (4 * (H + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨e, he, hcont⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous hW) η hη
  let δ := min d (e / 2)
  have hδ : 0 < δ := lt_min hd (half_pos he)
  refine ⟨max C₀ 1, δ, lt_of_lt_of_le zero_lt_one (le_max_right _ _), hδ, ?_, ?_⟩
  · intro c hc
    exact (hC₀ c ⟨by linarith [hc.1], by linarith [hc.2]⟩).trans (le_max_left _ _)
  · intro c hc r hrc
    have hcd : c ∈ J := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    have hrd : r ∈ J := by
      have hδd : δ ≤ d := min_le_left _ _
      obtain ⟨hl, hh⟩ := abs_le.mp hrc
      exact ⟨by linarith [hc.1], by linarith [hc.2]⟩
    refine ⟨hJI r hrd, ?_⟩
    have hdiff : ‖W r - W c‖ ≤ η := by
      apply le_of_lt
      have hdrc : dist r c < e := by
        rw [Real.dist_eq]
        exact hrc.trans_lt ((min_le_right d (e / 2)).trans_lt (half_lt_self he))
      simpa only [dist_eq_norm] using hcont r hrd c hcd hdrc
    have hdet : IsUnit (W c).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp ((D.original_kernel_regular hF hw).2
        (c - S.level) (hJI c hcd)).isUnit
    let _ := Matrix.invertibleOfIsUnitDet (W c) hdet
    have heq : W r * (W c)⁻¹ - 1 = (W r - W c) * (W c)⁻¹ := by
      rw [sub_mul, Matrix.mul_inv_of_invertible]
    have hηH : η * H ≤ (1 / 4 : ℝ) := by
      dsimp [η]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (show (0 : ℝ) < 4 * (H + 1) by positivity)).mpr
      nlinarith
    have hrel : ‖W r * (W c)⁻¹ - 1‖ ≤ (1 / 4 : ℝ) := by
      rw [heq]
      exact (norm_mul_le _ _).trans ((mul_le_mul hdiff (hInv _ (hJI c hcd))
        (norm_nonneg _) hη.le).trans hηH)
    intro p
    have hv := norm_mobility_velocity_sub_le (W r) (W c) hdet p hrel
    simpa only [W, div_eq_mul_inv, one_mul, mul_comm] using hv

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
