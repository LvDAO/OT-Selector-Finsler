import OTSelector.Reconstruction.FinslerOriginalCommonCutCompliance
import OTSelector.LinearAlgebra.Matrix.PositiveLegInverseQuadratic
import OTSelector.Reconstruction.SeparatedComplianceBound

/-!
# Internal positive-leg bounds on actual compact regular clock regions

Continuity and strict positivity of the actual original Finsler kernel on a compact region
produce a uniform Loewner lower bound. Integrating gives the corresponding original
compliance-leg bound, with no separately imposed inverse coefficient or rank assumption.
-/

open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

/-- The fixed coordinate square sum is controlled by dimension times the actual coordinate norm. -/
theorem sum_sq_le_card_mul_pi_norm_sq {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    (∑ i, v i ^ 2) ≤ (Fintype.card ι : ℝ) * ‖v‖ ^ 2 := by
  calc
    _ ≤ ∑ _i : ι, ‖v‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_le_pi_norm v i
      rw [Real.norm_eq_abs] at hi
      nlinarith [sq_abs (v i), abs_nonneg (v i)]
    _ = _ := by simp

/-- Every continuous compact positive matrix field has a uniform positive Loewner lower
bound, including zero-dimensional fibers. -/
theorem exists_uniform_scalar_identity_lower_bound
    {ι Θ : Type*} [Fintype ι] [DecidableEq ι] [TopologicalSpace Θ]
    {J : Set Θ} (hJ : IsCompact J) {A : Θ → Matrix ι ι ℝ}
    (hA : ContinuousOn A J) (hpos : ∀ x ∈ J, (A x).PosDef) :
    ∃ h : ℝ, h > 0 ∧ ∀ x ∈ J, (A x - h • (1 : Matrix ι ι ℝ)).PosSemidef := by
  obtain ⟨m, hm, hbound⟩ := exists_uniform_matrixQuadratic_lower_bound hJ hA hpos
  let h := m / ((Fintype.card ι : ℝ) + 1)
  have hh : 0 < h := by dsimp [h]; positivity
  have hscale : h * (Fintype.card ι : ℝ) ≤ m := by
    have heq : h * ((Fintype.card ι : ℝ) + 1) = m := by
      dsimp [h]
      field_simp
    nlinarith
  refine ⟨h, hh, fun x hx ↦ ?_⟩
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((hpos x hx).isHermitian.sub (Matrix.PosDef.one.smul hh).isHermitian)
  intro v
  have he := hbound x hx v
  have hsum := mul_le_mul_of_nonneg_left (sum_sq_le_card_mul_pi_norm_sq v) hh.le
  have hscalev := mul_le_mul_of_nonneg_right hscale (sq_nonneg ‖v‖)
  have hsumself : v ⬝ᵥ v = ∑ i, v i ^ 2 := by simp only [dotProduct, pow_two]
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul, hsumself]
  dsimp only [matrixQuadratic] at he
  nlinarith

/-- Integrating a genuine kernel lower bound gives the exact length-times-bound compliance
lower bound in the same original basis. -/
theorem intervalIntegral_scalar_identity_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {K : ℝ → Matrix ι ι ℝ} {a b h : ℝ} (hab : a ≤ b)
    (hK : ContinuousOn K (Icc a b))
    (hlower : ∀ t ∈ Icc a b, (K t - h • (1 : Matrix ι ι ℝ)).PosSemidef) :
    ((∫ t in a..b, K t) - ((b - a) * h) • (1 : Matrix ι ι ℝ)).PosSemidef := by
  have hKi : IntervalIntegrable K volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hK
  have hp := posSemidef_intervalIntegral hab hlower
  rw [intervalIntegral.integral_sub hKi intervalIntegrable_const,
    intervalIntegral.integral_const] at hp
  simpa only [smul_smul] using hp

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual original Finsler kernel internally has a uniform geometric lower bound on
every compact regular original clock region. -/
theorem exists_original_kernel_uniform_lower_on_compact
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) :
    ∃ h : ℝ, h > 0 ∧ ∀ t ∈ J, (originalSeedKernel S w t - h • 1).PosSemidef :=
  exists_uniform_scalar_identity_lower_bound hJ
    ((D.original_kernel_regular hF hw).1.mono hJI)
    (fun t ht ↦ (D.original_kernel_regular hF hw).2 t (hJI ht))

/-- Every actual original compliance leg lying in that compact regular clock region has
the derived positive lower bound scaled by its unchanged physical clock length. -/
theorem exists_original_compliance_lower_on_compact
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {J : Set ℝ} (hJ : IsCompact J) (hJI : J ⊆ Ioo D.lo D.hi) :
    ∃ h : ℝ, h > 0 ∧ ∀ {a b : ℝ}, a ≤ b → Icc (a - (S.level : ℝ)) (b - (S.level : ℝ)) ⊆ J →
      (originalSeedClockCompliance S w a b - ((b - a) * h) • 1).PosSemidef := by
  obtain ⟨h, hh, hK⟩ := D.exists_original_kernel_uniform_lower_on_compact hF hw hJ hJI
  refine ⟨h, hh, fun {a b} hab hsub ↦ ?_⟩
  have hp := intervalIntegral_scalar_identity_lower_bound (sub_le_sub_right hab (S.level : ℝ))
    ((D.original_kernel_regular hF hw).1.mono (hsub.trans hJI))
    (fun t ht ↦ hK t (hsub ht))
  have heq : (b - (S.level : ℝ)) - (a - (S.level : ℝ)) = b - a := by ring
  simpa only [heq, originalSeedClockCompliance] using hp

/-- Removing genuine nonnegative end pieces can only decrease the actual original
compliance. The endpoints remain the original physical clocks. -/
theorem original_compliance_subsegment_posSemidef
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {a r s b : ℝ} (ha : a - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hb : b - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (har : a ≤ r) (hrs : r ≤ s) (hsb : s ≤ b) :
    (originalSeedClockCompliance S w a b - originalSeedClockCompliance S w r s).PosSemidef := by
  apply posSemidef_compliance_sub_short_window
    (sub_le_sub_right har (S.level : ℝ)) (sub_le_sub_right hrs (S.level : ℝ))
    (sub_le_sub_right hsb (S.level : ℝ))
  · exact (D.original_kernel_regular hF hw).1.mono (Icc_subset_Ioo ha.1 hb.2)
  · intro t ht
    exact ((D.original_kernel_regular hF hw).2 t (Icc_subset_Ioo ha.1 hb.2 ht)).posSemidef

/-- A genuine original leg containing a fixed regular comparison segment inherits its
positive lower bound, even if the leg endpoints approach focal endpoints. -/
theorem exists_original_compliance_lower_containing_subinterval
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {r s : ℝ} (hr : r - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hs : s - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hrs : r < s) :
    ∃ h : ℝ, h > 0 ∧ ∀ {a b : ℝ},
      a - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      b - (S.level : ℝ) ∈ Ioo D.lo D.hi → a ≤ r → s ≤ b →
      (originalSeedClockCompliance S w a b - h • 1).PosSemidef := by
  obtain ⟨κ, hκ, hleg⟩ := D.exists_original_compliance_lower_on_compact hF hw isCompact_Icc
    (Icc_subset_Ioo hr.1 hs.2)
  refine ⟨(s-r)*κ, mul_pos (sub_pos.mpr hrs) hκ, fun {a b} ha hb har hsb ↦ ?_⟩
  have hsmall := hleg hrs.le (Subset.refl (Icc (r-(S.level : ℝ)) (s-(S.level : ℝ))))
  have hlarge := D.original_compliance_subsegment_posSemidef hF hw ha hb har hrs.le hsb
  have hsum := hlarge.add hsmall
  convert hsum using 1
  abel

/-- Weakening a positive original matrix lower bound preserves its geometric meaning. -/
theorem scalar_identity_lower_bound_mono
    {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ} {h k : ℝ}
    (hhk : h ≤ k) (hA : (A-k•1).PosSemidef) : (A-h•1).PosSemidef := by
  have hscalar : ((k-h) • (1 : Matrix ι ι ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (sub_nonneg.mpr hhk)
  convert hA.add hscalar using 1
  module

/-- At a fixed regular cut, original clock collars internally give a common positive
four-leg bound. This is uniform over all original endpoints beyond those collars. -/
theorem exists_original_commonCut_fourLeg_lower
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {r c s : ℝ} (hr : r - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hc : c - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    (hs : s - (S.level : ℝ) ∈ Ioo D.lo D.hi) (hrc : r < c) (hcs : c < s) :
    ∃ h : ℝ, h > 0 ∧ ∀ {a₁ a₂ b₁ b₂ : ℝ},
      a₁ - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      a₂ - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      b₁ - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      b₂ - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      a₁ ≤ r → a₂ ≤ r → s ≤ b₁ → s ≤ b₂ →
      (originalSeedClockCompliance S w a₁ c-h•1).PosSemidef ∧
      (originalSeedClockCompliance S w c b₁-h•1).PosSemidef ∧
      (originalSeedClockCompliance S w a₂ c-h•1).PosSemidef ∧
      (originalSeedClockCompliance S w c b₂-h•1).PosSemidef := by
  obtain ⟨hL, hhL, hleft⟩ :=
    D.exists_original_compliance_lower_containing_subinterval hF hw hr hc hrc
  obtain ⟨hR, hhR, hright⟩ :=
    D.exists_original_compliance_lower_containing_subinterval hF hw hc hs hcs
  refine ⟨min hL hR, lt_min hhL hhR, fun {a₁ a₂ b₁ b₂} ha₁ ha₂ hb₁ hb₂ h₁ h₂ h₃ h₄ ↦ ?_⟩
  exact ⟨scalar_identity_lower_bound_mono (min_le_left _ _) (hleft ha₁ hc h₁ le_rfl),
    scalar_identity_lower_bound_mono (min_le_right _ _) (hright hc hb₁ le_rfl h₃),
    scalar_identity_lower_bound_mono (min_le_left _ _) (hleft ha₂ hc h₂ le_rfl),
    scalar_identity_lower_bound_mono (min_le_right _ _) (hright hc hb₂ le_rfl h₄)⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
