import OTSelector.Geometry.FocalConditionalMoments
import Mathlib.Analysis.Matrix.Order

/-!
# Spectral absolute compliance moments for the same conditional law

Positivity of the velocity coefficient makes the actual compliance primitive positive
semidefinite to the right of its base time and negative semidefinite to the left.
Consequently its spectral absolute value is the corresponding signed primitive.
This identifies the determinant moment with `det (1 + |T|)` without an ordering
assumption on the conditional population.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator MatrixOrder

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Integrating positive semidefinite real matrices along an ordered interval preserves
positive semidefiniteness. The Bochner integral's zero fallback causes no exception. -/
theorem posSemidef_intervalIntegral {f : ℝ → Matrix n n ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, (f t).PosSemidef) :
    (∫ t in a..b, f t).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  rw [intervalIntegral.integral_of_le hab]
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact (hf t (Ioc_subset_Icc_self ht)).nonneg

/-- The actual compliance primitive is positive semidefinite to the right of its root. -/
theorem jacobiCompliancePrimitive_posSemidef_right
    {J C : ℝ → Matrix n n ℝ} {a b c t : ℝ}
    (hC : ∀ s ∈ Ioo a b, (C s).PosSemidef)
    (hc : c ∈ Ioo a b) (ht : t ∈ Ioo a b) (hct : c ≤ t) :
    (jacobiCompliancePrimitive J C c t).PosSemidef := by
  apply posSemidef_intervalIntegral hct
  intro s hs
  have hs' : s ∈ Ioo a b := ⟨hc.1.trans_le hs.1, hs.2.trans_lt ht.2⟩
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (hC s hs').mul_mul_conjTranspose_same ((J s)⁻¹)

/-- Negating the actual compliance primitive gives a positive semidefinite matrix on the left. -/
theorem neg_jacobiCompliancePrimitive_posSemidef_left
    {J C : ℝ → Matrix n n ℝ} {a b c t : ℝ}
    (hC : ∀ s ∈ Ioo a b, (C s).PosSemidef)
    (hc : c ∈ Ioo a b) (ht : t ∈ Ioo a b) (htc : t ≤ c) :
    (-jacobiCompliancePrimitive J C c t).PosSemidef := by
  have hswap : -jacobiCompliancePrimitive J C c t =
      jacobiCompliancePrimitive J C t c := by
    exact (intervalIntegral.integral_symm (f := fun s ↦
      (J s)⁻¹ * C s * (J s)⁻¹ᵀ) c t).symm
  rw [hswap]
  exact jacobiCompliancePrimitive_posSemidef_right hC ht hc htc

/-- The spectral absolute value equals the sign selected by the actual interval orientation. -/
theorem abs_jacobiCompliancePrimitive_eq
    {J C : ℝ → Matrix n n ℝ} {a b c t : ℝ}
    (hC : ∀ s ∈ Ioo a b, (C s).PosSemidef)
    (hc : c ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    CFC.abs (jacobiCompliancePrimitive J C c t) =
      if t ≤ c then -jacobiCompliancePrimitive J C c t
      else jacobiCompliancePrimitive J C c t := by
  split_ifs with htc
  · exact CFC.abs_of_nonpos _
      (neg_nonneg.mp (neg_jacobiCompliancePrimitive_posSemidef_left hC hc ht htc).nonneg)
  · exact CFC.abs_of_nonneg _
      (jacobiCompliancePrimitive_posSemidef_right hC hc ht (le_of_not_ge htc)).nonneg

/-- The original conditional density has the spectral determinant moment, even when its
support crosses the root and the Jacobi frame becomes singular at the finite endpoints. -/
theorem integrable_abs_jacobi_determinant_of_conditional_density
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCpos : ∀ t ∈ Ioo a b, (C t).PosSemidef)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|))) :
    Integrable (fun t ↦ (1 + CFC.abs (jacobiCompliancePrimitive J C c t)).det) μ := by
  have hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t := by
    intro t ht
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      (hCpos t ht).isHermitian
  have hsplit := (integrable_jacobi_determinants_of_conditional_density
    hJ hP hA hB hC hAsym hCsym hd hc hinit hρ hw hρ0 hρR hw0 hθ hμ).2.2
  apply hsplit.congr
  have hmem : ∀ᵐ t ∂μ, t ∈ Ioo a b := by
    rw [hμ]
    exact (withDensity_absolutelyContinuous _ _) (ae_restrict_mem measurableSet_Ioo)
  filter_upwards [hmem] with t ht
  rw [abs_jacobiCompliancePrimitive_eq hCpos hc ht]
  split_ifs <;> simp only [sub_eq_add_neg]

end OTSelector.Geometry
