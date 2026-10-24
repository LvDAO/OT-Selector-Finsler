import OTSelector.Reconstruction.PhysicalJacobiDeterminantWindow
import OTSelector.Reconstruction.EndpointWindowConditionalMoments

/-!
# Spectral determinant moments across endpoint charts

The physical measure and original inverse quadratic form are fixed. Each endpoint
chart supplies determinant cancellation for the same primitive, after exact rebasing.
Combining those estimates with the compact middle yields the full interval. Positivity
of the original inverse quadratic form identifies the signed determinants with the
spectral absolute-value determinant, without any source-target ordering.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator MatrixOrder

namespace OTSelector.Reconstruction
open OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Endpoint windows in different actual graph charts give both global signed
Jacobi determinant moments on the same original conditional measure. -/
theorem integrable_compliancePrimitive_determinants_of_endpoint_windows
    {K : ℝ → Matrix n n ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b l h c : ℝ}
    (WL : PhysicalJacobiMomentWindow K μ a l)
    (WR : PhysicalJacobiMomentWindow K μ h b)
    (hl : l < b) (hh : a < h)
    (hK : ContinuousOn K (Ioo a b)) (hc : c ∈ Ioo a b)
    (hμ : ∀ᵐ t ∂μ, t ∈ Ioo a b) :
    Integrable (fun t ↦ (1 + ∫ q in c..t, K q).det) μ ∧
      Integrable (fun t ↦ (1 - ∫ q in c..t, K q).det) μ := by
  have hL := WL.integrableOn_globalPrimitive_determinants hK hc
    (fun _ ht ↦ ⟨ht.1, ht.2.trans hl⟩)
  have hR := WR.integrableOn_globalPrimitive_determinants hK hc
    (fun _ ht ↦ ⟨hh.trans ht.1, ht.2⟩)
  have hT := continuousOn_compliancePrimitive hK hc
  have hmiddle : Icc ((a + l) / 2) ((h + b) / 2) ⊆ Ioo a b := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, WL.left_lt_right, WR.left_lt_right]
  have hcover : Ioo a b ⊆
      (Ioo a l ∪ Icc ((a + l) / 2) ((h + b) / 2)) ∪ Ioo h b := by
    intro t ht
    by_cases htl : t < l
    · exact Or.inl (Or.inl ⟨ht.1, htl⟩)
    by_cases htr : h < t
    · exact Or.inr ⟨htr, ht.2⟩
    exact Or.inl (Or.inr ⟨by linarith [WL.left_lt_right],
      by linarith [WR.left_lt_right]⟩)
  have finish (f : ℝ → ℝ) (hf : ContinuousOn f (Ioo a b))
      (hL : IntegrableOn f (Ioo a l) μ) (hR : IntegrableOn f (Ioo h b) μ) :
      Integrable f μ := by
    have hmid := (hf.mono hmiddle).integrableOn_Icc (μ := μ)
    have hwhole := ((hL.union hmid).union hR).mono_set hcover
    simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] using hwhole
  exact ⟨finish _ (continuous_id.matrix_det.comp_continuousOn (continuousOn_const.add hT))
    hL.1 hR.1,
    finish _ (continuous_id.matrix_det.comp_continuousOn (continuousOn_const.sub hT))
    hL.2 hR.2⟩

/-- A positive original inverse Hessian gives a definite sign to its integral on
either side of the fixed root, even when that root is outside a chosen endpoint chart. -/
theorem abs_compliancePrimitive_eq
    {K : ℝ → Matrix n n ℝ} {a b c t : ℝ}
    (hKpos : ∀ q ∈ Ioo a b, (K q).PosSemidef)
    (hc : c ∈ Ioo a b) (ht : t ∈ Ioo a b) :
    CFC.abs (∫ q in c..t, K q) =
      if t ≤ c then -(∫ q in c..t, K q) else (∫ q in c..t, K q) := by
  split_ifs with htc
  · have hneg : (-(∫ q in c..t, K q)).PosSemidef := by
      rw [← intervalIntegral.integral_symm]
      apply posSemidef_intervalIntegral htc
      intro q hq
      exact hKpos q ⟨ht.1.trans_le hq.1, hq.2.trans_lt hc.2⟩
    exact CFC.abs_of_nonpos _ (neg_nonneg.mp hneg.nonneg)
  · apply CFC.abs_of_nonneg
    apply Matrix.PosSemidef.nonneg
    apply posSemidef_intervalIntegral (le_of_not_ge htc)
    intro q hq
    exact hKpos q ⟨hc.1.trans_le hq.1, hq.2.trans_lt ht.2⟩

/-- Both required moment conclusions hold on the full original finite conditional
interval. The endpoints may have different charts and singular position matrices. -/
theorem compliance_moments_of_endpoint_windows
    {K : ℝ → Matrix n n ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b l h c : ℝ}
    (WL : PhysicalJacobiMomentWindow K μ a l)
    (WR : PhysicalJacobiMomentWindow K μ h b)
    (hl : l < b) (hh : a < h)
    (hK : ContinuousOn K (Ioo a b))
    (hKpos : ∀ q ∈ Ioo a b, (K q).PosSemidef)
    (hc : c ∈ Ioo a b) (hμ : ∀ᵐ t ∂μ, t ∈ Ioo a b) :
    Integrable (fun t ↦ (1 + CFC.abs (∫ q in c..t, K q)).det) μ ∧
      ∀ r : ℝ, 0 < r → r < 2 →
        Integrable (fun t ↦ ‖∫ q in c..t, K q‖ ^ r) μ := by
  classical
  refine ⟨?_, fun r hr0 hr ↦
    integrable_compliancePrimitive_rpow_of_endpoint_windows WL WR hl hh hK hc hμ hr0 hr⟩
  obtain ⟨hplus, hminus⟩ :=
    integrable_compliancePrimitive_determinants_of_endpoint_windows WL WR hl hh hK hc hμ
  have hsplit : Integrable (fun t ↦ if t ≤ c then (1 - ∫ q in c..t, K q).det
      else (1 + ∫ q in c..t, K q).det) μ :=
    Integrable.piecewise measurableSet_Iic hminus.integrableOn hplus.integrableOn
  apply hsplit.congr
  filter_upwards [hμ] with t ht
  rw [abs_compliancePrimitive_eq hKpos hc ht]
  split_ifs <;> simp only [sub_eq_add_neg]

end OTSelector.Reconstruction
