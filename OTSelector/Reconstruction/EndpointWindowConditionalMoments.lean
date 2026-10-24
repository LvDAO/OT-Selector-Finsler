import OTSelector.Reconstruction.PhysicalJacobiMomentWindow

/-!
# Whole conditional intervals from the two actual endpoint windows

The two endpoints may use different graph charts. Both represent the same original
inverse quadratic form and the same finite conditional law. Their proved focal
moments, exact changes of integration base, and continuity on the compact middle
imply the moment on the entire original interval.
-/

open Set MeasureTheory Matrix
open scoped Topology Matrix.Norms.Operator

namespace OTSelector.Reconstruction

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Two actual endpoint window systems suffice for the original full-interval power
moment. Neither a global adapted chart nor summability over a countable atlas is needed. -/
theorem integrable_compliancePrimitive_rpow_of_endpoint_windows
    {K : ℝ → Matrix n n ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b l h c r : ℝ}
    (WL : PhysicalJacobiMomentWindow K μ a l)
    (WR : PhysicalJacobiMomentWindow K μ h b)
    (hl : l < b) (hh : a < h)
    (hK : ContinuousOn K (Ioo a b)) (hc : c ∈ Ioo a b)
    (hμ : ∀ᵐ t ∂μ, t ∈ Ioo a b) (hr0 : 0 < r) (hr : r < 2) :
    Integrable (fun t ↦ ‖∫ q in c..t, K q‖ ^ r) μ := by
  have hL := WL.integrableOn_globalPrimitive_rpow hK hc
    (fun _ ht ↦ ⟨ht.1, ht.2.trans hl⟩) hr0 hr
  have hR := WR.integrableOn_globalPrimitive_rpow hK hc
    (fun _ ht ↦ ⟨hh.trans ht.1, ht.2⟩) hr0 hr
  have hmiddle : Icc ((a + l) / 2) ((h + b) / 2) ⊆ Ioo a b := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2, WL.left_lt_right, WR.left_lt_right]
  have hmid : IntegrableOn (fun t ↦ ‖∫ q in c..t, K q‖ ^ r)
      (Icc ((a + l) / 2) ((h + b) / 2)) μ :=
    ((((continuousOn_compliancePrimitive hK hc).mono hmiddle).norm).rpow_const
      (fun _ _ ↦ Or.inr hr0.le)).integrableOn_Icc
  have hcover : Ioo a b ⊆
      (Ioo a l ∪ Icc ((a + l) / 2) ((h + b) / 2)) ∪ Ioo h b := by
    intro t ht
    by_cases htl : t < l
    · exact Or.inl (Or.inl ⟨ht.1, htl⟩)
    by_cases htr : h < t
    · exact Or.inr ⟨htr, ht.2⟩
    exact Or.inl (Or.inr ⟨by linarith [WL.left_lt_right],
      by linarith [WR.left_lt_right]⟩)
  have hwhole := ((hL.union hmid).union hR).mono_set hcover
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] using hwhole

end OTSelector.Reconstruction
