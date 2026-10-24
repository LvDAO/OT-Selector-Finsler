import OTSelector.Geometry.FocalConditionalPowerMomentsGlobalLeft
import OTSelector.Geometry.FocalConditionalPowerMomentsGlobalRight
import OTSelector.MeasureTheory.Integrability.MatrixInverseProduct

/-!
# Power moments on the full finite conditional interval

Both endpoint neighborhoods and the compact middle are integrated under one original
conditional measure. Focal endpoints use their actual regular crossings; nonfocal
endpoints use continuity of the inverse Jacobi matrix. Every moment `0 < r < 2`
is therefore integrable on the full original support span, without uniform constants
over roots, an ordering assumption, or prescribed endpoint nullities.
-/

open Set MeasureTheory Matrix LinearMap Metric
open scoped Topology Matrix.Norms.Operator ENNReal

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The same finite conditional law has every compliance moment `0 < r < 2` on
its entire support interval. Regular crossing is used only when an endpoint is focal. -/
theorem integrable_jacobiCompliance_rpow_of_regular_endpoints
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ r : ℝ} {Da Db : Matrix n n ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    (hJa : HasDerivWithinAt J Da (Ici a) a)
    (hJb : HasDerivWithinAt J Db (Iic b) b)
    (hcrossa : ∀ v, J a *ᵥ v = 0 →
      Da *ᵥ v ∈ LinearMap.range (J a).mulVecLin → v = 0)
    (hcrossb : ∀ v, J b *ᵥ v = 0 →
      Db *ᵥ v ∈ LinearMap.range (J b).mulVecLin → v = 0)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|)))
    (hr0 : 0 < r) (hr : r < 2) :
    Integrable (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) μ := by
  have hab : a < b := hc.1.trans hc.2
  have hJclosed : ContinuousOn J (Icc a b) := by
    intro t ht
    by_cases hta : t = a
    · subst t
      exact hJa.continuousWithinAt.mono Icc_subset_Ici_self
    by_cases htb : t = b
    · subst t
      exact hJb.continuousWithinAt.mono Icc_subset_Iic_self
    have hti : t ∈ Ioo a b := ⟨lt_of_le_of_ne ht.1 (Ne.symm hta), lt_of_le_of_ne ht.2 htb⟩
    exact (hJ t hti).continuousAt.continuousWithinAt
  have hJdiff : DifferentiableOn ℝ J (Ioo a b) :=
    fun t ht ↦ (hJ t ht).differentiableAt.differentiableWithinAt
  have hT : ContinuousOn (jacobiCompliancePrimitive J C c) (Ioo a b) :=
    fun t ht ↦ (hasDerivAt_jacobiCompliancePrimitive hJdiff
      (hC.mono Ioo_subset_Icc_self) hd hc ht).continuousAt.continuousWithinAt
  obtain ⟨Kbar, Rbar, hKbar, _, hKeq, _⟩ :=
    exists_continuous_integral_second_jacobi_extension
      hJ hP hA hB hC hAsym hCsym hd hc hinit
  have hidentity : ∀ t ∈ Ioo a b,
      jacobiCompliancePrimitive J C c t = (J t)⁻¹ * Kbar t := by
    intro t ht
    rw [hKeq ht, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hd t ht)), Matrix.one_mul]
  have hleft : ∃ ε > 0,
      IntegrableOn (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) (Ioo a (a + ε)) μ := by
    by_cases hdet : (J a).det = 0
    · have hk : (1 : ℝ) ≤ (Module.finrank ℝ (ker (J a).mulVecLin) : ℝ) := by
        exact_mod_cast jacobi_nullity_pos_of_det_eq_zero (J a) hdet
      obtain ⟨ε, hε, _, hi⟩ :=
        exists_integrableOn_jacobiCompliance_rpow_near_regular_left_endpoint
          hJ hP hA hB hC hAsym hCsym hd hc hinit hJa hcrossa
          hρ hw hρ0 hρR hw0 hθ hμ hr0 (by linarith)
      exact ⟨ε, hε, hi⟩
    · obtain ⟨δ, hδ, hi⟩ := exists_integrableOn_inverse_jacobi_product_rpow_near_nonfocal
        hJclosed hKbar hT hidentity (left_mem_Icc.mpr hab.le) hdet μ hr0.le
      let ε := min δ ((b - a) / 2)
      have hε : 0 < ε := lt_min hδ (half_pos (sub_pos.mpr hab))
      refine ⟨ε, hε, hi.mono_set ?_⟩
      intro t ht
      have heδ : ε ≤ δ := min_le_left _ _
      have heb : ε < b - a := (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hab))
      refine ⟨⟨ht.1, by linarith [ht.2]⟩, ?_⟩
      rw [mem_ball, Real.dist_eq, abs_of_pos (sub_pos.mpr ht.1)]
      linarith [ht.2]
  have hright : ∃ ε > 0,
      IntegrableOn (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) (Ioo (b - ε) b) μ := by
    by_cases hdet : (J b).det = 0
    · have hk : (1 : ℝ) ≤ (Module.finrank ℝ (ker (J b).mulVecLin) : ℝ) := by
        exact_mod_cast jacobi_nullity_pos_of_det_eq_zero (J b) hdet
      obtain ⟨ε, hε, _, hi⟩ :=
        exists_integrableOn_jacobiCompliance_rpow_near_regular_right_endpoint
          hJ hP hA hB hC hAsym hCsym hd hc hinit hJb hcrossb
          hρ hw hρ0 hρR hw0 hθ hμ hr0 (by linarith)
      exact ⟨ε, hε, hi⟩
    · obtain ⟨δ, hδ, hi⟩ := exists_integrableOn_inverse_jacobi_product_rpow_near_nonfocal
        hJclosed hKbar hT hidentity (right_mem_Icc.mpr hab.le) hdet μ hr0.le
      let ε := min δ ((b - a) / 2)
      have hε : 0 < ε := lt_min hδ (half_pos (sub_pos.mpr hab))
      refine ⟨ε, hε, hi.mono_set ?_⟩
      intro t ht
      have heδ : ε ≤ δ := min_le_left _ _
      have heb : ε < b - a := (min_le_right _ _).trans_lt (half_lt_self (sub_pos.mpr hab))
      refine ⟨⟨by linarith [ht.1], ht.2⟩, ?_⟩
      rw [mem_ball, Real.dist_eq, abs_of_neg (sub_neg.mpr ht.2)]
      linarith [ht.1]
  obtain ⟨εL, hεL, hleft⟩ := hleft
  obtain ⟨εR, hεR, hright⟩ := hright
  have hmiddle : Icc (a + εL / 2) (b - εR / 2) ⊆ Ioo a b := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hmid : IntegrableOn (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r)
      (Icc (a + εL / 2) (b - εR / 2)) μ :=
    (((hT.mono hmiddle).norm).rpow_const (fun _ _ ↦ Or.inr hr0.le)).integrableOn_Icc
  have hcover : Ioo a b ⊆
      (Ioo a (a + εL) ∪ Icc (a + εL / 2) (b - εR / 2)) ∪ Ioo (b - εR) b := by
    intro t ht
    by_cases htl : t < a + εL
    · exact Or.inl (Or.inl ⟨ht.1, htl⟩)
    by_cases htr : b - εR < t
    · exact Or.inr ⟨htr, ht.2⟩
    exact Or.inl (Or.inr ⟨by linarith, by linarith⟩)
  have hwhole := ((hleft.union hmid).union hright).mono_set hcover
  have hrestrict : μ.restrict (Ioo a b) = μ := by
    rw [hμ, restrict_withDensity measurableSet_Ioo,
      Measure.restrict_restrict_of_subset (Subset.rfl : Ioo a b ⊆ Ioo a b)]
  simpa only [IntegrableOn, hrestrict] using hwhole

/-- The original Hamiltonian endpoint data supply both crossing conditions internally.
No endpoint determinant is required to be nonzero: focal and nonfocal ends are both covered. -/
theorem integrable_jacobiCompliance_rpow_of_hamiltonian_endpoints
    {J P A B C : ℝ → Matrix n n ℝ} {a b c θ r : ℝ}
    (hJ : ∀ t ∈ Ioo a b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo a b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc a b)) (hB : ContinuousOn B (Icc a b))
    (hC : ContinuousOn C (Icc a b))
    (hAsym : ∀ t ∈ Ioo a b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo a b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo a b, (J t).det ≠ 0) (hc : c ∈ Ioo a b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    (hJa : HasDerivWithinAt J (B a * J a + C a * P a) (Ici a) a)
    (hJb : HasDerivWithinAt J (B b * J b + C b * P b) (Iic b) b)
    (hWa : (J a)ᵀ * P a = (P a)ᵀ * J a)
    (hWb : (J b)ᵀ * P b = (P b)ᵀ * J b)
    (hphasea : ∀ v, J a *ᵥ v = 0 → P a *ᵥ v = 0 → v = 0)
    (hphaseb : ∀ v, J b *ᵥ v = 0 → P b *ᵥ v = 0 → v = 0)
    (hCa : (C a).PosDef) (hCb : (C b).PosDef)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc a b))
    (hρ0 : ∀ t ∈ Ioo a b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo a b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo a b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ = (volume.restrict (Ioo a b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|)))
    (hr0 : 0 < r) (hr : r < 2) :
    Integrable (fun t ↦ ‖jacobiCompliancePrimitive J C c t‖ ^ r) μ := by
  exact integrable_jacobiCompliance_rpow_of_regular_endpoints
    hJ hP hA hB hC hAsym hCsym hd hc hinit hJa hJb
    (fun _ hv hrange ↦ focal_crossing_kernel_eq_zero hWa hphasea hCa hv hrange)
    (fun _ hv hrange ↦ focal_crossing_kernel_eq_zero hWb hphaseb hCb hv hrange)
    hρ hw hρ0 hρR hw0 hθ hμ hr0 hr

end OTSelector.Geometry
