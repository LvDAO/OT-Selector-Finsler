import OTSelector.MeasureTheory.PowerDensityPoleMoments
import OTSelector.Geometry.FocalAsymptotics
import OTSelector.Geometry.JacobiEndpoint

/-!
# Conditional power moments at a regular focal endpoint

The same Jacobi compliance primitive and the same normalized conditional density
have every positive local moment below the endpoint nullity plus one. Regular
crossing produces the determinant zero and inverse pole estimates. The actual
second Jacobi solution, continuously extended to the endpoint, then controls the
compliance primitive itself. No moment or pole bound is an input.

The endpoint is written as zero in its inward distance parameter. The exact
conditional-density identity and the actual endpoint crossing are producer inputs.
-/

open Set MeasureTheory Filter Matrix LinearMap
open scoped Topology Matrix.Norms.Operator

set_option backward.isDefEq.respectTransparency false

namespace OTSelector.Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- At a regular endpoint of nullity `k`, the actual compliance primitive has every
`0 < r < k+1` local moment under the original normalized Jacobi conditional density. -/
theorem exists_integrableOn_jacobiCompliance_rpow_near_regular_endpoint
    {J P A B C : ℝ → Matrix n n ℝ} {b c θ r : ℝ} {D : Matrix n n ℝ}
    (hJ : ∀ t ∈ Ioo 0 b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo 0 b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc 0 b)) (hB : ContinuousOn B (Icc 0 b))
    (hC : ContinuousOn C (Icc 0 b))
    (hAsym : ∀ t ∈ Ioo 0 b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo 0 b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo 0 b, (J t).det ≠ 0) (hc : c ∈ Ioo 0 b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    (hJ0 : HasDerivWithinAt J D (Ioi 0) 0)
    (hcross : ∀ v, J 0 *ᵥ v = 0 → D *ᵥ v ∈ LinearMap.range (J 0).mulVecLin → v = 0)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc 0 b))
    (hρ0 : ∀ t ∈ Ioo 0 b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo 0 b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo 0 b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo 0 b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|)))
    (hr0 : 0 < r) (hr : r < (Module.finrank ℝ (ker (J 0).mulVecLin) : ℝ) + 1) :
    ∃ ε : ℝ, 0 < ε ∧ ε < b ∧
      IntegrableOn (fun s ↦ ‖jacobiCompliancePrimitive J C c s‖ ^ r) (Ioo 0 ε) μ := by
  have hb : 0 < b := hc.1.trans hc.2
  obtain ⟨Kbar, Rbar, hKbar, _, hKeq, _⟩ :=
    exists_continuous_integral_second_jacobi_extension
      hJ hP hA hB hC hAsym hCsym hd hc hinit
  obtain ⟨K₀, hK₀⟩ := isCompact_Icc.bddAbove_image hKbar.norm
  let K := max K₀ 0
  have hK0 : 0 ≤ K := le_max_right _ _
  have hKb : ∀ s ∈ Icc 0 b, ‖Kbar s‖ ≤ K := fun s hs ↦
    (hK₀ (mem_image_of_mem _ hs)).trans (le_max_left _ _)
  obtain ⟨cdet, Cdet, Cinv, _, hCdet, hCinv, hbounds⟩ :=
    regular_crossing_bounds hJ0 hcross
  obtain ⟨δ, hδ, hδbounds⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hbounds
  let ε := min δ (b / 2)
  have hε : 0 < ε := lt_min hδ (half_pos hb)
  have hεb : ε < b := (min_le_right δ (b / 2)).trans_lt (half_lt_self hb)
  have hsub : Ioo (0 : ℝ) ε ⊆ Ioo 0 b := Ioo_subset_Ioo le_rfl hεb.le
  have hdet : ∀ s ∈ Ioo 0 ε,
      |(J s).det| ≤ Cdet * s ^ Module.finrank ℝ (ker (J 0).mulVecLin) := by
    intro s hs
    simpa only [abs_of_pos hs.1] using
      (hδbounds ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩).2.1
  have hTbound : ∀ s ∈ Ioo 0 ε,
      ‖jacobiCompliancePrimitive J C c s‖ ≤ (Cinv * K) / s := by
    intro s hs
    have hs' := hsub hs
    have hidentity : jacobiCompliancePrimitive J C c s = (J s)⁻¹ * Kbar s := by
      rw [hKeq hs', ← Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hd s hs')), Matrix.one_mul]
    have hinv : ‖(J s)⁻¹‖ ≤ Cinv / s := by
      simpa only [abs_of_pos hs.1] using
        (hδbounds ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩).2.2
    rw [hidentity]
    calc
      ‖(J s)⁻¹ * Kbar s‖ ≤ ‖(J s)⁻¹‖ * ‖Kbar s‖ := norm_mul_le _ _
      _ ≤ (Cinv / s) * K := mul_le_mul hinv (hKb s (Ioo_subset_Icc_self hs'))
        (norm_nonneg _) (div_nonneg hCinv.le hs.1.le)
      _ = (Cinv * K) / s := by ring
  obtain ⟨W₀, hW₀⟩ := isCompact_Icc.bddAbove_image hw
  let W := max W₀ 0
  have hW0 : 0 ≤ W := le_max_right _ _
  have hW : ∀ s ∈ Ioo 0 b, w s ≤ W := fun s hs ↦
    (hW₀ (mem_image_of_mem _ (Ioo_subset_Icc_self hs))).trans (le_max_left _ _)
  have hR0 : 0 ≤ R := (hρ0 c hc).trans (hρR c hc)
  have hqbound : ∀ s ∈ Ioo 0 b, ρ s * w s / θ ≤ R * W / θ := by
    intro s hs
    exact div_le_div_of_nonneg_right
      (mul_le_mul (hρR s hs) (hW s hs) (hw0 s hs) hR0) hθ.le
  have hJdiff : DifferentiableOn ℝ J (Ioo 0 b) :=
    fun s hs ↦ (hJ s hs).differentiableAt.differentiableWithinAt
  have hT : ContinuousOn (jacobiCompliancePrimitive J C c) (Ioo 0 b) :=
    fun s hs ↦ (hasDerivAt_jacobiCompliancePrimitive hJdiff
      (hC.mono Ioo_subset_Icc_self) hd hc hs).continuousAt.continuousWithinAt
  have hdensity : AEMeasurable (fun s ↦ (ρ s * w s / θ) * |(J s).det|)
      (volume.restrict (Ioo 0 ε)) := by
    have hw' : AEMeasurable w (volume.restrict (Ioo 0 ε)) :=
      (hw.mono (hsub.trans Ioo_subset_Icc_self)).aemeasurable measurableSet_Ioo
    have hJ' : AEMeasurable (fun s ↦ |(J s).det|) (volume.restrict (Ioo 0 ε)) :=
      (((continuous_id.matrix_det).comp_continuousOn
      (hJdiff.continuousOn.mono hsub)).abs).aemeasurable measurableSet_Ioo
    exact ((hρ.aemeasurable.mul hw').div_const θ).mul hJ'
  have hlocal := integrable_rpow_withDensity_of_power_bounds
    hε (mul_nonneg (div_nonneg (mul_nonneg hR0 hW0) hθ.le) hCdet.le)
    (mul_nonneg hCinv.le hK0) hr0.le hr hdensity
    ((hT.mono hsub).aestronglyMeasurable measurableSet_Ioo)
    (fun s hs ↦ mul_nonneg
      (div_nonneg (mul_nonneg (hρ0 s (hsub hs)) (hw0 s (hsub hs))) hθ.le)
      (abs_nonneg _))
    (fun s hs ↦ calc
      (ρ s * w s / θ) * |(J s).det| ≤
          (R * W / θ) * (Cdet * s ^ Module.finrank ℝ (ker (J 0).mulVecLin)) :=
        mul_le_mul (hqbound s (hsub hs)) (hdet s hs) (abs_nonneg _)
          (div_nonneg (mul_nonneg hR0 hW0) hθ.le)
      _ = ((R * W / θ) * Cdet) * s ^ Module.finrank ℝ (ker (J 0).mulVecLin) := by ring)
    hTbound
  refine ⟨ε, hε, hεb, ?_⟩
  rw [IntegrableOn, hμ, restrict_withDensity measurableSet_Ioo,
    Measure.restrict_restrict_of_subset hsub]
  exact hlocal

/-- Actual positive-Hessian Hamiltonian endpoint data supply regular crossing, and
singularity supplies positive nullity. Thus every `0 < r < 2` moment is locally
integrable, without a prescribed nullity or a separate crossing hypothesis. -/
theorem exists_integrableOn_jacobiCompliance_rpow_lt_two_at_focal_endpoint
    {J P A B C : ℝ → Matrix n n ℝ} {b c θ r : ℝ}
    (hJ : ∀ t ∈ Ioo 0 b, HasDerivAt J (B t * J t + C t * P t) t)
    (hP : ∀ t ∈ Ioo 0 b, HasDerivAt P (-A t * J t - (B t)ᵀ * P t) t)
    (hA : ContinuousOn A (Icc 0 b)) (hB : ContinuousOn B (Icc 0 b))
    (hC : ContinuousOn C (Icc 0 b))
    (hAsym : ∀ t ∈ Ioo 0 b, (A t)ᵀ = A t)
    (hCsym : ∀ t ∈ Ioo 0 b, (C t)ᵀ = C t)
    (hd : ∀ t ∈ Ioo 0 b, (J t).det ≠ 0) (hc : c ∈ Ioo 0 b)
    (hinit : (J c)ᵀ * P c = (P c)ᵀ * J c)
    (hJ0 : HasDerivWithinAt J (B 0 * J 0 + C 0 * P 0) (Ici 0) 0)
    (hW0 : (J 0)ᵀ * P 0 = (P 0)ᵀ * J 0)
    (hphase : ∀ v, J 0 *ᵥ v = 0 → P 0 *ᵥ v = 0 → v = 0)
    (hC0 : (C 0).PosDef) (hfocal : (J 0).det = 0)
    {ρ w : ℝ → ℝ} {R : ℝ} (hρ : Measurable ρ) (hw : ContinuousOn w (Icc 0 b))
    (hρ0 : ∀ t ∈ Ioo 0 b, 0 ≤ ρ t) (hρR : ∀ t ∈ Ioo 0 b, ρ t ≤ R)
    (hw0 : ∀ t ∈ Ioo 0 b, 0 ≤ w t) (hθ : 0 < θ)
    {μ : Measure ℝ}
    (hμ : μ = (volume.restrict (Ioo 0 b)).withDensity
      (fun t ↦ ENNReal.ofReal ((ρ t * w t / θ) * |(J t).det|)))
    (hr0 : 0 < r) (hr : r < 2) :
    ∃ ε : ℝ, 0 < ε ∧ ε < b ∧
      IntegrableOn (fun s ↦ ‖jacobiCompliancePrimitive J C c s‖ ^ r) (Ioo 0 ε) μ := by
  have hk : 0 < Module.finrank ℝ (ker (J 0).mulVecLin) := by
    apply Nat.pos_of_ne_zero
    intro hdim
    have hker := Submodule.finrank_eq_zero.mp hdim
    have hdet : (J 0).mulVecLin.det = 0 := by
      rw [← LinearMap.det_toLin'] at hfocal
      exact hfocal
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet) hker
  have hkr : (1 : ℝ) ≤ (Module.finrank ℝ (ker (J 0).mulVecLin) : ℝ) := by
    exact_mod_cast hk
  exact exists_integrableOn_jacobiCompliance_rpow_near_regular_endpoint
    hJ hP hA hB hC hAsym hCsym hd hc hinit (hJ0.mono Ioi_subset_Ici_self)
    (fun _ hv hrange ↦ focal_crossing_kernel_eq_zero hW0 hphase hC0 hv hrange)
    hρ hw hρ0 hρR hw0 hθ hμ hr0 (by linarith)

end OTSelector.Geometry
