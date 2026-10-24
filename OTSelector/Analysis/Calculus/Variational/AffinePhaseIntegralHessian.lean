import OTSelector.Analysis.Calculus.AffineEndpointVariation
import OTSelector.Analysis.Calculus.Variational.AffineEndpointParameter
import OTSelector.Analysis.Calculus.Variational.CompactSmoothIntegral
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.AffinePhaseIntegralHessian.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.AffinePhaseIntegralHessian`; the selected original proof blocks follow. -/
section

/-!
Conditions: The stated smooth actual path and Lagrangian, with the common compact admissible perturbation set and Hessian bound.

Objects: Smooth endpoint-parameter action and its twice-differentiated integral, with the explicit interval/operator constant.

Proof detail: Use affine endpoint perturbation, differentiate the actual action twice under the integral and bound the bilinear composition by the perturbation norm squared.

Sources: Jiří Lebl, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters) (https://www.jirka.org/ra/html/sec_diffunderint.html); Gerald Teschl, Section 8.3, p. 238, equations (8.33)–(8.36); Problem 8.7, p. 241 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249); Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46).
Relation: Quantitative action-Hessian corollary, proved from the true integral action rather than an assumed endpoint formula.
-/

/-!
# Actual Hessians of affine endpoint phase integrals

The original scalar integrand is evaluated on the actual affine endpoint path and its
actual time velocity. Differentiating twice gives its genuine endpoint Hessian, with
an explicit bound uniform in every central path whose varied phases satisfy the same
original Hessian bound. No regularity of a selected family of central paths is assumed.
-/

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem hasFDerivAt_intervalIntegral_of_partial
    {f : E × ℝ → ℝ} {g : E × ℝ → E →L[ℝ] ℝ} {O : Set (E × ℝ)}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) {a b : ℝ} (hab : a ≤ b)
    {z : E} (htrace : ∀ t ∈ Icc a b, (z, t) ∈ O)
    (hg : ∀ t ∈ Icc a b, HasFDerivAt (fun w ↦ f (w, t)) (g (z, t)) z) :
    HasFDerivAt (fun w ↦ ∫ t in a..b, f (w, t)) (∫ t in a..b, g (z, t)) z := by
  have hd := hasFDerivAt_intervalIntegral_of_contDiffOn_normed hO
    (hf.of_le (by simp)) hab htrace
  have heq : (∫ t in a..b, (fderiv ℝ f (z, t)).comp
      (ContinuousLinearMap.inl ℝ E ℝ)) = ∫ t in a..b, g (z, t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by
      rw [uIcc_of_le hab] at ht
      exact ht
    have hdjoint : HasFDerivAt (fun w ↦ f (w, t))
        ((fderiv ℝ f (z, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) z :=
      ((hf.contDiffAt (hO.mem_nhds (htrace t ht'))).differentiableAt
      (by simp)).hasFDerivAt.comp z (hasFDerivAt_prodMk_left z t)
    exact hdjoint.unique (hg t ht')
  rwa [heq] at hd

/-- The constructed scalar integral is smooth in its endpoint on any open endpoint
set whose actual varied phases remain in the original smoothness domain. -/
theorem contDiffOn_intervalIntegral_affineEndpointPhase
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I)
    {L : E × E → ℝ} {D : Set (E × E)} (hD : IsOpen D)
    (hL : ContDiffOn ℝ ∞ L D) {a b : ℝ} (hab : a ≤ b)
    (hseg : Icc a b ⊆ I) {U : Set E} (hU : IsOpen U)
    (hphase : ∀ z ∈ U, ∀ t ∈ Icc a b, affineEndpointPhase x a b (z, t) ∈ D) :
    ContDiffOn ℝ ∞ (fun z ↦ ∫ t in a..b, L (affineEndpointPhase x a b (z, t))) U := by
  let O := (univ ×ˢ I) ∩ (affineEndpointPhase x a b) ⁻¹' D
  have hp := contDiffOn_affineEndpointPhase hI hx a b
  have hO : IsOpen O := hp.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hI) hD
  have hf : ContDiffOn ℝ ∞ (fun q ↦ L (affineEndpointPhase x a b q)) O :=
    hL.comp (hp.mono inter_subset_left) (fun _ hq ↦ hq.2)
  exact contDiffOn_infty_intervalIntegral_of_contDiffOn hU hO hf hab
    (fun z hz t ht ↦ ⟨⟨mem_univ _, hseg ht⟩, hphase z hz t ht⟩)

/-- The actual second endpoint derivative is the integral of the original Hessian
pulled back along the explicit affine endpoint linear map in both arguments. -/
theorem hasFDerivAt_fderiv_intervalIntegral_affineEndpointPhase
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I)
    {L : E × E → ℝ} {D : Set (E × E)} (hD : IsOpen D)
    (hL : ContDiffOn ℝ ∞ L D) {a b : ℝ} (hab : a ≤ b)
    (hseg : Icc a b ⊆ I) {U : Set E} (hU : IsOpen U)
    (hphase : ∀ z ∈ U, ∀ t ∈ Icc a b, affineEndpointPhase x a b (z, t) ∈ D)
    {z : E} (hz : z ∈ U) :
    HasFDerivAt
      (fderiv ℝ (fun w ↦ ∫ t in a..b, L (affineEndpointPhase x a b (w, t))))
      (∫ t in a..b,
        ((ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip
          (affineEndpointParameterMap a b t)).comp
          ((fderiv ℝ (fderiv ℝ L) (affineEndpointPhase x a b (z, t))).comp
            (affineEndpointParameterMap a b t))) z := by
  let O := (univ ×ˢ I) ∩ (affineEndpointPhase x a b) ⁻¹' D
  let f : E × ℝ → ℝ := fun q ↦ L (affineEndpointPhase x a b q)
  let g : E × ℝ → E →L[ℝ] ℝ := fun q ↦
    (fderiv ℝ L (affineEndpointPhase x a b q)).comp
      (affineEndpointParameterMap a b q.2)
  have hp := contDiffOn_affineEndpointPhase hI hx a b
  have hO : IsOpen O := hp.continuousOn.isOpen_inter_preimage (isOpen_univ.prod hI) hD
  have hf : ContDiffOn ℝ ∞ f O :=
    hL.comp (hp.mono inter_subset_left) (fun _ hq ↦ hq.2)
  have hg : ContDiffOn ℝ ∞ g O :=
    ((hL.fderiv_of_isOpen hD (m := ∞) (by simp)).comp
      (hp.mono inter_subset_left) (fun _ hq ↦ hq.2)).clm_comp
        ((contDiff_affineEndpointParameterMap (E := E) a b).comp contDiff_snd).contDiffOn
  have htrace (w : E) (hw : w ∈ U) (t : ℝ) (ht : t ∈ Icc a b) : (w, t) ∈ O :=
    ⟨⟨mem_univ _, hseg ht⟩, hphase w hw t ht⟩
  have hfirst (w : E) (hw : w ∈ U) :
      HasFDerivAt (fun v ↦ ∫ t in a..b, f (v, t)) (∫ t in a..b, g (w, t)) w := by
    apply hasFDerivAt_intervalIntegral_of_partial hO hf hab (htrace w hw)
    intro t ht
    exact ((hL.contDiffAt (hD.mem_nhds (hphase w hw t ht))).differentiableAt
      (by simp)).hasFDerivAt.comp w (hasFDerivAt_affineEndpointPhase_parameter x a b t w)
  have heq : fderiv ℝ (fun w ↦ ∫ t in a..b, f (w, t)) =ᶠ[𝓝 z]
      (fun w ↦ ∫ t in a..b, g (w, t)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (hfirst w hw).fderiv
  have hd := hasFDerivAt_intervalIntegral_of_contDiffOn_normed hO
    (hg.of_le (by simp)) hab (htrace z hz)
  have hi : (∫ t in a..b, (fderiv ℝ g (z, t)).comp
      (ContinuousLinearMap.inl ℝ E ℝ)) = ∫ t in a..b,
        ((ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip
          (affineEndpointParameterMap a b t)).comp
          ((fderiv ℝ (fderiv ℝ L) (affineEndpointPhase x a b (z, t))).comp
            (affineEndpointParameterMap a b t)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc a b := by
      rw [uIcc_of_le hab] at ht
      exact ht
    have hdg : DifferentiableAt ℝ g (z, t) :=
      (hg.contDiffAt (hO.mem_nhds (htrace z hz t ht'))).differentiableAt (by simp)
    have hdg' : HasFDerivAt g (fderiv ℝ g (z, t)) (z, t) := hdg.hasFDerivAt
    have hpair : HasFDerivAt (fun w : E ↦ (w, t))
        (ContinuousLinearMap.inl ℝ E ℝ) z := hasFDerivAt_prodMk_left z t
    have hdjoint : HasFDerivAt (fun w ↦ g (w, t))
        ((fderiv ℝ g (z, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) z :=
      HasFDerivAt.comp (g := g) (g' := fderiv ℝ g (z, t))
        (f := fun w : E ↦ (w, t)) (f' := ContinuousLinearMap.inl ℝ E ℝ) z hdg' hpair
    have hLt := (hL.fderiv_of_isOpen hD (m := ∞) (by simp)).contDiffAt
      (hD.mem_nhds (hphase z hz t ht'))
    have hdpartial := (hLt.differentiableAt (by simp)).hasFDerivAt.comp z
      (hasFDerivAt_affineEndpointPhase_parameter x a b t z)
    have hcomp := hdpartial.clm_comp
      (hasFDerivAt_const (affineEndpointParameterMap (E := E) a b t) z)
    have hunique := hdjoint.unique hcomp
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using hunique
  rw [hi] at hd
  exact hd.congr_of_eventuallyEq heq

/-- A bound on the actual original integrand Hessian along the varied central time
trace bounds the actual endpoint Hessian of its integral, uniformly in the central path. -/
theorem norm_fderiv_fderiv_intervalIntegral_affineEndpointPhase_le
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I)
    {L : E × E → ℝ} {D : Set (E × E)} (hD : IsOpen D)
    (hL : ContDiffOn ℝ ∞ L D) {a b : ℝ} (hab : a < b)
    (hseg : Icc a b ⊆ I) {U : Set E} (hU : IsOpen U)
    (hphase : ∀ z ∈ U, ∀ t ∈ Icc a b, affineEndpointPhase x a b (z, t) ∈ D)
    {z : E} (hz : z ∈ U) {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hbound : ∀ t ∈ Icc a b,
      ‖fderiv ℝ (fderiv ℝ L) (affineEndpointPhase x a b (z, t))‖ ≤ M₂) :
    ‖fderiv ℝ (fderiv ℝ
      (fun w ↦ ∫ t in a..b, L (affineEndpointPhase x a b (w, t)))) z‖ ≤
        (b - a) * M₂ * (1 + (b - a)⁻¹) ^ 2 := by
  rw [(hasFDerivAt_fderiv_intervalIntegral_affineEndpointPhase
    hI hx hD hL hab.le hseg hU hphase hz).fderiv]
  have hA : 0 ≤ 1 + (b - a)⁻¹ := by positivity
  have hbnd : ∀ t ∈ Ι a b,
      ‖((ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip
        (affineEndpointParameterMap a b t)).comp
          ((fderiv ℝ (fderiv ℝ L) (affineEndpointPhase x a b (z, t))).comp
            (affineEndpointParameterMap a b t))‖ ≤ M₂ * (1 + (b - a)⁻¹) ^ 2 := by
    intro t ht
    have ht' : t ∈ Icc a b := by
      rw [uIoc_of_le hab.le] at ht
      exact ⟨ht.1.le, ht.2⟩
    let Q := affineEndpointParameterMap (E := E) a b t
    have hQ : ‖Q‖ ≤ 1 + (b - a)⁻¹ := norm_affineEndpointParameterMap_le hab ht'
    have hc : ‖(ContinuousLinearMap.compL ℝ E (E × E) ℝ).flip Q‖ ≤ ‖Q‖ := by
      apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
      intro l
      exact (ContinuousLinearMap.opNorm_comp_le l Q).trans_eq (mul_comm _ _)
    calc
      _ ≤ ‖Q‖ * (‖fderiv ℝ (fderiv ℝ L) (affineEndpointPhase x a b (z, t))‖ *
          ‖Q‖) := (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hc (ContinuousLinearMap.opNorm_comp_le _ _)
              (norm_nonneg _) (norm_nonneg _))
      _ ≤ (1 + (b - a)⁻¹) * (M₂ * (1 + (b - a)⁻¹)) := by
        gcongr
        exact hbound t ht'
      _ = M₂ * (1 + (b - a)⁻¹) ^ 2 := by ring
  calc
    _ ≤ (M₂ * (1 + (b - a)⁻¹) ^ 2) * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hbnd
    _ = (b - a) * M₂ * (1 + (b - a)⁻¹) ^ 2 := by
      rw [abs_of_pos (sub_pos.mpr hab)]
      ring

end OTSelector.Geometry

end
end
