import OTSelector.Analysis.Calculus.SmoothCutoff
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.PositiveDensityInterpolationAction
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiDifferentiation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiDifferentiation`; the selected original proof blocks follow. -/
section

/-!
Conditions: A finite measure is carried on a compact set inside the smooth-test support; time-dependent tests and derivatives are continuous on the stated compact time strip.

Objects: Actual smooth cutoff tests preserving values and derivatives on support, extended flux pairings and differentiation of the affine-density test integral.

Proof detail: Use a locally-one smooth cutoff, preserve the original derivatives on support and pass the time derivative through the integral with compact uniform domination.

Sources: Terence Tao, Section 1.10.1, Lemma 1.10.1, pp. 134–135, and Exercise 1.10.6, p. 136 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=143); Jiří Lebl, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters) (https://www.jirka.org/ra/html/sec_diffunderint.html); D. H. Fremlin, Sections 234I–234L, pp. 27–29; especially 234L(c); Section 235K, p. 40 (https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf#page=27); Hassler Whitney, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1) (https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5).
Relation: Cutoff/Leibniz adapter for actual weak fluxes. The cutoff existence uses the smooth finite-dimensional bump interface, beyond the cited topological continuous-cutoff background. Smooth localization is also supported by the explicit normalized smooth partition construction in Whitney (1934), Sections 7–10.
-/

/-! Actual weak Neumann fluxes test smooth functions on the retained compact
support, and differentiation follows the original affine density interpolation. -/
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A genuinely smooth function agrees with an original supported test,
including its derivative, almost everywhere on the same retained compact. -/
theorem exists_original_smoothTest_ae_eq_on_support
    (K : Compacts (ι→ℝ)) (μ : Measure (ι→ℝ))
    {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀⊆interior (K:Set (ι→ℝ)))
    (hμ : ∀ᵐx∂μ,x∈K₀) (ψ : (ι→ℝ)→ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    ∃φ:𝓓_{K}(ι→ℝ,ℝ),(∀ᵐx∂μ,φ x=ψ x) ∧
      (∀ᵐx∂μ,fderiv ℝ φ x=fderiv ℝ ψ x) := by
  obtain ⟨χ,hχ,hχsupp,U,hU,hK₀U,hχone⟩:=exists_contDiff_cutoff K hK₀ hK₀K
  let φ : 𝓓_{K}(ι→ℝ,ℝ):=ContDiffMapSupportedIn.of_support_subset (hχ.mul hψ)
    ((Function.support_mul_subset_left χ ψ).trans hχsupp)
  have heq : ∀ᵐx∂μ,φ x=ψ x := by
    filter_upwards [hμ] with x hx
    change χ x*ψ x=ψ x
    rw [hχone x (hK₀U hx),one_mul]
  have hgrad : ∀ᵐx∂μ,fderiv ℝ φ x=fderiv ℝ ψ x := by
    filter_upwards [hμ] with x hx
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hU.mem_nhds (hK₀U hx)] with y hy
    change χ y*ψ y=ψ y
    rw [hχone y hy,one_mul]
  exact ⟨φ,heq,hgrad⟩

/-- The original weak flux pairs with every genuinely smooth function on the
retained compact support. The compactly supported test and its unchanged gradient
are constructed with the original larger test compact. -/
theorem original_weakNeumannFlux_pairing_of_smooth_on_support
    (K : Compacts (ι→ℝ)) (μ : Measure (ι→ℝ))
    {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀⊆interior (K:Set (ι→ℝ)))
    (hμ : ∀ᵐx∂μ,x∈K₀) (f g : (ι→ℝ)→ℝ)
    (j : (ι→ℝ)→EuclideanSpace ℝ ι)
    (hflux : ∀φ:𝓓_{K}(ι→ℝ,ℝ),
      (∫x,inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x))∂μ)=
        (∫x,φ x*f x∂μ)-(∫x,φ x*g x∂μ))
    (ψ : (ι→ℝ)→ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    (∫x,inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ ψ x))∂μ)=
      (∫x,ψ x*f x∂μ)-(∫x,ψ x*g x∂μ) := by
  obtain ⟨φ,heq,hgrad⟩:=exists_original_smoothTest_ae_eq_on_support K μ hK₀ hK₀K hμ ψ hψ
  calc
    _=(∫x,inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x))∂μ) :=
      integral_congr_ae (hgrad.mono fun x hx↦(congrArg (fun L↦inner ℝ (j x) (physicalCoordinateGradient ι L)) hx).symm)
    _=_:=hflux φ
    _=_:=by
      congr 1
      · exact integral_congr_ae (heq.mono fun x hx↦congrArg (fun r↦r*f x) hx)
      · exact integral_congr_ae (heq.mono fun x hx↦congrArg (fun r↦r*g x) hx)

/-- Uniform bounds for an actual time test and its true derivative dominate the
same affine-density product by the original L1 endpoint densities. -/
theorem norm_timeTest_density_derivative_le
    {p d t f g C T : ℝ} (hp : ‖p‖≤C) (hd : ‖d‖≤C)
    (ht : ‖t‖≤T) (hC : 0≤C) :
    ‖d*((1-t)*f+t*g)+p*(g-f)‖≤C*(T+2)*(‖f‖+‖g‖) := by
  have hT : 0≤T:=(norm_nonneg t).trans ht
  have hsum : 0≤‖f‖+‖g‖:=add_nonneg (norm_nonneg _) (norm_nonneg _)
  have h1 : ‖(1:ℝ)-t‖≤T+1 := by
    exact (norm_sub_le (1:ℝ) t).trans (by
      simpa only [norm_one,add_comm] using add_le_add_left ht 1)
  have hr : ‖(1-t)*f+t*g‖≤(T+1)*(‖f‖+‖g‖) := by
    calc
      _≤‖(1-t)*f‖+‖t*g‖:=norm_add_le _ _
      _=‖1-t‖*‖f‖+‖t‖*‖g‖:=by rw [norm_mul,norm_mul]
      _≤(T+1)*‖f‖+T*‖g‖:=add_le_add
        (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
        (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
      _≤_:=by nlinarith [norm_nonneg g]
  calc
    _≤‖d*((1-t)*f+t*g)‖+‖p*(g-f)‖:=norm_add_le _ _
    _=‖d‖*‖(1-t)*f+t*g‖+‖p‖*‖g-f‖:=by rw [norm_mul,norm_mul]
    _≤C*((T+1)*(‖f‖+‖g‖))+C*(‖f‖+‖g‖):=add_le_add
      (mul_le_mul hd hr (norm_nonneg _) hC)
      (mul_le_mul hp (by simpa only [add_comm] using norm_sub_le g f) (norm_nonneg _) hC)
    _=_:=by ring

omit [DecidableEq ι] in
/-- A time-dependent smooth test differentiates against the literal original
linear density interpolation. All domination is constructed from compact support
and L1 endpoint densities; no interpolation derivative or endpoint bound is assumed. -/
theorem hasDerivAt_integral_timeTest_residualDensityInterpolation
    (μ : Measure (ι→ℝ)) {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀)
    (hμ : ∀ᵐx∂μ,x∈K₀) (f g : (ι→ℝ)→ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (ψ d : ℝ→(ι→ℝ)→ℝ) {a b t : ℝ} (ht : t∈Ioo a b)
    (hψ : ContinuousOn (Function.uncurry ψ) (Icc a b×ˢuniv))
    (hd : ContinuousOn (Function.uncurry d) (Icc a b×ˢuniv))
    (hderiv : ∀s∈Icc a b,∀x,HasDerivAt (fun σ↦ψ σ x) (d s x) s) :
    Integrable (fun x↦d t x*residualDensityInterpolation f g t x+ψ t x*(g x-f x)) μ ∧
    HasDerivAt (fun σ↦∫x,ψ σ x*residualDensityInterpolation f g σ x∂μ)
      (∫x,d t x*residualDensityInterpolation f g t x+ψ t x*(g x-f x)∂μ) t := by
  have hψspace (s:ℝ) (hs:s∈Icc a b) : Continuous (ψ s) := by
    rw [←continuousOn_univ]
    exact hψ.comp (continuous_const.prodMk continuous_id).continuousOn (fun x _↦⟨hs,mem_univ _⟩)
  have hdspace (s:ℝ) (hs:s∈Icc a b) : Continuous (d s) := by
    rw [←continuousOn_univ]
    exact hd.comp (continuous_const.prodMk continuous_id).continuousOn (fun x _↦⟨hs,mem_univ _⟩)
  obtain ⟨Cψ,hCψ⟩:=(isCompact_Icc.prod hK₀).exists_bound_of_continuousOn
    (hψ.mono (Set.prod_mono subset_rfl (subset_univ _)))
  obtain ⟨Cd,hCd⟩:=(isCompact_Icc.prod hK₀).exists_bound_of_continuousOn
    (hd.mono (Set.prod_mono subset_rfl (subset_univ _)))
  let C:=max (max Cψ Cd) 0
  let T:=|a|+|b|+1
  let B:=C*(T+2)
  have hC : 0≤C:=le_max_right _ _
  have hT : 0≤T:=by dsimp [T];positivity
  have hB : 0≤B:=by dsimp [B];positivity
  have htime (s:ℝ) (hs:s∈Icc a b) : ‖s‖≤T := by
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> dsimp [T] <;> linarith [hs.1,hs.2,le_abs_self a,neg_abs_le a,le_abs_self b,neg_abs_le b]
  have hψbound (s:ℝ) (hs:s∈Icc a b) (x) (hx:x∈K₀) : ‖ψ s x‖≤C:=
    (hCψ (s,x) ⟨hs,hx⟩).trans ((le_max_left Cψ Cd).trans (le_max_left _ _))
  have hdbound (s:ℝ) (hs:s∈Icc a b) (x) (hx:x∈K₀) : ‖d s x‖≤C:=
    (hCd (s,x) ⟨hs,hx⟩).trans ((le_max_right Cψ Cd).trans (le_max_left _ _))
  let F:=fun s x↦ψ s x*residualDensityInterpolation f g s x
  let F':=fun s x↦d s x*residualDensityInterpolation f g s x+ψ s x*(g x-f x)
  have hFmeas (s) (hs:s∈Icc a b) : AEStronglyMeasurable (F s) μ :=
    (hψspace s hs).aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.const_mul _).add (hg.aestronglyMeasurable.const_mul _))
  have hF'meas : AEStronglyMeasurable (F' t) μ :=
    (((hdspace t ⟨ht.1.le,ht.2.le⟩).aestronglyMeasurable.mul
      ((hf.aestronglyMeasurable.const_mul _).add (hg.aestronglyMeasurable.const_mul _))).add
      ((hψspace t ⟨ht.1.le,ht.2.le⟩).aestronglyMeasurable.mul
        (hg.aestronglyMeasurable.sub hf.aestronglyMeasurable)))
  have hboundInt : Integrable (fun x↦B*(‖f x‖+‖g x‖)) μ:=(hf.norm.add hg.norm).const_mul B
  have hFint : Integrable (F t) μ := by
    apply hboundInt.mono' (hFmeas t ⟨ht.1.le,ht.2.le⟩)
    filter_upwards [hμ] with x hx
    have hp:=hψbound t ⟨ht.1.le,ht.2.le⟩ x hx
    have hr : ‖residualDensityInterpolation f g t x‖≤(T+1)*(‖f x‖+‖g x‖) := by
      dsimp only [residualDensityInterpolation]
      have h1:‖1-t‖≤T+1:=(norm_sub_le (1:ℝ) t).trans (by simpa only [norm_one,add_comm] using add_le_add_left (htime t ⟨ht.1.le,ht.2.le⟩) 1)
      calc
        _≤‖(1-t)*f x‖+‖t*g x‖:=norm_add_le _ _
        _≤(T+1)*‖f x‖+T*‖g x‖:=by
          rw [norm_mul,norm_mul]
          exact add_le_add (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right (htime t ⟨ht.1.le,ht.2.le⟩) (norm_nonneg _))
        _≤_:=by nlinarith [norm_nonneg (g x)]
    calc
      _=‖ψ t x‖*‖residualDensityInterpolation f g t x‖:=norm_mul _ _
      _≤C*((T+1)*(‖f x‖+‖g x‖)):=mul_le_mul hp hr (norm_nonneg _) hC
      _=C*(T+1)*(‖f x‖+‖g x‖):=by ring
      _≤C*(T+2)*(‖f x‖+‖g x‖):=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith : T+1≤T+2) hC)
        (add_nonneg (norm_nonneg _) (norm_nonneg _))
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le (Icc_mem_nhds ht.1 ht.2)
    (by filter_upwards [Icc_mem_nhds ht.1 ht.2] with s hs;exact hFmeas s hs) hFint hF'meas
    (by
      filter_upwards [hμ] with x hx
      intro s hs
      exact norm_timeTest_density_derivative_le (hψbound s hs x hx) (hdbound s hs x hx) (htime s hs) hC)
    hboundInt
  filter_upwards [] with x
  intro s hs
  have hr : HasDerivAt (fun σ↦residualDensityInterpolation f g σ x) (g x-f x) s := by
    have heq : (fun σ↦residualDensityInterpolation f g σ x)=(fun σ↦σ*(g x-f x)+f x) := by
      funext σ
      dsimp only [residualDensityInterpolation]
      ring
    rw [heq]
    have hlinear : HasDerivAt (fun σ:ℝ↦σ*(g x-f x)+f x) (1*(g x-f x)) s :=
      ((hasDerivAt_id s).mul_const (g x-f x)).add_const (f x)
    simpa only [one_mul] using hlinear
  exact (hderiv s hs x).mul hr

end OTSelector.Reconstruction

end
end
