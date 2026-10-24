import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import OTSelector.Analysis.Convex.TimeDependentSoftTests
import OTSelector.Analysis.HamiltonJacobiFluxYoung
import OTSelector.Analysis.Sobolev.AffineDensityIntegralDifferentiation
import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.DensityNeumannInterpolation
import OTSelector.Transport.PositiveDensityInterpolationAction
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiValue.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiValue`; the selected original proof blocks follow. -/
section

/-!
Conditions: A compactly carried finite measure, positive endpoint density lower bound and actual weak Neumann flux or discrepancy estimate.

Objects: Actual smooth-gradient integrability and the time-dependent soft-test endpoint value bound by half the inverse-density flux energy.

Proof detail: Localize the smooth tests without changing derivatives on support, differentiate their affine-density integrals, insert the true flux pairing and apply quadratic Young/Hamilton–Jacobi before integrating time.

Sources: Gabriel Peyré, Section 7.1, equations (7.1)–(7.5), pp. 112–113 (https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=116); Stephen Boyd, Section 3.3.2, Fenchel’s inequality and quadratic example, p. 94 (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=108); Jiří Lebl, Section 9.1, Theorem 9.1.1 (Leibniz integral rule), Exercise 9.1.5 (several parameters) (https://www.jirka.org/ra/html/sec_diffunderint.html); Terence Tao, Section 1.4, Theorem 1.4.13, p. 53 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=62).
Relation: Weak-flux/action comparison proved from actual test identities; no endpoint plan or unproved smoothing callback is assumed.
-/

/-! The actual shifted soft quadratic potential tests the original Neumann
flux along its same linear density interpolation, yielding the quadratic action. -/
open Set Filter MeasureTheory TopologicalSpace
open scoped Distributions RealInnerProductSpace ContDiff
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
variable {ι I : Type*} [Fintype ι] [DecidableEq ι] [Fintype I] [Nonempty I]

/-- The actual smooth test gradient pairs integrably with the same L2 flux on
its retained original compact support. -/
theorem integrable_original_smoothGradient_inner_on_support
    (K : Compacts (ι→ℝ)) (μ : Measure (ι→ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀⊆interior (K:Set (ι→ℝ)))
    (hμ : ∀ᵐx∂μ,x∈K₀) (j : Lp (EuclideanSpace ℝ ι) 2 μ)
    (ψ : (ι→ℝ)→ℝ) (hψ : ContDiff ℝ ∞ ψ) :
    Integrable (fun x↦inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ ψ x))) μ := by
  obtain ⟨φ,_hφ,hgrad⟩:=exists_original_smoothTest_ae_eq_on_support K μ hK₀ hK₀K hμ ψ hψ
  apply (L2.integrable_inner j (smoothPhysicalGradientLtwo K μ φ)).congr
  filter_upwards [smoothPhysicalGradientLtwo_ae K μ φ,hgrad] with x hx hg
  exact congrArg (fun p↦inner ℝ (j x) p) (hx.trans (congrArg (physicalCoordinateGradient ι) hg))

/-- The genuine time-dependent quadratic soft test has its signed endpoint
value bounded by half the actual Neumann energy divided by the common positive
original density floor. No static endpoint HJ condition is assumed. -/
theorem neumannQuadraticSoftTest_valueComparison_of_flux
    (K : Compacts (ι→ℝ)) (μ : Measure (ι→ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀⊆interior (K:Set (ι→ℝ)))
    (hμ : ∀ᵐx∂μ,x∈K₀) (f g : (ι→ℝ)→ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ : ℝ} (hρ : 0<ρ) (hfl : ∀ᵐx∂μ,ρ≤f x) (hgl : ∀ᵐx∂μ,ρ≤g x)
    (j : Lp (EuclideanSpace ℝ ι) 2 μ)
    (hflux : ∀φ:𝓓_{K}(ι→ℝ,ℝ),
      (∫x,inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x))∂μ)=
        (∫x,φ x*f x∂μ)-(∫x,φ x*g x∂μ))
    {ε δ : ℝ} (hε : ε≠0) (hδ : 0<δ) (a : I→ℝ) (y : I→EuclideanSpace ℝ ι) :
    (∫x,neumannQuadraticSoftTest ε a y δ 1 x*g x∂μ)-
      (∫x,neumannQuadraticSoftTest ε a y δ 0 x*f x∂μ)≤
        ρ⁻¹*(∫x,‖j x‖^2∂μ)/2 := by
  let ψ:=neumannQuadraticSoftTest ε a y δ
  let d:=neumannQuadraticSoftTimeDerivative ε a y δ
  let p:=fun t x↦physicalCoordinateGradient ι (fderiv ℝ (ψ t) x)
  let mean:=fun t↦∫x,ψ t x*residualDensityInterpolation f g t x∂μ
  let rate:=fun t↦(∫x,d t x*residualDensityInterpolation f g t x∂μ)-
    (∫x,inner ℝ (j x) (p t x)∂μ)
  let budget:=ρ⁻¹*(∫x,‖j x‖^2∂μ)/2
  have hjI : Integrable (fun x↦‖j x‖^2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable j)).mp (Lp.memLp j)
  have hTime : ∀t∈Icc (-δ/2) (1+δ/2),t+δ≠0 := by
    intro t ht
    have : 0<t+δ:=by linarith [ht.1]
    exact this.ne'
  have hjoint:=continuousOn_neumannQuadraticSoftTest_timeDerivative ε a y δ (-δ/2) (1+δ/2) hTime
  have hpacket (t:ℝ) (ht:t∈Icc (0:ℝ) 1) : HasDerivAt mean (rate t) t ∧ rate t≤budget := by
    have htd : t+δ≠0:=(add_pos_of_nonneg_of_pos ht.1 hδ).ne'
    have hψ : ContDiff ℝ ∞ (ψ t):=contDiff_neumannQuadraticSoftTest ε a y δ t htd
    obtain ⟨φ,hφ,_hgrad⟩:=exists_original_smoothTest_ae_eq_on_support K μ hK₀ hK₀K hμ (ψ t) hψ
    have hψf : Integrable (fun x↦ψ t x*f x) μ:=
      (smoothTest_mul_density_integrable K μ φ hf).congr (hφ.mono fun x hx↦congrArg (fun r↦r*f x) hx)
    have hψg : Integrable (fun x↦ψ t x*g x) μ:=
      (smoothTest_mul_density_integrable K μ φ hg).congr (hφ.mono fun x hx↦congrArg (fun r↦r*g x) hx)
    have hψgf : Integrable (fun x↦ψ t x*(g x-f x)) μ:=
      (hψg.sub hψf).congr (ae_of_all _ fun x↦by
        change ψ t x*g x-ψ t x*f x=ψ t x*(g x-f x)
        ring)
    have hdiff:=hasDerivAt_integral_timeTest_residualDensityInterpolation μ hK₀ hμ f g hf hg ψ d
      (show t∈Ioo (-δ/2) (1+δ/2) by constructor <;> linarith [ht.1,ht.2]) hjoint.1 hjoint.2
      (fun s hs x↦(neumannQuadraticSoftTest_pointwise ε hε a y δ s (hTime s hs) x).1)
    have hdr : Integrable (fun x↦d t x*residualDensityInterpolation f g t x) μ:=
      (hdiff.1.sub hψgf).congr (ae_of_all _ fun x↦by
        change (d t x*residualDensityInterpolation f g t x+ψ t x*(g x-f x))-ψ t x*(g x-f x)=_
        ring)
    have hjp : Integrable (fun x↦inner ℝ (j x) (p t x)) μ:=
      integrable_original_smoothGradient_inner_on_support K μ hK₀ hK₀K hμ j (ψ t) hψ
    have hfluxψ:=original_weakNeumannFlux_pairing_of_smooth_on_support K μ hK₀ hK₀K hμ f g
      (fun x↦j x) hflux (ψ t) hψ
    have hgf : (∫x,ψ t x*(g x-f x)∂μ)=-(∫x,inner ℝ (j x) (p t x)∂μ) := by
      have heq : (fun x↦ψ t x*(g x-f x))=(fun x↦ψ t x*g x-ψ t x*f x):=funext fun x↦by ring
      rw [heq,integral_sub hψg hψf]
      change _=-(∫x,inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ (ψ t) x))∂μ)
      rw [hfluxψ]
      ring
    have hderiv : HasDerivAt mean (rate t) t := by
      convert hdiff.2 using 1
      rw [integral_add hdr hψgf,hgf]
      rfl
    refine ⟨hderiv,?_⟩
    have hbound : ∀ᵐx∂μ,d t x*residualDensityInterpolation f g t x-inner ℝ (j x) (p t x)≤
        ρ⁻¹*‖j x‖^2/2 := by
      filter_upwards [hfl,hgl] with x hx hy
      have hr:=residualDensityInterpolation_lower ht hx hy
      have hHJ : d t x+‖p t x‖^2/2≤0 := by
        dsimp only [p]
        rw [(neumannQuadraticSoftTest_pointwise ε hε a y δ t htd x).2.1]
        exact (neumannQuadraticSoftTest_pointwise ε hε a y δ t htd x).2.2
      exact (hamiltonJacobi_flux_young (j x) (p t x) (hρ.trans_le hr) hHJ).trans
        (div_le_div_of_nonneg_right (by
          simpa only [div_eq_mul_inv,mul_comm] using
            div_le_div_of_nonneg_left (sq_nonneg ‖j x‖) hρ hr) (by norm_num))
    have hb:=integral_mono_ae (hdr.sub hjp) ((hjI.const_mul ρ⁻¹).div_const 2) hbound
    change (∫x,d t x*residualDensityInterpolation f g t x-inner ℝ (j x) (p t x)∂μ)≤_ at hb
    rw [integral_sub hdr hjp,integral_div,integral_const_mul] at hb
    exact hb
  have hFTC:=intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num : (0:ℝ)≤1)
    (fun t ht↦(hpacket t ht).1.continuousAt.continuousWithinAt)
    (fun t ht↦(hpacket t ⟨ht.1.le,ht.2.le⟩).1.hasDerivWithinAt)
    (show IntegrableOn (fun _t:ℝ↦budget) (Icc (0:ℝ) 1) volume from integrable_const _)
    (fun t ht↦(hpacket t ⟨ht.1.le,ht.2.le⟩).2)
  simpa only [mean,residualDensityInterpolation,sub_self,zero_mul,one_mul,sub_zero,add_zero,zero_add,
    intervalIntegral.integral_const,one_smul] using hFTC

/-- The original gradient discrepancy itself constructs the same flux and its
quadratic soft-test endpoint budget, with the exact Neumann energy constant. -/
theorem originalDensity_neumannQuadraticSoft_signedValue_le
    (K : Compacts (ι→ℝ)) (μ : Measure (ι→ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι→ℝ)} (hK₀ : IsCompact K₀) (hK₀K : K₀⊆interior (K:Set (ι→ℝ)))
    (hμ : ∀ᵐx∂μ,x∈K₀) (f g : (ι→ℝ)→ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    {ρ C : ℝ} (hρ : 0<ρ) (hC : 0≤C)
    (hfl : ∀ᵐx∂μ,ρ≤f x) (hgl : ∀ᵐx∂μ,ρ≤g x)
    (hbound : ∀φ:𝓓_{K}(ι→ℝ,ℝ),
      ‖(∫x,φ x*f x∂μ)-(∫x,φ x*g x∂μ)‖≤C*‖smoothPhysicalGradientLtwo K μ φ‖)
    {ε δ : ℝ} (hε : ε≠0) (hδ : 0<δ) (a : I→ℝ) (y : I→EuclideanSpace ℝ ι) :
    (∫x,neumannQuadraticSoftTest ε a y δ 1 x*g x∂μ)-
      (∫x,neumannQuadraticSoftTest ε a y δ 0 x*f x∂μ)≤ρ⁻¹*C^2/2 := by
  obtain ⟨j,_hjI,hjE,hjtest,_hactI,_hactE⟩:=exists_originalDensity_weakNeumannInterpolation K μ f g hf hg hρ hC hfl hgl hbound
  have hflux (φ:𝓓_{K}(ι→ℝ,ℝ)) :
      (∫x,inner ℝ (j x) (physicalCoordinateGradient ι (fderiv ℝ φ x))∂μ)=
        (∫x,φ x*f x∂μ)-(∫x,φ x*g x∂μ) := by
    have hh:=(hasDerivAt_residualDensityInterpolation_test K μ φ hf hg 0).unique (hjtest φ 0)
    linarith
  exact (neumannQuadraticSoftTest_valueComparison_of_flux K μ hK₀ hK₀K hμ f g hf hg hρ hfl hgl j hflux hε hδ a y).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hjE (inv_nonneg.mpr hρ.le)) (by norm_num))

end OTSelector.Reconstruction

end
end
