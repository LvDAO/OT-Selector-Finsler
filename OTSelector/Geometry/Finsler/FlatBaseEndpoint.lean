import OTSelector.Analysis.Calculus.Variational.CalibratedEnergyIdentities
import OTSelector.Analysis.Calculus.Variational.HamiltonianFlatBase
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.CompleteChartBox
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Jacobi.PositiveEndpointKernel

/-!
# Geometry.Finsler.FlatBaseEndpoint

* **Conditions:** The original energy has zero base Hessian columns along the actual central curve, with genuine initial tangent and positive vertical Hessian; affine calibration is a sufficient geometric specialization.
* **Objects:** Zero actual endpoint-fixed phase kernel and invertibility of the original endpoint map differential.
* **Proof detail:** The true variational equation makes momentum constant and its position derivative a positive inverse-Hessian response; endpoint fixation forces zero momentum and initial phase.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): The zero-base-column hypothesis is explicit or derived from the stated affine calibrated tube; no unrelated Jacobi model is substituted.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFlatBaseEndpoint.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFlatBaseEndpoint`; the selected original proof blocks follow. -/
section

/-!
# Nondegeneracy of the actual Finsler endpoint map on a flat-base energy tube

Zero base columns of the original energy Hessian along the actual central curve give
the true parameter variation a constant momentum and a positive velocity response.
Its endpoint-fixed kernel is zero. The genuine initial-tangent identity then makes
the actual endpoint differential invertible. Neither a Jacobi model nor an endpoint
nonconjugacy hypothesis is supplied independently of the intrinsic family.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

/-- Actual parameter variations of the same intrinsic family obey the positive
inverse-Hessian equation when the original energy has zero base Hessian columns. -/
theorem hasDerivAt_chartMomentumVariation_of_hessian_base_zero
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w : W} (hw : w ∈ B) (old : M) (t : ℝ)
    (hx : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hzero : ∀ u : E, fderiv ℝ (fderiv ℝ (F.chartEnergy old))
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t) (u, 0) = 0) (ξ : W) :
    HasDerivAt (fun s ↦ fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, s)) w ξ)
      (ContinuousLinearMap.inverse (verticalEnergyHessian (F.chartEnergy old)
        ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t,
          deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t))
        (fderiv ℝ (fun v ↦ F.chartMomentumFamily old Γ (v, t)) w ξ).2, 0) t := by
  obtain ⟨e, r, he, hs, hi, hr, _, _, _, hm, hODE⟩ :=
    hF.exists_chartMomentumFamily_box hB hEL hG hw old t hx
  have ht : (w, t) ∈ Metric.ball w r ×ˢ Ioo (t - r) (t + r) :=
    ⟨Metric.mem_ball_self hr, by constructor <;> linarith⟩
  have hz := (hF.chartTangent_of_isEulerLagrangeAt (hEL w hw t (mem_univ _)) old hx).2
  have hident : e.symm (F.chartMomentumFamily old Γ (w, t)) =
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t) := by
    apply hF.injOn_parametricLegendre_chartEnergy old (hs (e.map_target (hm ht))) hz
    have h := e.right_inv (hm ht)
    rw [he] at h
    exact h
  have hflat : ∀ u : E, fderiv ℝ (fderiv ℝ (F.chartEnergy old))
      (e.symm (F.chartMomentumFamily old Γ (w, t))) (u, 0) = 0 := by
    simpa only [hident] using hzero
  have hpos : ∀ u : E, u ≠ 0 → 0 < verticalEnergyHessian (F.chartEnergy old)
      (e.symm (F.chartMomentumFamily old Γ (w, t))) u u := by
    rw [hident]
    exact fun u hu ↦ hF.chartEnergy_hessian_pos old hz hu
  have hd := (hODE (w, t) ht).2 ξ
  rw [localHamiltonianVectorField_fderiv_of_hessian_base_zero he
    ((hF.contDiffOn_chartEnergy old).mono hs) hi (hm ht) hflat hpos, hident] at hd
  exact hd

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The endpoint-fixed kernel of the actual momentum-family parameter derivative is
zero, using the original initial tangent and original energy Hessian along the curve. -/
theorem chartMomentumFamily_endpoint_kernel_eq_zero
    (hF : F.IsSmoothStronglyConvex) (old : M) {a b : ℝ} (hab : a < b)
    {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old)
    (hx : ∀ t ∈ Icc a b, Γ z t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hzero : ∀ t ∈ Icc a b, ∀ u : E, fderiv ℝ (fderiv ℝ (F.chartEnergy old))
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ z) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z) t) (u, 0) = 0)
    {ξ : E × E}
    (ha : (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, a)) z ξ).1 = 0)
    (hb : (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, b)) z ξ).1 = 0) : ξ = 0 := by
  let R := fun t ↦ fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) z ξ
  let C := fun t ↦ ContinuousLinearMap.inverse (verticalEnergyHessian (F.chartEnergy old)
    ((extChartAt 𝓘(ℝ, E) old ∘ Γ z) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z) t))
  have hODE (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt R (C t (R t).2, 0) t :=
    hF.hasDerivAt_chartMomentumVariation_of_hessian_base_zero
      (isOpen_chartEnergyDomain old) hEL hG hz old t (hx t ht) (hzero t ht) ξ
  have hp0 : (R a).2 = 0 := by
    apply momentum_eq_zero_of_endpoint_fixed_positive_variation hab
      (fun t ht ↦ (hODE t ht).fst) (fun t ht ↦ (hODE t ht).snd) ?_ ha hb
    intro t ht p hp
    exact inverse_verticalEnergyHessian_pos (fun u hu ↦ hF.chartEnergy_hessian_pos old
      (hF.chartTangent_of_isEulerLagrangeAt (hEL z hz t (mem_univ _)) old (hx t ht)).2 hu) hp
  have hR : R a = 0 := Prod.ext ha hp0
  have heq : (fun w ↦ F.chartMomentumFamily old Γ (w, a)) =ᶠ[𝓝 z]
      parametricLegendre (F.chartEnergy old) := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz] with w hw
    exact hF.chartMomentum_of_tangent_eq (hEL w hw a (mem_univ _)) old hw (hinit w hw)
  have hR' : fderiv ℝ (parametricLegendre (F.chartEnergy old)) z ξ = 0 := by
    simpa only [R, heq.fderiv_eq] using hR
  have hinj := (parametricLegendre_fderiv_bijective
    ((hF.contDiffOn_chartEnergy old).contDiffAt ((isOpen_chartEnergyDomain old).mem_nhds hz))
    (fun u hu ↦ hF.chartEnergy_hessian_pos old hz hu)).1
  exact hinj (hR'.trans (_root_.map_zero _).symm)

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- The original Hessian identities imply invertibility of the actual endpoint map;
no endpoint differential or independent Jacobi rank assumption is supplied. -/
theorem isInvertible_chartEndpointMap_of_hessian_base_zero
    (hF : F.IsSmoothStronglyConvex) (old : M) {a b : ℝ} (hab : a < b)
    {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old)
    (hx : ∀ t ∈ Icc a b, Γ z t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hzero : ∀ t ∈ Icc a b, ∀ u : E, fderiv ℝ (fderiv ℝ (F.chartEnergy old))
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ z) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z) t) (u, 0) = 0) :
    (fderiv ℝ (chartEndpointMap old Γ b) z).IsInvertible := by
  obtain ⟨e, r, _, _, _, hr, _, _, hΨ, _, _⟩ :=
    hF.exists_chartMomentumFamily_box (isOpen_chartEnergyDomain old) hEL hG hz old b
      (hx b (right_mem_Icc.mpr hab.le))
  have hzb : (z, b) ∈ Metric.ball z r ×ˢ Ioo (b - r) (b + r) :=
    ⟨Metric.mem_ball_self hr, by constructor <;> linarith⟩
  have hd : DifferentiableAt ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, b)) z :=
    ((hΨ.contDiffAt ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hzb)).comp z
      (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)
  have hDP : HasFDerivAt (chartEndpointMap old Γ b)
      ((ContinuousLinearMap.fst ℝ E E).prod
        ((ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).comp
          (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, b)) z))) z :=
    hasFDerivAt_fst.prodMk hd.hasFDerivAt.fst
  have heq : (fun w ↦ F.chartMomentumFamily old Γ (w, a)) =ᶠ[𝓝 z]
      parametricLegendre (F.chartEnergy old) := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz] with w hw
    exact hF.chartMomentum_of_tangent_eq (hEL w hw a (mem_univ _)) old hw (hinit w hw)
  have hinj : Function.Injective (fderiv ℝ (chartEndpointMap old Γ b) z) := by
    apply (injective_iff_map_eq_zero _).2
    intro ξ hξ
    rw [hDP.fderiv] at hξ
    apply hF.chartMomentumFamily_endpoint_kernel_eq_zero old hab hEL hinit hG hz hx hzero
    · rw [heq.fderiv_eq, parametricLegendre_fderiv_eq
        ((hF.contDiffOn_chartEnergy old).contDiffAt
          ((isOpen_chartEnergyDomain old).mem_nhds hz))]
      exact congrArg Prod.fst hξ
    · exact congrArg Prod.snd hξ
  exact ⟨(LinearEquiv.ofBijective
    (fderiv ℝ (chartEndpointMap old Γ b) z).toLinearMap
      ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩).toContinuousLinearEquiv, rfl⟩

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- A calibrated unit-velocity coordinate tube gives an invertible actual endpoint
map. The original energy Hessian identities are derived from length calibration. -/
theorem isInvertible_chartEndpointMap_of_calibrated_tube
    (hF : F.IsSmoothStronglyConvex) (old : M) {a b : ℝ} (hab : a < b)
    {Γ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old)
    (hx : ∀ t ∈ Icc a b, Γ z t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ F.chartLength old (x, v))
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ Γ z) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z) t = v₀) :
    (fderiv ℝ (chartEndpointMap old Γ b) z).IsInvertible := by
  apply hF.isInvertible_chartEndpointMap_of_hessian_base_zero old hab hEL hinit hG hz hx
  intro t ht u
  rw [hvelocity t ht]
  obtain ⟨_, _, _, _, _, _, hflat, _⟩ :=
    hF.chartEnergy_calibrated_identities old hU hsub p hp hunit hbound (hspace t ht)
  exact hflat u

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
