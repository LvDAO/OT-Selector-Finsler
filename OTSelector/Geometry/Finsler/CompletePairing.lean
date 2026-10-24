import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Symplectic.CotangentChartPairing
import OTSelector.Geometry.Symplectic.CotangentFamilyTransition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompletePairing.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompletePairing`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CompletePairing

* **Conditions:** A jointly C2 intrinsic Finsler Euler–Lagrange family, with arbitrary legal endpoint charts and real times.
* **Objects:** Chart-independent conservation of canonical pairing between actual parameter variations.
* **Proof detail:** Differentiate pairing using the genuine linearized Hamiltonian equation and Hessian symmetry, transfer by cotangent charts and use connectedness of time.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): The symplectic-flow conservation is derived directly; the source canonical-form formulas supply the algebra and coordinate rule.
-/

/-!
# Canonical pairing along complete intrinsic Finsler families

Actual chart momenta transform by the genuine cotangent lift. Their true parameter
variations have chart-independent canonical pairing. Local Hamiltonian dynamics and
actual Hessian symmetry make that scalar stationary; connected real time then gives
conservation through arbitrarily many changes of chart and Legendre inverse branch.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem hamiltonian_pairing_derivative_zero
    {L : E × E → ℝ} {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre L)
    (hL : ContDiffOn ℝ ∞ L e.source) (hG : ContDiffOn ℝ ∞ e.symm e.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    {U V : ℝ → E × (E →L[ℝ] ℝ)} {t : ℝ}
    (hu : HasDerivAt U (fderiv ℝ (localHamiltonianVectorField L e) p (U t)) t)
    (hv : HasDerivAt V (fderiv ℝ (localHamiltonianVectorField L e) p (V t)) t) :
    HasDerivAt (fun s ↦ canonicalPhasePairing (U s) (V s)) 0 t := by
  have h := localHamiltonian_hessian_symm hL hG hp (U t) (V t)
  rw [localHamiltonian_hessian_field_identity he hL hG hp,
    localHamiltonian_hessian_field_identity he hL hG hp] at h
  have hu₁ : HasDerivAt (fun s ↦ (U s).1)
      (fderiv ℝ (localHamiltonianVectorField L e) p (U t)).1 t := hu.fst
  have hu₂ : HasDerivAt (fun s ↦ (U s).2)
      (fderiv ℝ (localHamiltonianVectorField L e) p (U t)).2 t := hu.snd
  have hv₁ : HasDerivAt (fun s ↦ (V s).1)
      (fderiv ℝ (localHamiltonianVectorField L e) p (V t)).1 t := hv.fst
  have hv₂ : HasDerivAt (fun s ↦ (V s).2)
      (fderiv ℝ (localHamiltonianVectorField L e) p (V t)).2 t := hv.snd
  apply ((hv₂.clm_apply hu₁).sub (hu₂.clm_apply hv₁)).congr_deriv
  linarith

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Actual momenta of one intrinsic solution are related by the true cotangent chart lift. -/
theorem chartMomentumFamily_cotangentLift (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {w : W} {t : ℝ} (hc : F.IsEulerLagrangeAt (Γ w) t)
    (old new : M) (ho : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hn : Γ w t ∈ (extChartAt 𝓘(ℝ, E) new).source) :
    cotangentLift (chartTransition old new) (chartTransition new old)
      (F.chartMomentumFamily new Γ (w, t)) = F.chartMomentumFamily old Γ (w, t) := by
  obtain ⟨J, hJ, ht, hm, hy, hp, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc new hn
  have hdom : (extChartAt 𝓘(ℝ, E) new ∘ Γ w) t ∈ chartTransitionDomain old new := by
    refine ⟨(extChartAt 𝓘(ℝ, E) new).map_source hn, ?_⟩
    change (extChartAt 𝓘(ℝ, E) new).symm (extChartAt 𝓘(ℝ, E) new (Γ w t)) ∈
      (extChartAt 𝓘(ℝ, E) old).source
    rwa [(extChartAt 𝓘(ℝ, E) new).left_inv hn]
  have hgerm : (extChartAt 𝓘(ℝ, E) old ∘ Γ w) =ᶠ[𝓝 t]
      chartTransition old new ∘ (extChartAt 𝓘(ℝ, E) new ∘ Γ w) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    simp only [chartTransition, Function.comp_apply,
      (extChartAt 𝓘(ℝ, E) new).left_inv (hm hs)]
  have hlift := tangentLift_curve_eq
    (((contDiffOn_chartTransition old new).contDiffAt
      ((isOpen_chartTransitionDomain old new).mem_nhds hdom)).differentiableAt (by simp))
    ((hy.contDiffAt (hJ.mem_nhds ht)).differentiableAt (by simp))
  rw [← hgerm.eq_of_nhds, ← hgerm.deriv_eq] at hlift
  have hcov := hF.chartLegendre_cotangentLift old new hdom (hp t ht).2
  change cotangentLift (chartTransition old new) (chartTransition new old)
      (parametricLegendre (F.chartEnergy new)
        ((extChartAt 𝓘(ℝ, E) new ∘ Γ w) t,
          deriv (extChartAt 𝓘(ℝ, E) new ∘ Γ w) t)) =
    parametricLegendre (F.chartEnergy old) (tangentLift (chartTransition old new)
      ((extChartAt 𝓘(ℝ, E) new ∘ Γ w) t,
        deriv (extChartAt 𝓘(ℝ, E) new ∘ Γ w) t)) at hcov
  rw [hlift] at hcov
  exact hcov

private theorem chartFamily_domain (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (old : M) :
    let D := (B ×ˢ univ) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹'
      (extChartAt 𝓘(ℝ, E) old).source
    IsOpen D ∧ ContDiffOn ℝ 2 (F.chartMomentumFamily old Γ) D := by
  have hb : ContinuousOn (fun q : W × ℝ ↦ Γ q.1 q.2) (B ×ˢ univ) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn hG.continuousOn
  refine ⟨hb.isOpen_inter_preimage (hB.prod isOpen_univ) (isOpen_extChartAt_source old), ?_⟩
  exact hF.contDiffOn_chartMomentumFamily old
    (fun q hq ↦ hEL q.1 hq.1.1 q.2 (mem_univ _)) (hG.mono inter_subset_left)
    (fun _ hq ↦ hq.2)

/-- The canonical pairing of actual parameter momentum derivatives is independent of
which genuine chart is used at that same point and time. -/
theorem chartMomentumFamily_parameter_pairing_change (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (t : ℝ) (old new : M)
    (ho : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hn : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) new).source) (u v : W) :
    canonicalPhasePairing (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ v) =
    canonicalPhasePairing (fderiv ℝ (fun w ↦ F.chartMomentumFamily new Γ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily new Γ (w, t)) w₀ v) := by
  obtain ⟨hDo, _⟩ := hF.chartFamily_domain hB hEL hG old
  obtain ⟨hDn, hΨ⟩ := hF.chartFamily_domain hB hEL hG new
  have hqc : ContinuousAt (fun w : W ↦ (w, t)) w₀ :=
    continuousAt_id.prodMk continuousAt_const
  have hnear := hqc.preimage_mem_nhds ((hDo.inter hDn).mem_nhds
    ⟨⟨⟨hw, mem_univ t⟩, ho⟩, ⟨⟨hw, mem_univ t⟩, hn⟩⟩)
  have heq : (fun w ↦ F.chartMomentumFamily old Γ (w, t)) =ᶠ[𝓝 w₀]
      cotangentLift (chartTransition old new) (chartTransition new old) ∘
        (fun w ↦ F.chartMomentumFamily new Γ (w, t)) := by
    filter_upwards [hnear] with w hw'
    exact (hF.chartMomentumFamily_cotangentLift
      (hEL w hw'.1.1.1 t (mem_univ _)) old new hw'.1.2 hw'.2.2).symm
  have hdiff : DifferentiableAt ℝ (fun w ↦ F.chartMomentumFamily new Γ (w, t)) w₀ :=
    ((hΨ.contDiffAt (hDn.mem_nhds ⟨⟨hw, mem_univ t⟩, hn⟩)).differentiableAt
      (by norm_num)).comp w₀ (differentiableAt_id.prodMk (differentiableAt_const t))
  have hdom : (F.chartMomentumFamily new Γ (w₀, t)).1 ∈
      chartTransitionDomain old new := by
    refine ⟨(extChartAt 𝓘(ℝ, E) new).map_source hn, ?_⟩
    change (extChartAt 𝓘(ℝ, E) new).symm (extChartAt 𝓘(ℝ, E) new (Γ w₀ t)) ∈
      (extChartAt 𝓘(ℝ, E) old).source
    rwa [(extChartAt 𝓘(ℝ, E) new).left_inv hn]
  rw [heq.fderiv_eq]
  exact rechartedPhase_fderiv_pairing old new hdiff hdom u v

private theorem chart_pairing_hasDerivAt (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) (t : ℝ)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) (u v : W) :
    HasDerivAt (fun s ↦ canonicalPhasePairing
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, s)) w₀ u)
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, s)) w₀ v)) 0 t := by
  let D₀ := (B ×ˢ univ) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹'
    (extChartAt 𝓘(ℝ, E) old).source
  let Ψ := F.chartMomentumFamily old Γ
  obtain ⟨hD₀, hΨ₀⟩ := hF.chartFamily_domain hB hEL hG old
  have hq₀ : (w₀, t) ∈ D₀ := ⟨⟨hw, mem_univ t⟩, hx⟩
  obtain ⟨J, _, ht, _, _, hp, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt (hEL w₀ hw t (mem_univ _)) old hx
  obtain ⟨e, he, _, hpe, hes, hi, _, hX, _⟩ :=
    hF.exists_smooth_chartHamiltonian old (hp t ht)
  have hpt : Ψ (w₀, t) ∈ e.target := hpe
  let D := D₀ ∩ Ψ ⁻¹' e.target
  have hD : IsOpen D := hΨ₀.continuousOn.isOpen_inter_preimage hD₀ e.open_target
  have hΨ : ContDiffOn ℝ 2 Ψ D := hΨ₀.mono inter_subset_left
  have hq : (w₀, t) ∈ D := ⟨hq₀, hpt⟩
  have hODE : ∀ q ∈ D, HasDerivAt (fun s ↦ Ψ (q.1, s))
      (localHamiltonianVectorField (F.chartEnergy old) e (Ψ q)) q.2 := by
    intro q hq
    exact hF.hasDerivAt_chartMomentum old (hEL q.1 hq.1.1.1 q.2 (mem_univ _))
      hq.1.2 he hes hq.2
  have hvar (ξ : W) := hasDerivAt_parameterVariation_of_nonautonomousODE
    (X := fun _ ↦ localHamiltonianVectorField (F.chartEnergy old) e) hD hΨ hODE hq
    ((hX.contDiffAt (e.open_target.mem_nhds hpt)).differentiableAt (by simp)) ξ
  exact hamiltonian_pairing_derivative_zero he ((hF.contDiffOn_chartEnergy old).mono hes)
    hi hpt (hvar u) (hvar v)

/-- Actual parameter momentum pairing is conserved between any two times, with independent
legal charts at the two endpoints. No common chart or common inverse branch is required. -/
theorem chartMomentumFamily_parameter_pairing_eq (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old new : M) (s t : ℝ)
    (hs : Γ w₀ s ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (ht : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) new).source) (u v : W) :
    canonicalPhasePairing (fderiv ℝ (fun w ↦ F.chartMomentumFamily new Γ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily new Γ (w, t)) w₀ v) =
    canonicalPhasePairing (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, s)) w₀ u)
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, s)) w₀ v) := by
  let P : M → ℝ → ℝ := fun a r ↦ canonicalPhasePairing
    (fderiv ℝ (fun w ↦ F.chartMomentumFamily a Γ (w, r)) w₀ u)
    (fderiv ℝ (fun w ↦ F.chartMomentumFamily a Γ (w, r)) w₀ v)
  let K : ℝ → ℝ := fun r ↦ P (Γ w₀ r) r
  have hd (r : ℝ) : HasDerivAt K 0 r := by
    have hc := (hF.contMDiffAt_of_isEulerLagrangeAt (hEL w₀ hw r (mem_univ _))).continuousAt
    have hnear := hc.preimage_mem_nhds ((isOpen_extChartAt_source (Γ w₀ r)).mem_nhds
      (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ r)))
    apply (hF.chart_pairing_hasDerivAt hB hEL hG hw (Γ w₀ r) r
      (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ r)) u v).congr_of_eventuallyEq
    filter_upwards [hnear] with r' hr'
    exact hF.chartMomentumFamily_parameter_pairing_change hB hEL hG hw r'
      (Γ w₀ r') (Γ w₀ r) (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ r')) hr' u v
  have hconst : K t = K s :=
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun r _ ↦ (hd r).differentiableAt.differentiableWithinAt)
      (fun r _ ↦ (hd r).deriv) (mem_univ t) (mem_univ s)
  calc
    P new t = K t := hF.chartMomentumFamily_parameter_pairing_change hB hEL hG hw t
      new (Γ w₀ t) ht (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ t)) u v
    _ = K s := hconst
    _ = P old s := hF.chartMomentumFamily_parameter_pairing_change hB hEL hG hw s
      (Γ w₀ s) old (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ s)) hs u v

/-- Prescribing genuine initial tangent vectors identifies the conserved pairing with the
actual initial Legendre seed differential, with no separate momentum-compatibility premise. -/
theorem chartMomentumFamily_parameter_pairing_eq_initial (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (initial : M) (t₀ : ℝ) {seed : W → E × E}
    (hseed : MapsTo seed B (chartEnergyDomain initial))
    (hinit : ∀ w ∈ B, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (seed w))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) (t : ℝ)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) (u v : W) :
    canonicalPhasePairing (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ u)
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ v) =
    canonicalPhasePairing
      (fderiv ℝ (parametricLegendre (F.chartEnergy initial) ∘ seed) w₀ u)
      (fderiv ℝ (parametricLegendre (F.chartEnergy initial) ∘ seed) w₀ v) := by
  have hb : Γ w₀ t₀ = (extChartAt 𝓘(ℝ, E) initial).symm (seed w₀).1 := by
    have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit w₀ hw)
    rw [show seed w₀ = ((seed w₀).1, (seed w₀).2) from rfl,
      tangentChart_symm_eq initial (hseed hw).1] at h
    exact h
  have hi : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target (hseed hw).1
  have heq : (fun w ↦ F.chartMomentumFamily initial Γ (w, t₀)) =ᶠ[𝓝 w₀]
      parametricLegendre (F.chartEnergy initial) ∘ seed := by
    filter_upwards [hB.mem_nhds hw] with w hw'
    exact hF.chartMomentum_of_tangent_eq (hEL w hw' t₀ (mem_univ _)) initial
      (hseed hw') (hinit w hw')
  have h := hF.chartMomentumFamily_parameter_pairing_eq hB hEL hG hw initial old t₀ t
    hi hx u v
  rwa [heq.fderiv_eq] at h

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
