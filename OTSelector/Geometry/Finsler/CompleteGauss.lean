import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.CompletePairing
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Symplectic.CotangentChartPairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompleteGauss.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompleteGauss`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CompleteGauss

* **Conditions:** A jointly C2 intrinsic Euler–Lagrange family with one common original energy across its parameters and arbitrary legal endpoint charts.
* **Objects:** Global Gauss conservation of momentum evaluated on actual position variation.
* **Proof detail:** Differentiate that scalar using common energy and the actual variational equation, prove its chart invariance by cotangent evaluation and propagate its zero derivative along real time.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.

Source relation (derived): The Gauss identity is derived from genuine dynamics and constant energy, not quoted as an arbitrary normal-family premise.
-/

/-!
# Gauss identity along complete intrinsic Finsler families

For the same actual family, common original energy makes the momentum evaluated on
its position variation stationary. Genuine cotangent changes preserve this scalar,
so the identity holds between arbitrary times and arbitrary legal endpoint charts.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem cotangent_evaluation (old new : M)
    {p : E × (E →L[ℝ] ℝ)} (hp : p.1 ∈ chartTransitionDomain old new)
    (u : E × (E →L[ℝ] ℝ)) :
    (cotangentLift (chartTransition old new) (chartTransition new old) p).2
      (fderiv ℝ (cotangentLift (chartTransition old new)
        (chartTransition new old)) p u).1 = p.2 u.1 := by
  let T := cotangentLift (chartTransition (E := E) old new) (chartTransition new old)
  have hφ := ((contDiffOn_chartTransition old new).contDiffAt
    ((isOpen_chartTransitionDomain old new).mem_nhds hp)).differentiableAt (by simp)
  have hψ := ((contDiffOn_chartTransition new old).contDiffAt
    ((isOpen_chartTransitionDomain new old).mem_nhds
      (mapsTo_chartTransition old new hp))).differentiableAt (by simp)
  have hT : DifferentiableAt ℝ T p := ((contDiffOn_chartCotangentLift old new).contDiffAt
    (((isOpen_chartTransitionDomain old new).prod isOpen_univ).mem_nhds
      ⟨hp, mem_univ _⟩)).differentiableAt (by simp)
  have hfst : (fderiv ℝ T p u).1 = fderiv ℝ (chartTransition old new) p.1 u.1 := by
    exact congrArg (fun D : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ D u)
      (hT.hasFDerivAt.fst.unique (hφ.hasFDerivAt.comp p
        (ContinuousLinearMap.fst ℝ E (E →L[ℝ] ℝ)).hasFDerivAt))
  have hleft : chartTransition new old ∘ chartTransition old new =ᶠ[𝓝 p.1] id := by
    filter_upwards [(isOpen_chartTransitionDomain old new).mem_nhds hp] with x hx
    exact chartTransition_reverse old new hx
  have hinv := (hψ.hasFDerivAt.comp p.1 hφ.hasFDerivAt).fderiv.symm.trans
    (hleft.fderiv_eq.trans fderiv_id)
  change p.2 (fderiv ℝ (chartTransition new old) (chartTransition old new p.1)
    (fderiv ℝ T p u).1) = p.2 u.1
  rw [hfst]
  exact congrArg p.2 (congrArg (fun D : E →L[ℝ] E ↦ D u.1) hinv)

private theorem fderiv_first {Ψ : W → E × (E →L[ℝ] ℝ)} {w : W}
    (hΨ : DifferentiableAt ℝ Ψ w) (ξ : W) :
    (fderiv ℝ Ψ w ξ).1 = fderiv ℝ (fun b ↦ (Ψ b).1) w ξ :=
  (congrArg (fun D : W →L[ℝ] E ↦ D ξ) hΨ.hasFDerivAt.fst.fderiv).symm

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

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

private theorem chartMomentum_differentiable (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) (t : ℝ)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    DifferentiableAt ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ := by
  obtain ⟨hD, hΨ⟩ := hF.chartFamily_domain hB hEL hG old
  exact ((hΨ.contDiffAt (hD.mem_nhds ⟨⟨hw, mem_univ t⟩, hx⟩)).differentiableAt
    (by norm_num)).comp w₀ (differentiableAt_id.prodMk (differentiableAt_const t))

/-- Actual momentum evaluated on the true parameter position derivative is independent
of the legal chart. The genuine cotangent lift supplies the transformation identity. -/
theorem chartMomentumFamily_gauss_change (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {w₀ : W} (hw : w₀ ∈ B) (t : ℝ) (old new : M)
    (ho : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hn : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) new).source) (ξ : W) :
    (F.chartMomentumFamily old Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) =
    (F.chartMomentumFamily new Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) new (Γ w t)) w₀ ξ) := by
  obtain ⟨hDo, _⟩ := hF.chartFamily_domain hB hEL hG old
  obtain ⟨hDn, _⟩ := hF.chartFamily_domain hB hEL hG new
  have hnear := (continuousAt_id.prodMk (continuousAt_const (y := t))).preimage_mem_nhds
    ((hDo.inter hDn).mem_nhds
      ⟨⟨⟨hw, mem_univ t⟩, ho⟩, ⟨⟨hw, mem_univ t⟩, hn⟩⟩)
  have heq : (fun w ↦ F.chartMomentumFamily old Γ (w, t)) =ᶠ[𝓝 w₀]
      cotangentLift (chartTransition old new) (chartTransition new old) ∘
        (fun w ↦ F.chartMomentumFamily new Γ (w, t)) := by
    filter_upwards [hnear] with w hw'
    exact (hF.chartMomentumFamily_cotangentLift
      (hEL w hw'.1.1.1 t (mem_univ _)) old new hw'.1.2 hw'.2.2).symm
  have hdiff := hF.chartMomentum_differentiable hB hEL hG hw new t hn
  have hdom : (F.chartMomentumFamily new Γ (w₀, t)).1 ∈
      chartTransitionDomain old new := by
    refine ⟨(extChartAt 𝓘(ℝ, E) new).map_source hn, ?_⟩
    change (extChartAt 𝓘(ℝ, E) new).symm (extChartAt 𝓘(ℝ, E) new (Γ w₀ t)) ∈
      (extChartAt 𝓘(ℝ, E) old).source
    rwa [(extChartAt 𝓘(ℝ, E) new).left_inv hn]
  have hT := ((contDiffOn_chartCotangentLift old new).contDiffAt
    (((isOpen_chartTransitionDomain old new).prod isOpen_univ).mem_nhds
      ⟨hdom, mem_univ _⟩)).differentiableAt (by simp)
  change (F.chartMomentumFamily old Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ (F.chartMomentumFamily old Γ (w, t)).1) w₀ ξ) =
    (F.chartMomentumFamily new Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ (F.chartMomentumFamily new Γ (w, t)).1) w₀ ξ)
  rw [← fderiv_first (hF.chartMomentum_differentiable hB hEL hG hw old t ho) ξ,
    ← fderiv_first hdiff ξ, heq.eq_of_nhds, heq.fderiv_eq,
    (hT.hasFDerivAt.comp w₀ hdiff.hasFDerivAt).fderiv]
  exact cotangent_evaluation old new hdom _

private theorem chart_gauss_hasDerivAt (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = C)
    {w₀ : W} (hw : w₀ ∈ B) (old : M) (t : ℝ)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) (ξ : W) :
    HasDerivAt (fun s ↦ (F.chartMomentumFamily old Γ (w₀, s)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w s)) w₀ ξ)) 0 t := by
  let D₀ := (B ×ˢ univ) ∩ (fun q : W × ℝ ↦ Γ q.1 q.2) ⁻¹'
    (extChartAt 𝓘(ℝ, E) old).source
  let Ψ := F.chartMomentumFamily old Γ
  let L := F.chartEnergy old
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
      (localHamiltonianVectorField L e (Ψ q)) q.2 := by
    intro q hq
    exact hF.hasDerivAt_chartMomentum old (hEL q.1 hq.1.1.1 q.2 (mem_univ _))
      hq.1.2 he hes hq.2
  have hvar := hasDerivAt_parameterVariation_of_nonautonomousODE
    (X := fun _ ↦ localHamiltonianVectorField L e) hD hΨ hODE hq
    ((hX.contDiffAt (e.open_target.mem_nhds hpt)).differentiableAt (by simp)) ξ
  have hL : ContDiffOn ℝ ∞ L e.source := (hF.contDiffOn_chartEnergy old).mono hes
  have hdG := (hi.contDiffAt (e.open_target.mem_nhds hpt)).differentiableAt (by simp)
  have hdL := (hL.contDiffAt
    (e.open_source.mem_nhds (e.map_target hpt))).differentiableAt (by simp)
  have heq (q : W × ℝ) (hq : q ∈ D) : L (e.symm (Ψ q)) = C := by
    rw [hamiltonian_inverse_eq_position_deriv he hq.2 (hODE q hq)]
    have hr := (hF.chartTangent_of_isEulerLagrangeAt
      (hEL q.1 hq.1.1.1 q.2 (mem_univ _)) old hq.1.2).1
    change F.energy ((extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ q.1) q.2,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ q.1) q.2)) = C
    rw [← hr, (extChartAt _ _).left_inv]
    · exact henergy q.1 hq.1.1.1 q.2
    · simpa only [FiberBundle.chartedSpace_chartAt, mfld_simps] using hq.1.2
  have hnear := (continuousAt_id.prodMk (continuousAt_const (y := t))).preimage_mem_nhds
    (hD.mem_nhds hq)
  have hgerm : (fun w ↦ L (e.symm (Ψ (w, t)))) =ᶠ[𝓝 w₀] fun _ ↦ C := by
    filter_upwards [hnear] with w hw'
    exact heq (w, t) hw'
  have hdΨ := hF.chartMomentum_differentiable hB hEL hG hw old t hx
  have hd := hdL.hasFDerivAt.comp w₀ (hdG.hasFDerivAt.comp w₀ hdΨ.hasFDerivAt)
  have hc : HasFDerivAt (fun w ↦ L (e.symm (Ψ (w, t)))) 0 w₀ :=
    (hasFDerivAt_const (𝕜 := ℝ) C w₀).congr_of_eventuallyEq hgerm
  let Z := fun s ↦ fderiv ℝ (fun w ↦ Ψ (w, s)) w₀ ξ
  have henergyD : fderiv ℝ L (e.symm (Ψ (w₀, t)))
      (fderiv ℝ e.symm (Ψ (w₀, t)) (Z t)) = 0 := by
    simpa only [ContinuousLinearMap.comp_apply, _root_.zero_apply, Z, Ψ] using
      congrArg (fun A : W →L[ℝ] ℝ ↦ A ξ) (hd.unique hc)
  have hP : HasDerivAt (fun s ↦ (Ψ (w₀, s)).2)
      (baseEnergyDifferential L (e.symm (Ψ (w₀, t)))) t := (hODE (w₀, t) hq).snd
  have hJ : HasDerivAt (fun s ↦ (Z s).1)
      (fderiv ℝ (localHamiltonianVectorField L e) (Ψ (w₀, t)) (Z t)).1 t := hvar.fst
  rw [localHamiltonianVectorField_fderiv_fst hL hi hpt] at hJ
  have hfst : (fderiv ℝ e.symm (Ψ (w₀, t)) (Z t)).1 = (Z t).1 :=
    congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] E ↦ A (Z t))
      (parametricLegendre_inverse_derivative_fst he hpt hdG.hasFDerivAt)
  rw [← Prod.eta (fderiv ℝ e.symm (Ψ (w₀, t)) (Z t)), fderiv_energy_split hdL,
    hfst, (parametricLegendre_inverse_components he hpt).2] at henergyD
  apply ((hP.clm_apply hJ).congr_deriv henergyD).congr_of_eventuallyEq
  have htnear := (continuousAt_const.prodMk continuousAt_id).preimage_mem_nhds
    (hD.mem_nhds hq)
  filter_upwards [htnear] with s hs
  exact congrArg (Ψ (w₀, s)).2
    (fderiv_first (hF.chartMomentum_differentiable hB hEL hG hw old s hs.1.2) ξ).symm

/-- Common original energy makes the actual momentum-position pairing constant between
arbitrary real times, allowing independent genuine charts at the two endpoints. -/
theorem chartMomentumFamily_gauss_eq (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = C)
    {w₀ : W} (hw : w₀ ∈ B) (old new : M) (s t : ℝ)
    (hs : Γ w₀ s ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (ht : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) new).source) (ξ : W) :
    (F.chartMomentumFamily new Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) new (Γ w t)) w₀ ξ) =
    (F.chartMomentumFamily old Γ (w₀, s)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w s)) w₀ ξ) := by
  let P : M → ℝ → ℝ := fun a r ↦ (F.chartMomentumFamily a Γ (w₀, r)).2
    (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) a (Γ w r)) w₀ ξ)
  let K : ℝ → ℝ := fun r ↦ P (Γ w₀ r) r
  have hd (r : ℝ) : HasDerivAt K 0 r := by
    have hc := (hF.contMDiffAt_of_isEulerLagrangeAt (hEL w₀ hw r (mem_univ _))).continuousAt
    have hnear := hc.preimage_mem_nhds ((isOpen_extChartAt_source (Γ w₀ r)).mem_nhds
      (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ r)))
    apply (hF.chart_gauss_hasDerivAt hB hEL hG henergy hw (Γ w₀ r) r
      (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ r)) ξ).congr_of_eventuallyEq
    filter_upwards [hnear] with r' hr'
    exact hF.chartMomentumFamily_gauss_change hB hEL hG hw r'
      (Γ w₀ r') (Γ w₀ r) (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ r')) hr' ξ
  have hconst : K t = K s :=
    isOpen_univ.is_const_of_deriv_eq_zero isPreconnected_univ
      (fun r _ ↦ (hd r).differentiableAt.differentiableWithinAt)
      (fun r _ ↦ (hd r).deriv) (mem_univ t) (mem_univ s)
  calc
    P new t = K t := hF.chartMomentumFamily_gauss_change hB hEL hG hw t
      new (Γ w₀ t) ht (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ t)) ξ
    _ = K s := hconst
    _ = P old s := hF.chartMomentumFamily_gauss_change hB hEL hG hw s
      (Γ w₀ s) old (mem_extChartAt_source (I := 𝓘(ℝ, E)) (Γ w₀ s)) hs ξ

/-- Genuine initial tangents identify the conserved Gauss scalar with the original
initial energy momentum acting on the actual seed position differential. -/
theorem chartMomentumFamily_gauss_eq_initial (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = C)
    (initial : M) (t₀ : ℝ) {seed : W → E × E}
    (hseed : MapsTo seed B (chartEnergyDomain initial))
    (hinit : ∀ w ∈ B, tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t₀, (1 : ℝ)⟩ =
      (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
        (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (seed w))
    {w₀ : W} (hw : w₀ ∈ B) (old : M) (t : ℝ)
    (hx : Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source) (ξ : W) :
    (F.chartMomentumFamily old Γ (w₀, t)).2
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) =
    fiberLegendre (F.chartEnergy initial) (seed w₀)
      (fderiv ℝ (fun w ↦ (seed w).1) w₀ ξ) := by
  have hb : Γ w₀ t₀ = (extChartAt 𝓘(ℝ, E) initial).symm (seed w₀).1 := by
    have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit w₀ hw)
    rw [show seed w₀ = ((seed w₀).1, (seed w₀).2) from rfl,
      tangentChart_symm_eq initial (hseed hw).1] at h
    exact h
  have hi : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, E) initial).source := by
    rw [hb]
    exact (extChartAt 𝓘(ℝ, E) initial).map_target (hseed hw).1
  have heq : (fun w ↦ extChartAt 𝓘(ℝ, E) initial (Γ w t₀)) =ᶠ[𝓝 w₀]
      fun w ↦ (seed w).1 := by
    filter_upwards [hB.mem_nhds hw] with w hw'
    exact congrArg Prod.fst (hF.chartPhase_of_tangent_eq
      (hEL w hw' t₀ (mem_univ _)) initial (hseed hw') (hinit w hw'))
  have hp := congrArg Prod.snd (hF.chartMomentum_of_tangent_eq
    (hEL w₀ hw t₀ (mem_univ _)) initial (hseed hw) (hinit w₀ hw))
  have h := hF.chartMomentumFamily_gauss_eq hB hEL hG henergy hw initial old t₀ t hi hx ξ
  change _ = fiberLegendre (F.chartEnergy initial) (seed w₀) at hp
  rw [heq.fderiv_eq] at h
  exact h.trans (congrArg (fun p : E →L[ℝ] ℝ ↦
    p (fderiv ℝ (fun w ↦ (seed w).1) w₀ ξ)) hp)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
