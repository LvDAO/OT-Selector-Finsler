import OTSelector.Analysis.Calculus.LocalSmoothExtension
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.JointC2
import OTSelector.Analysis.ODE.Flow.LocalC2
import OTSelector.Analysis.ODE.Flow.LocalVariational
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeVectorField
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
# Geometry.Finsler.CompleteTangentSmooth

* **Conditions:** A complete actual intrinsic family with smooth original initial tangent data; generic finite-order helpers require the stated regular vector field and flow domain.
* **Objects:** Joint smoothness of the same complete tangent/position family for all real times.
* **Proof detail:** Construct each finite-order local ODE restart, identify it with the original family by uniqueness, propagate along connected time and pass through all finite orders.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompleteTangentSmooth.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompleteTangentSmooth`; the selected original proof blocks follow. -/
section

/-!
# Smoothness of the same complete Finsler tangent family

The existing finite-order variational-flow theorem supplies every natural regularity
order. Local restarts identify those flows with the given complete intrinsic family;
open-and-closed propagation then covers every time. Applying this at each finite
order yields joint smoothness of that same family from its actual smooth initial
state, without selecting a second family or assuming higher flow regularity.
-/

/-!
## Finite-order smooth local flows and restarts

An actual local flow of a smooth open-domain field has arbitrarily high finite
joint regularity after restriction. Time-shifted restarts retain that regularity.
-/

open Set Filter Metric Function
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth open-domain vector field admits an actual local flow of any finite
order at least two, with its range confined to the original domain. -/
private theorem exists_cnFlow_in_open [FiniteDimensional ℝ E] (n : ℕ) (hn : 2 ≤ n)
    {U : Set E} {X : E → E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {p : E} (hp : p ∈ U) (t₀ : ℝ) :
    ∃ (r : ℝ≥0) (T : ℝ), 0 < r ∧ 0 < T ∧ ∃ Φ : E × ℝ → E,
      IsLocalFlow (fun _ ↦ X) t₀ p r (t₀ - T) (t₀ + T) Φ ∧
      MapsTo Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) U ∧
      ContDiffOn ℝ (n : ℕ∞) Φ (closedBall p r ×ˢ Icc (t₀ - T) (t₀ + T)) := by
  obtain ⟨r, T, hr, hT, Φ, hΦ, _, _, _, _, _⟩ :=
    exists_c2Flow_in_open hU hX hp t₀
  obtain ⟨V, Y, hV, hpV, hVU, hY, _, _, hYX⟩ :=
    exists_contDiff_compactlySupported_extension hU hp hX
  obtain ⟨r₁, T₁, hr₁, hr₁le, hT₁, hT₁le, hstay⟩ :=
    hΦ.exists_shrink_mapsTo hr hT hV hpV
  have hspace₁ : closedBall p (r₁ : ℝ) ⊆ closedBall p (r : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hr₁le)
  have htime₁ : Icc (t₀ - T₁) (t₀ + T₁) ⊆ Icc (t₀ - T) (t₀ + T) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hΦY : IsLocalFlow (fun _ ↦ Y) t₀ p r₁ (t₀ - T₁) (t₀ + T₁) Φ := {
    minTime_le_initial := by linarith
    initial_le_maxTime := by linarith
    apply_initial := fun x hx ↦ hΦ.apply_initial x (hspace₁ hx)
    hasDerivWithinAt := fun x hx t ht ↦ by
      rw [hYX (hstay ⟨hx, ht⟩)]
      exact (hΦ.hasDerivWithinAt x (hspace₁ hx) t (htime₁ ht)).mono htime₁
    continuousOn := hΦ.continuousOn.mono (prod_mono hspace₁ htime₁)
    exists_lipschitz := by
      obtain ⟨K, hK⟩ := hΦ.exists_lipschitz
      exact ⟨K, fun t ht ↦ (hK t (htime₁ ht)).mono hspace₁⟩ }
  have hf : ContDiffOn ℝ (n : ℕ∞) (uncurry (fun (_ : ℝ) ↦ Y)) univ :=
    ((hY.of_le (by simp : (n : ℕ∞ω) ≤ ∞)).comp contDiff_snd).contDiffOn
  obtain ⟨D, hD, hpD, hCn⟩ := exists_contDiffOn_flow_Cnat hΦY (by omega : 1 ≤ n) hf
    (by constructor <;> linarith) (show (0 : ℝ) < r₁ from hr₁)
  obtain ⟨r₂, T₂, hr₂, hr₂le, hT₂, hT₂le, hbox⟩ :=
    exists_pos_closed_flow_box_subset (hD.mem_nhds hpD) hr₁ hT₁
  have hspace₂ : closedBall p (r₂ : ℝ) ⊆ closedBall p (r₁ : ℝ) :=
    closedBall_subset_closedBall (by exact_mod_cast hr₂le)
  have htime₂ : Icc (t₀ - T₂) (t₀ + T₂) ⊆ Icc (t₀ - T₁) (t₀ + T₁) := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hs := hspace₂.trans hspace₁
  have ht := htime₂.trans htime₁
  refine ⟨r₂, T₂, hr₂, hT₂, Φ, ?_,
    fun q hq ↦ hVU (hstay ⟨hspace₂ hq.1, htime₂ hq.2⟩), hCn.mono hbox⟩
  exact {
    minTime_le_initial := by linarith
    initial_le_maxTime := by linarith
    apply_initial := fun x hx ↦ hΦ.apply_initial x (hs hx)
    hasDerivWithinAt := fun x hx t h ↦
      (hΦ.hasDerivWithinAt x (hs hx) t (ht h)).mono ht
    continuousOn := hΦ.continuousOn.mono (prod_mono hs ht)
    exists_lipschitz := by
      obtain ⟨K, hK⟩ := hΦ.exists_lipschitz
      exact ⟨K, fun t h ↦ (hK t (ht h)).mono hs⟩ }

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A time-shifted restart of the same actual local flow accepts a finite-order smooth seed.
The common parameter neighborhood and its genuine initial derivative are constructed. -/
private theorem IsLocalFlow.exists_cnRestart (n : ℕ)
    {X : E → E} {U : Set E} {p : E} {r : ℝ≥0} {τ T : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow (fun _ ↦ X) τ p r (τ - T) (τ + T) Φ)
    (hT : 0 < T)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)) U)
    (hCn : ContDiffOn ℝ (n : ℕ∞) Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)))
    {seed : W → E} {B : Set W} (hB : IsOpen B) (hseed : ContDiffOn ℝ (n : ℕ∞) seed B)
    {w₀ : W} (hw₀ : w₀ ∈ B) (hp : seed w₀ ∈ ball p r) (s₀ : ℝ) :
    let Ψ : W × ℝ → E := fun q ↦ Φ (seed q.1, τ + (q.2 - s₀))
    ∃ B' : Set W, IsOpen B' ∧ w₀ ∈ B' ∧ B' ⊆ B ∧
      MapsTo seed B' (ball p r) ∧
      ContDiffOn ℝ (n : ℕ∞) Ψ (B' ×ˢ Ioo (s₀ - T) (s₀ + T)) ∧
      MapsTo Ψ (B' ×ˢ Ioo (s₀ - T) (s₀ + T)) U ∧
      s₀ ∈ Ioo (s₀ - T) (s₀ + T) ∧
      (∀ w ∈ B', Ψ (w, s₀) = seed w) ∧
      (∀ w ∈ B', ∀ t ∈ Ioo (s₀ - T) (s₀ + T),
        HasDerivAt (fun s ↦ Ψ (w, s)) (X (Ψ (w, t))) t) ∧
      fderiv ℝ (fun w ↦ Ψ (w, s₀)) w₀ = fderiv ℝ seed w₀ := by
  let B' := B ∩ seed ⁻¹' ball p (r : ℝ)
  have hB' : IsOpen B' := hseed.continuousOn.isOpen_inter_preimage hB isOpen_ball
  have hw : w₀ ∈ B' := ⟨hw₀, hp⟩
  have hsub : B' ⊆ B := inter_subset_left
  have hs : MapsTo seed B' (ball p r) := fun w hw ↦ hw.2
  have htime (t : ℝ) (ht : t ∈ Ioo (s₀ - T) (s₀ + T)) :
      τ + (t - s₀) ∈ Ioo (τ - T) (τ + T) := by
    constructor <;> linarith [ht.1, ht.2]
  have hinit (w : W) (hw : w ∈ B') : Φ (seed w, τ + (s₀ - s₀)) = seed w := by
    simpa using hΦ.apply_initial (seed w) (ball_subset_closedBall (hs hw))
  refine ⟨B', hB', hw, hsub, hs, ?_, ?_, ⟨by linarith, by linarith⟩, hinit, ?_, ?_⟩
  · apply hCn.comp
      (((hseed.mono hsub).comp contDiffOn_fst (fun _ hz ↦ hz.1)).prodMk
        (contDiffOn_const.add (contDiffOn_snd.sub contDiffOn_const)))
    intro q hq
    exact ⟨ball_subset_closedBall (hs hq.1), Ioo_subset_Icc_self (htime q.2 hq.2)⟩
  · intro q hq
    exact hmap ⟨ball_subset_closedBall (hs hq.1), Ioo_subset_Icc_self (htime q.2 hq.2)⟩
  · intro w hw t ht
    have hd := (hΦ.hasDerivWithinAt (seed w) (ball_subset_closedBall (hs hw))
      (τ + (t - s₀)) (Ioo_subset_Icc_self (htime t ht))).hasDerivAt
        (Icc_mem_nhds (htime t ht).1 (htime t ht).2)
    have hshift := ((hasDerivAt_id t).sub_const s₀).const_add τ
    simpa only [Function.comp_def, one_smul, id_eq] using hd.scomp t hshift
  · have he : (fun w ↦ Φ (seed w, τ + (s₀ - s₀))) =ᶠ[𝓝 w₀] seed :=
      Filter.eventually_of_mem (hB'.mem_nhds hw) hinit
    exact he.fderiv_eq

end OTSelector.Geometry.LocalFlow

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

private abbrev actualTangent (c : ℝ → M) (t : ℝ) : TangentBundle 𝓘(ℝ, E) M :=
  tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩

private abbrev phaseChart (old : M) :=
  extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] in
private theorem actualTangent_mem_source {c : ℝ → M} {t : ℝ} (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    actualTangent (E := E) c t ∈ (phaseChart (E := E) old).source := by
  simpa only [phaseChart, actualTangent, FiberBundle.chartedSpace_chartAt, mfld_simps] using hx

private theorem phaseChart_actualTangent (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    phaseChart (E := E) old (actualTangent (E := E) c t) =
      ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) :=
  (hF.chartTangent_of_isEulerLagrangeAt hc old hx).1

private theorem phaseField_solution (hF : F.IsSmoothStronglyConvex) (old : M)
    {y : ℝ → E × E} {J : Set ℝ} (hJ : IsOpen J) (hy : ContDiffOn ℝ 2 y J)
    (hm : MapsTo y J (chartEnergyDomain old))
    (ho : ∀ t ∈ J, HasDerivAt y (eulerLagrangeVectorField (F.chartEnergy old) (y t)) t) :
    F.IsEulerLagrangeOn ((extChartAt 𝓘(ℝ, E) old).symm ∘ fun t ↦ (y t).1) J ∧
      ∀ t ∈ J, actualTangent (E := E) ((extChartAt 𝓘(ℝ, E) old).symm ∘ fun s ↦ (y s).1) t =
        (phaseChart (E := E) old).symm (y t) := by
  have hd (t : ℝ) (ht : t ∈ J) : HasDerivAt (fun s ↦ (y s).1) (y t).2 t := by
    have h : HasDerivAt (fun s ↦ (y s).1)
        (eulerLagrangeVectorField (F.chartEnergy old) (y t)).1 t := (ho t ht).fst
    simpa only [hF.chartEulerLagrangeVectorField_fst old (hm ht)] using h
  refine ⟨F.isEulerLagrangeOn_chart_symm old hJ hy.fst ?_ ?_, ?_⟩
  · intro t ht
    rw [(hd t ht).deriv]
    exact hm ht
  · intro t ht
    exact hF.hasDerivAt_chartEulerLagrange_of_positionVelocity old hJ hm ho ht
  · intro t ht
    exact tangentMap_chart_symm_curve old (hm ht).1 (hd t ht)

private theorem identify_phaseFamily [T2Space M] (hF : F.IsSmoothStronglyConvex) (old : M)
    {Γ : W → ℝ → M} {B : Set W} {J : Set ℝ} {s : ℝ}
    (hJ : IsOpen J) (hc : IsPreconnected J) (hs : s ∈ J)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    {Ψ : W × ℝ → E × E} (hΨ : ContDiffOn ℝ 2 Ψ (B ×ˢ J))
    (hm : MapsTo Ψ (B ×ˢ J) (chartEnergyDomain old))
    (ho : ∀ w ∈ B, ∀ t ∈ J,
      HasDerivAt (fun u ↦ Ψ (w, u))
        (eulerLagrangeVectorField (F.chartEnergy old) (Ψ (w, t))) t)
    (hi : ∀ w ∈ B, actualTangent (E := E) (Γ w) s = (phaseChart (E := E) old).symm (Ψ (w, s))) :
    ∀ w ∈ B, ∀ t ∈ J, actualTangent (E := E) (Γ w) t =
      (phaseChart (E := E) old).symm (Ψ (w, t)) := by
  intro w hw
  obtain ⟨hEL, htan⟩ := hF.phaseField_solution old hJ
    (hΨ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ ht ↦ ⟨hw, ht⟩))
    (fun _ ht ↦ hm ⟨hw, ht⟩) (ho w hw)
  have he := hF.tangentCurve_eqOn_of_isEulerLagrangeOn hJ hc
    ((hΓ w hw).mono (subset_univ _)) hEL hs ((hi w hw).trans (htan s hs).symm)
  exact fun t ht ↦ (he ht).trans (htan t ht)

private theorem tangentFamily_restart_cn [T2Space M] (hF : F.IsSmoothStronglyConvex)
    (n : ℕ) (hn : 2 ≤ n)
    (old : M) {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) {w₀ : W} (hw₀ : w₀ ∈ B)
    {p : E × E} {r : ℝ≥0} {τ T s : ℝ} {Φ : (E × E) × ℝ → E × E}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ eulerLagrangeVectorField (F.chartEnergy old))
      τ p r (τ - T) (τ + T) Φ) (hT : 0 < T)
    (hm : MapsTo Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)) (chartEnergyDomain old))
    (hCn : ContDiffOn ℝ (n : ℕ∞) Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)))
    (hreg : ContMDiffAt 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞)
      (fun w ↦ actualTangent (E := E) (Γ w) s) w₀)
    (hsrc : actualTangent (E := E) (Γ w₀) s ∈ (phaseChart (E := E) old).source)
    (hp : phaseChart (E := E) old (actualTangent (E := E) (Γ w₀) s) ∈ ball p r) :
    ∃ B' : Set W, IsOpen B' ∧ w₀ ∈ B' ∧ B' ⊆ B ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞)
        (fun q ↦ actualTangent (E := E) (Γ q.1) q.2) (B' ×ˢ Ioo (s - T) (s + T)) := by
  let seed : W → E × E := fun w ↦ phaseChart (E := E) old (actualTangent (E := E) (Γ w) s)
  have hch : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E × E) (n : ℕ∞)
      (phaseChart (E := E) old) (actualTangent (E := E) (Γ w₀) s) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)
  have hsmooth : ContDiffAt ℝ (n : ℕ∞) seed w₀ := (hch.comp w₀ hreg).contDiffAt
  obtain ⟨N, hN, hNs⟩ := hsmooth.contDiffOn le_rfl (by norm_num)
  have hsrcnear : ∀ᶠ w in 𝓝 w₀, actualTangent (E := E) (Γ w) s ∈ (phaseChart (E := E) old).source :=
    hreg.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source _).mem_nhds hsrc)
  obtain ⟨B₀, hB₀sub, hB₀, hwB₀⟩ :=
    _root_.mem_nhds_iff.mp (inter_mem hN (inter_mem (hB.mem_nhds hw₀) hsrcnear))
  have hB₀N : B₀ ⊆ N := fun w hw ↦ (hB₀sub hw).1
  obtain ⟨B', hB', hwB', hsub, _, hΨ, hΨmap, hsJ, hinit, hode, _⟩ :=
    hΦ.exists_cnRestart n hT hm hCn hB₀ (hNs.mono hB₀N) hwB₀ hp s
  let Ψ : W × ℝ → E × E := fun q ↦ Φ (seed q.1, τ + (q.2 - s))
  have hB'B : B' ⊆ B := fun w hw ↦ (hB₀sub (hsub hw)).2.1
  have hid := hF.identify_phaseFamily old isOpen_Ioo isPreconnected_Ioo hsJ
    (fun w hw ↦ hΓ w (hB'B hw))
    (hΨ.of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hn))) hΨmap hode
    (fun w hw ↦ by
      exact ((phaseChart (E := E) old).left_inv (hB₀sub (hsub hw)).2.2).symm.trans
        (congrArg (phaseChart (E := E) old).symm (hinit w hw).symm))
  refine ⟨B', hB', hwB', hB'B, ?_⟩
  have hcomp : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞)
      ((phaseChart (E := E) old).symm ∘ Ψ) (B' ×ˢ Ioo (s - T) (s + T)) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).comp hΨ.contMDiffOn (fun q hq ↦ by
        rw [tangentChart_target]
        exact ⟨(hΨmap hq).1, mem_univ _⟩)
  exact hcomp.congr (fun q hq ↦ hid q.1 hq.1 q.2 hq.2)

private theorem restart_time_neighborhood_cn [T2Space M] (hF : F.IsSmoothStronglyConvex)
    (n : ℕ) (hn : 2 ≤ n)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) {w₀ : W} (hw₀ : w₀ ∈ B) (t : ℝ) :
    ∃ N ∈ 𝓝 t, ∀ s ∈ N,
      ContMDiffAt 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞)
        (fun w ↦ actualTangent (E := E) (Γ w) s) w₀ →
      ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞)
        (fun q ↦ actualTangent (E := E) (Γ q.1) q.2) (w₀, t) := by
  let old := Γ w₀ t
  have hc := hΓ w₀ hw₀
  have hsrc := actualTangent_mem_source (E := E) old
    (mem_extChartAt_source old)
  let p := phaseChart (E := E) old (actualTangent (E := E) (Γ w₀) t)
  have hp : p ∈ chartEnergyDomain old := by
    dsimp only [p]
    rw [hF.phaseChart_actualTangent (hc t (mem_univ t)) old (mem_extChartAt_source old)]
    obtain ⟨J, _, ht, _, _, hphase, _⟩ :=
      hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt
        (hc t (mem_univ t)) old (mem_extChartAt_source old)
    exact hphase t ht
  obtain ⟨r, T, hr, hT, Φ, hΦ, hm, hCn⟩ :=
    LocalFlow.exists_cnFlow_in_open n hn (isOpen_chartEnergyDomain old)
      (hF.contDiffOn_chartEulerLagrangeVectorField old) hp t
  have htc : Continuous (fun s ↦ actualTangent (E := E) (Γ w₀) s) :=
    continuousOn_univ.mp (hF.continuousOn_tangentCurve_of_isEulerLagrangeOn isOpen_univ hc)
  have hch : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E × E) (n : ℕ∞)
      (phaseChart (E := E) old) (actualTangent (E := E) (Γ w₀) t) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)
  have hn₁ : ∀ᶠ s in 𝓝 t,
      actualTangent (E := E) (Γ w₀) s ∈ (phaseChart (E := E) old).source :=
    htc.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source _).mem_nhds hsrc)
  have hn₂ : ∀ᶠ s in 𝓝 t,
      phaseChart (E := E) old (actualTangent (E := E) (Γ w₀) s) ∈ ball p r :=
    (hch.continuousAt.comp htc.continuousAt).preimage_mem_nhds
      (isOpen_ball.mem_nhds (mem_ball_self (by exact_mod_cast hr)))
  have hn₃ : Ioo (t - T) (t + T) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  refine ⟨_, inter_mem hn₁ (inter_mem hn₂ hn₃), ?_⟩
  intro s hs hreg
  obtain ⟨B', hB', hwB', _, hsm⟩ := hF.tangentFamily_restart_cn n hn old hB hΓ hw₀
    hΦ hT hm hCn hreg hs.1 hs.2.1
  have ht : t ∈ Ioo (s - T) (s + T) := by
    constructor <;> linarith [hs.2.2.1, hs.2.2.2]
  exact hsm.contMDiffAt ((hB'.prod isOpen_Ioo).mem_nhds ⟨hwB', ht⟩)

/-- Any finite order of dependence of the actual initial tangent propagates along
every complete intrinsic solution. No joint regularity at a later time or common
coordinate chart is assumed. -/
theorem contMDiffAt_tangentFamily_of_initial_cn [T2Space M] (hF : F.IsSmoothStronglyConvex)
    (n : ℕ) (hn : 2 ≤ n)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) {w₀ : W} (hw₀ : w₀ ∈ B)
    {s₀ : ℝ} (hinit : ContMDiffAt 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞)
      (fun w ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨s₀, (1 : ℝ)⟩) w₀) :
    ∀ t : ℝ, ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞)
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (w₀, t) := by
  let G : W × ℝ → TangentBundle 𝓘(ℝ, E) M := fun q ↦ actualTangent (E := E) (Γ q.1) q.2
  let P : Set ℝ := {t | ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞) G (w₀, t)}
  have hnon : P.Nonempty := by
    obtain ⟨N, hN, hn⟩ := hF.restart_time_neighborhood_cn n hn hB hΓ hw₀ s₀
    exact ⟨s₀, hn s₀ (mem_of_mem_nhds hN) hinit⟩
  have hopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have he : ∀ᶠ q in 𝓝 (w₀, t),
        ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞) G q :=
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp ht
    exact (continuousAt_const.prodMk continuousAt_id).tendsto.eventually he
  have hclosed : IsClosed P := by
    apply isClosed_iff_nhds.mpr
    intro t ht
    obtain ⟨N, hN, hn⟩ := hF.restart_time_neighborhood_cn n hn hB hΓ hw₀ t
    obtain ⟨s, hsN, hsP⟩ := ht N hN
    apply hn s hsN
    change ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) (n : ℕ∞) G (w₀, s) at hsP
    exact hsP.comp w₀ ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)
  have hall : P = univ := (show IsClopen P from ⟨hclosed, hopen⟩).eq_univ hnon
  intro t
  change t ∈ P
  rw [hall]
  exact mem_univ t

/-- Smooth dependence of the actual initial tangent gives joint smoothness of the
same complete family at every time, by finite-order propagation at the same point. -/
theorem contMDiffAt_tangentFamily_of_initial_smooth [T2Space M]
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) {w₀ : W} (hw₀ : w₀ ∈ B)
    {s₀ : ℝ} (hinit : ContMDiffAt 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun w ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨s₀, (1 : ℝ)⟩) w₀)
    (t : ℝ) :
    ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (w₀, t) := by
  apply contMDiffAt_infty.mpr
  intro n
  have h := hF.contMDiffAt_tangentFamily_of_initial_cn (max n 2) (le_max_right _ _)
    hB hΓ hw₀ (hinit.of_le (by simp)) t
  exact h.of_le (by
    exact_mod_cast (show (n : ℕ∞) ≤ ((max n 2 : ℕ) : ℕ∞) by exact_mod_cast le_max_left n 2))

/-- Initial smoothness throughout the original parameter domain gives joint smoothness
of the same actual tangent family on that domain and all real times. -/
theorem contMDiffOn_tangentFamily_of_initial_smooth [T2Space M]
    (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    {s₀ : ℝ} (hinit : ContMDiffOn 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun w ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨s₀, (1 : ℝ)⟩) B) :
    ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) := by
  intro q hq
  exact (hF.contMDiffAt_tangentFamily_of_initial_smooth hB hΓ hq.1
    (hinit.contMDiffAt (hB.mem_nhds hq.1)) q.2).contMDiffWithinAt

/-- The original smooth chart seed and prescribed actual initial tangent suffice to
upgrade the already constructed complete family and its position to joint smoothness.
This applies directly to the existing smooth normalized potential-level seeds. -/
theorem contMDiffOn_tangentFamily_of_chartSeed_smooth [T2Space M]
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    {ι : W → E × E} (hι : ContDiffOn ℝ ∞ ι B)
    (hιDomain : MapsTo ι B (chartEnergyDomain old)) {s₀ : ℝ}
    (hinit : ∀ w ∈ B,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨s₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (ι w)) :
    ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ) ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E) ∞ (fun q ↦ Γ q.1 q.2) (B ×ˢ univ) := by
  have hm : MapsTo ι B (phaseChart (E := E) old).target := by
    intro w hw
    rw [phaseChart, tangentChart_target]
    exact ⟨(hιDomain hw).1, mem_univ _⟩
  have hi : ContMDiffOn 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun w ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨s₀, (1 : ℝ)⟩) B :=
    ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).comp hι.contMDiffOn hm).congr hinit
  have hG := hF.contMDiffOn_tangentFamily_of_initial_smooth hB hΓ hi
  exact ⟨hG, fun q hq ↦ (Bundle.contMDiffWithinAt_totalSpace.mp (hG q hq)).1⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
end
