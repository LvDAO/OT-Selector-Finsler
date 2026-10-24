import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.C2FlowRestart
import OTSelector.Analysis.ODE.Flow.LocalC2
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Complete
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeVectorField
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.TangentChartCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerFlowLocalC2.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerFlowLocalC2`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.FlowLocalC2

* **Conditions:** Complete actual intrinsic Euler–Lagrange solutions with C2 initial tangent dependence; completeness is needed only for the existence interface.
* **Objects:** Joint local/all-time C2 regularity of the same complete tangent family and its actual chart phase.
* **Proof detail:** Identify a local coordinate solution by the actual initial tangent and uniqueness, restart in legal charts and propagate regularity along the connected time line.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Joint local regularity of the actual complete Finsler flow

Local coordinate flows are identified with the complete intrinsic solutions by their
actual initial tangent. Regularity can therefore propagate without a fixed global chart.
-/

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

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
private theorem actualTangent_congr {c d : ℝ → M} {t : ℝ}
    (h : c =ᶠ[𝓝 t] d) : actualTangent (E := E) c t = actualTangent (E := E) d t := by
  refine TotalSpace.ext h.eq_of_nhds ?_
  rw [actualTangent, tangentMap, h.eq_of_nhds, actualTangent, tangentMap, h.mfderiv_eq]

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

private theorem actualTangent_chart (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hsource : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    actualTangent (E := E) c t = (phaseChart (E := E) old).symm
      ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) := by
  obtain ⟨J, hJ, ht, hm, hx, hphase, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc old hsource
  have heq : c =ᶠ[𝓝 t] (extChartAt 𝓘(ℝ, E) old).symm ∘
      (extChartAt 𝓘(ℝ, E) old ∘ c) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hm hs)).symm
  exact (actualTangent_congr heq).trans
    (tangentMap_chart_symm_curve old (hphase t ht).1
      (((hx.contDiffAt (hJ.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt))

private theorem actualTangent_mem_source (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hsource : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    actualTangent (E := E) c t ∈ (phaseChart (E := E) old).source := by
  rw [hF.actualTangent_chart hc old hsource]
  apply (phaseChart (E := E) old).map_target
  rw [phaseChart, tangentChart_target]
  exact ⟨(extChartAt 𝓘(ℝ, E) old).map_source hsource, mem_univ _⟩

private theorem phaseChart_actualTangent (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hsource : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    phaseChart (E := E) old (actualTangent (E := E) c t) =
      ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) := by
  rw [hF.actualTangent_chart hc old hsource]
  apply (phaseChart (E := E) old).right_inv
  rw [phaseChart, tangentChart_target]
  exact ⟨(extChartAt 𝓘(ℝ, E) old).map_source hsource, mem_univ _⟩

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

private theorem tangentFamily_restart [T2Space M] (hF : F.IsSmoothStronglyConvex)
    (old : M) {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) {w₀ : W} (hw₀ : w₀ ∈ B)
    {p : E × E} {r : ℝ≥0} {τ T s : ℝ} {Φ : (E × E) × ℝ → E × E}
    (hΦ : LocalFlow.IsLocalFlow (fun _ ↦ eulerLagrangeVectorField (F.chartEnergy old))
      τ p r (τ - T) (τ + T) Φ) (hT : 0 < T)
    (hm : MapsTo Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)) (chartEnergyDomain old))
    (hC2 : ContDiffOn ℝ 2 Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)))
    (hreg : ContMDiffAt 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun w ↦ actualTangent (E := E) (Γ w) s) w₀)
    (hsrc : actualTangent (E := E) (Γ w₀) s ∈ (phaseChart (E := E) old).source)
    (hp : phaseChart (E := E) old (actualTangent (E := E) (Γ w₀) s) ∈ ball p r) :
    ∃ B' : Set W, IsOpen B' ∧ w₀ ∈ B' ∧ B' ⊆ B ∧
      ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ actualTangent (E := E) (Γ q.1) q.2) (B' ×ˢ Ioo (s - T) (s + T)) := by
  let seed : W → E × E := fun w ↦ phaseChart (E := E) old (actualTangent (E := E) (Γ w) s)
  have hch : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E × E) 2
      (phaseChart (E := E) old) (actualTangent (E := E) (Γ w₀) s) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)
  have hsmooth : ContDiffAt ℝ 2 seed w₀ := (hch.comp w₀ hreg).contDiffAt
  obtain ⟨N, hN, hNs⟩ := hsmooth.contDiffOn le_rfl (by norm_num)
  have hsrcnear : ∀ᶠ w in 𝓝 w₀, actualTangent (E := E) (Γ w) s ∈ (phaseChart (E := E) old).source :=
    hreg.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source _).mem_nhds hsrc)
  obtain ⟨B₀, hB₀sub, hB₀, hwB₀⟩ :=
    _root_.mem_nhds_iff.mp (inter_mem hN (inter_mem (hB.mem_nhds hw₀) hsrcnear))
  have hB₀N : B₀ ⊆ N := fun w hw ↦ (hB₀sub hw).1
  obtain ⟨B', hB', hwB', hsub, _, hΨ, hΨmap, hsJ, hinit, hode, _⟩ :=
    hΦ.exists_c2Restart hT hm hC2 hB₀ (hNs.mono hB₀N) hwB₀ hp s
  let Ψ : W × ℝ → E × E := fun q ↦ Φ (seed q.1, τ + (q.2 - s))
  have hB'B : B' ⊆ B := fun w hw ↦ (hB₀sub (hsub hw)).2.1
  have hid := hF.identify_phaseFamily old isOpen_Ioo isPreconnected_Ioo hsJ
    (fun w hw ↦ hΓ w (hB'B hw)) hΨ hΨmap hode
    (fun w hw ↦ by
      exact ((phaseChart (E := E) old).left_inv (hB₀sub (hsub hw)).2.2).symm.trans
        (congrArg (phaseChart (E := E) old).symm (hinit w hw).symm))
  refine ⟨B', hB', hwB', hB'B, ?_⟩
  have hcomp : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      ((phaseChart (E := E) old).symm ∘ Ψ) (B' ×ˢ Ioo (s - T) (s + T)) :=
    (contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).comp hΨ.contMDiffOn (fun q hq ↦ by
        rw [tangentChart_target]
        exact ⟨(hΨmap hq).1, mem_univ _⟩)
  exact hcomp.congr (fun q hq ↦ hid q.1 hq.1 q.2 hq.2)

private theorem restart_time_neighborhood [T2Space M] (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) {w₀ : W} (hw₀ : w₀ ∈ B) (t : ℝ) :
    ∃ N ∈ 𝓝 t, ∀ s ∈ N,
      ContMDiffAt 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun w ↦ actualTangent (E := E) (Γ w) s) w₀ →
      ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ actualTangent (E := E) (Γ q.1) q.2) (w₀, t) := by
  let old := Γ w₀ t
  have hc := hΓ w₀ hw₀
  have hsrc := hF.actualTangent_mem_source (hc t (mem_univ t)) old
    (mem_extChartAt_source old)
  let p := phaseChart (E := E) old (actualTangent (E := E) (Γ w₀) t)
  have hp : p ∈ chartEnergyDomain old := by
    dsimp only [p]
    rw [hF.phaseChart_actualTangent (hc t (mem_univ t)) old (mem_extChartAt_source old)]
    obtain ⟨J, _, ht, _, _, hphase, _⟩ :=
      hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt
        (hc t (mem_univ t)) old (mem_extChartAt_source old)
    exact hphase t ht
  obtain ⟨r, T, hr, hT, Φ, hΦ, hm, hC2, _⟩ :=
    LocalFlow.exists_c2Flow_in_open (isOpen_chartEnergyDomain old)
      (hF.contDiffOn_chartEulerLagrangeVectorField old) hp t
  have htc : Continuous (fun s ↦ actualTangent (E := E) (Γ w₀) s) :=
    continuousOn_univ.mp (hF.continuousOn_tangentCurve_of_isEulerLagrangeOn isOpen_univ hc)
  have hch : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E × E) 2
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
  obtain ⟨B', hB', hwB', _, hsm⟩ := hF.tangentFamily_restart old hB hΓ hw₀
    hΦ hT hm hC2 hreg hs.1 hs.2.1
  have ht : t ∈ Ioo (s - T) (s + T) := by
    constructor <;> linarith [hs.2.2.1, hs.2.2.2]
  exact hsm.contMDiffAt ((hB'.prod isOpen_Ioo).mem_nhds ⟨hwB', ht⟩)

/-- C2 dependence of the actual initial tangent propagates along every complete intrinsic
solution. No joint regularity at a later time or common coordinate chart is assumed. -/
theorem contMDiffAt_tangentFamily_of_initial [T2Space M] (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hΓ : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ) {w₀ : W} (hw₀ : w₀ ∈ B)
    {s₀ : ℝ} (hinit : ContMDiffAt 𝓘(ℝ, W) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun w ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨s₀, (1 : ℝ)⟩) w₀) :
    ∀ t : ℝ, ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (w₀, t) := by
  let G : W × ℝ → TangentBundle 𝓘(ℝ, E) M := fun q ↦ actualTangent (E := E) (Γ q.1) q.2
  let P : Set ℝ := {t | ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2 G (w₀, t)}
  have hnon : P.Nonempty := by
    obtain ⟨N, hN, hn⟩ := hF.restart_time_neighborhood hB hΓ hw₀ s₀
    exact ⟨s₀, hn s₀ (mem_of_mem_nhds hN) hinit⟩
  have hopen : IsOpen P := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    have he : ∀ᶠ q in 𝓝 (w₀, t),
        ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2 G q :=
      (contMDiffAt_iff_contMDiffAt_nhds (by norm_num)).mp ht
    exact (continuousAt_const.prodMk continuousAt_id).tendsto.eventually he
  have hclosed : IsClosed P := by
    apply isClosed_iff_nhds.mpr
    intro t ht
    obtain ⟨N, hN, hn⟩ := hF.restart_time_neighborhood hB hΓ hw₀ t
    obtain ⟨s, hsN, hsP⟩ := ht N hN
    apply hn s hsN
    change ContMDiffAt 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2 G (w₀, s) at hsP
    exact hsP.comp w₀ ((contDiffAt_id.prodMk contDiffAt_const).contMDiffAt)
  have hall : P = univ := (show IsClopen P from ⟨hclosed, hopen⟩).eq_univ hnon
  intro t
  change t ∈ P
  rw [hall]
  exact mem_univ t

/-- Reading a jointly C2 actual tangent family in a genuine chart gives joint C2
regularity of its actual position-and-time-derivative coordinates. -/
theorem contDiffOn_chartPhase_of_tangentFamily_C2 (hF : F.IsSmoothStronglyConvex)
    (old : M) {Γ : W → ℝ → M} {D : Set (W × ℝ)}
    (hEL : ∀ q ∈ D, F.IsEulerLagrangeAt (Γ q.1) q.2)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D)
    (hmap : ∀ q ∈ D, Γ q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    ContDiffOn ℝ 2 (fun q ↦
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ q.1) q.2,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ q.1) q.2)) D := by
  have hcomp : ContMDiffOn 𝓘(ℝ, W × ℝ) 𝓘(ℝ, E × E) 2
      (fun q ↦ phaseChart (E := E) old (actualTangent (E := E) (Γ q.1) q.2)) D :=
    contMDiffOn_extChartAt.comp hG (fun q hq ↦ by
      change actualTangent (E := E) (Γ q.1) q.2 ∈
        (chartAt (ModelProd E E) (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).source
      simpa only [extChartAt_source] using
        hF.actualTangent_mem_source (hEL q hq) old (hmap q hq))
  exact hcomp.contDiffOn.congr (fun q hq ↦
    (hF.phaseChart_actualTangent (hEL q hq) old (hmap q hq)).symm)

private theorem exists_global_from_chart [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {z : E × E} (hz : z ∈ chartEnergyDomain old) (t₀ : ℝ) :
    ∃ c : ℝ → M, F.IsEulerLagrangeOn c univ ∧
      actualTangent (E := E) c t₀ = (phaseChart (E := E) old).symm z := by
  let x := (extChartAt 𝓘(ℝ, E) old).symm z.1
  let e := (trivializationAt E (TangentSpace 𝓘(ℝ, E)) old).continuousLinearEquivAt ℝ x
    (chartEnergy_base_mem old hz.1)
  have hv : e.symm z.2 ≠ 0 := by
    intro h
    exact hz.2 (e.symm.map_eq_zero_iff.mp h)
  obtain ⟨c, ⟨hc, hi⟩, _⟩ := hF.exists_unique_global_eulerLagrange hcomplete x hv t₀
  refine ⟨c, hc, hi.trans ?_⟩
  exact (tangentChart_symm_eq old hz.1 z.2).symm

/-- The complete original Finsler metric produces a family for every slit initial chart
state. Its actual total tangent depends jointly C2 on the initial state and all real times.
The proof uses local restarts and intrinsic uniqueness, without a global common chart. -/
theorem exists_complete_tangentFamily_C2 [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M) (t₀ : ℝ) :
    ∃ Γ : (E × E) → ℝ → M,
      (∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ) ∧
      (∀ z ∈ chartEnergyDomain old,
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (chartEnergyDomain old ×ˢ univ) := by
  classical
  have hex := fun z hz ↦ hF.exists_global_from_chart hcomplete old (z := z) hz t₀
  let Γ : (E × E) → ℝ → M := fun z ↦
    if hz : z ∈ chartEnergyDomain old then (hex z hz).choose else fun _ ↦ old
  have hΓ (z : E × E) (hz : z ∈ chartEnergyDomain old) :
      F.IsEulerLagrangeOn (Γ z) univ ∧
        actualTangent (E := E) (Γ z) t₀ = (phaseChart (E := E) old).symm z := by
    simpa only [Γ, dite_eq_left hz] using (hex z hz).choose_spec
  refine ⟨Γ, fun z hz ↦ (hΓ z hz).1, fun z hz ↦ (hΓ z hz).2, ?_⟩
  intro q hq
  have htgt : q.1 ∈ (phaseChart (E := E) old).target := by
    rw [tangentChart_target]
    exact ⟨hq.1.1, mem_univ _⟩
  have ho : IsOpen (phaseChart (E := E) old).target := by
    rw [tangentChart_target]
    exact (isOpen_extChartAt_target old).prod isOpen_univ
  have hi : ContMDiffAt 𝓘(ℝ, E × E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun z ↦ actualTangent (E := E) (Γ z) t₀) q.1 := by
    apply ((contMDiffOn_extChartAt_symm (I := 𝓘(ℝ, E).prod 𝓘(ℝ, E))
      (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).contMDiffAt (ho.mem_nhds htgt)).congr_of_eventuallyEq
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hq.1] with z hz
    exact (hΓ z hz).2
  exact (hF.contMDiffAt_tangentFamily_of_initial (isOpen_chartEnergyDomain old)
    (fun z hz ↦ (hΓ z hz).1) hq.1 hi q.2).contMDiffWithinAt

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
