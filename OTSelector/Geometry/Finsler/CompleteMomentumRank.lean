import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.FlowLocalC2
import OTSelector.Geometry.Finsler.FlowRank
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeVectorField
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.TangentChartCurve
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCompleteMomentumRank.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCompleteMomentumRank`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CompleteMomentumRank

* **Conditions:** The actual complete tangent family and its genuine Legendre transform in a legal final chart.
* **Objects:** Full rank of actual complete chart-momentum derivatives and preservation of immersed seed rank.
* **Proof detail:** Differentiate the actual chart momentum factorization into phase chart followed by Legendre, then compose the two invertible differentials.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Full rank of actual complete Finsler momentum families

The true chart Legendre differential is invertible by the original positive vertical
Hessian. Composing it with the full initial-tangent derivative transports actual phase
rank to momentum coordinates, for the same complete family and every admissible chart.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

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

private theorem actual_chartPhase (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t) (old : M)
    (hx : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    phaseChart (E := E) old (actualTangent (E := E) c t) =
      ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) ∧
    ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) ∈
      chartEnergyDomain old := by
  obtain ⟨J, hJ, ht, hm, hy, hphase, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt hc old hx
  have heq : c =ᶠ[𝓝 t] (extChartAt 𝓘(ℝ, E) old).symm ∘
      (extChartAt 𝓘(ℝ, E) old ∘ c) := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact ((extChartAt 𝓘(ℝ, E) old).left_inv (hm hs)).symm
  have htan : actualTangent (E := E) c t =
      actualTangent (E := E) ((extChartAt 𝓘(ℝ, E) old).symm ∘
        (extChartAt 𝓘(ℝ, E) old ∘ c)) t := by
    refine TotalSpace.ext heq.eq_of_nhds ?_
    rw [actualTangent, tangentMap, heq.eq_of_nhds, actualTangent, tangentMap, heq.mfderiv_eq]
  have hp := tangentMap_chart_symm_curve old (hphase t ht).1
    (((hy.contDiffAt (hJ.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt)
  refine ⟨?_, hphase t ht⟩
  rw [htan.trans hp, (phaseChart (E := E) old).right_inv]
  rw [tangentChart_target]
  exact ⟨(hphase t ht).1, mem_univ _⟩

private theorem momentum_slice_differentiable (hF : F.IsSmoothStronglyConvex)
    (initial old : M) {Γ : (E × E) → ℝ → M}
    (hΓ : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ actualTangent (E := E) (Γ q.1) q.2)
      (chartEnergyDomain initial ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain initial) (t : ℝ)
    (hx : Γ z t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    DifferentiableAt ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) z ∧
    fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) z =
      (fderiv ℝ (parametricLegendre (F.chartEnergy old))
        (phaseChart (E := E) old (actualTangent (E := E) (Γ z) t))).comp
        (fderiv ℝ (fun w ↦ phaseChart (E := E) old
          (actualTangent (E := E) (Γ w) t)) z) := by
  let A : (E × E) → E × E := fun w ↦
    phaseChart (E := E) old (actualTangent (E := E) (Γ w) t)
  have hsrc : actualTangent (E := E) (Γ z) t ∈ (phaseChart (E := E) old).source := by
    simpa only [phaseChart, FiberBundle.chartedSpace_chartAt, mfld_simps] using hx
  have hslice := (hG.contMDiffAt
    (((isOpen_chartEnergyDomain initial).prod isOpen_univ).mem_nhds
      ⟨hz, mem_univ t⟩)).comp z
        ((contDiffAt_id.prodMk (contDiffAt_const (c := t))).contMDiffAt)
  have hchart : ContMDiffAt (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 𝓘(ℝ, E × E) 2
      (phaseChart (E := E) old) (actualTangent (E := E) (Γ z) t) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hsrc)
  have hA : DifferentiableAt ℝ A z :=
    ((hchart.comp z hslice).contDiffAt).differentiableAt (by norm_num)
  have hAz : A z ∈ chartEnergyDomain old := by
    obtain ⟨he, hm⟩ := hF.actual_chartPhase (hΓ z hz t (mem_univ t)) old hx
    change phaseChart (E := E) old (actualTangent (E := E) (Γ z) t) ∈ _
    rw [he]
    exact hm
  have hL := (contDiffAt_parametricLegendre ((hF.contDiffOn_chartEnergy old).contDiffAt
    ((isOpen_chartEnergyDomain old).mem_nhds hAz))).differentiableAt (by simp)
  have hnear : ∀ᶠ w in 𝓝 z,
      actualTangent (E := E) (Γ w) t ∈ (phaseChart (E := E) old).source :=
    hslice.continuousAt.preimage_mem_nhds ((isOpen_extChartAt_source _).mem_nhds hsrc)
  have heq : (fun w ↦ F.chartMomentumFamily old Γ (w, t)) =ᶠ[𝓝 z]
      parametricLegendre (F.chartEnergy old) ∘ A := by
    filter_upwards [(isOpen_chartEnergyDomain initial).mem_nhds hz, hnear] with w hw hs
    have hb : Γ w t ∈ (extChartAt 𝓘(ℝ, E) old).source := by
      simpa only [phaseChart, FiberBundle.chartedSpace_chartAt, mfld_simps] using hs
    obtain ⟨he, _⟩ := hF.actual_chartPhase (hΓ w hw t (mem_univ t)) old hb
    change parametricLegendre (F.chartEnergy old)
      ((extChartAt 𝓘(ℝ, E) old ∘ Γ w) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ w) t) = _
    exact congrArg (parametricLegendre (F.chartEnergy old)) he.symm
  exact ⟨(hL.comp z hA).congr_of_eventuallyEq heq,
    heq.fderiv_eq.trans (hL.hasFDerivAt.comp z hA.hasFDerivAt).fderiv⟩

/-- The same complete intrinsic family has invertible full phase derivative in actual
position-momentum coordinates, using the original positive vertical Hessian. -/
theorem isInvertible_fderiv_complete_chartMomentumFamily [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ)
    {Γ : (E × E) → ℝ → M}
    (hΓ : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain initial ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain initial) (old : M) (t : ℝ)
    (hx : Γ z t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) z).IsInvertible := by
  obtain ⟨he, hm⟩ := hF.actual_chartPhase (hΓ z hz t (mem_univ t)) old hx
  have hphase := he.symm ▸ hm
  obtain ⟨d, hd⟩ := hF.isInvertible_fderiv_complete_tangentFamily
    hcomplete initial t₀ hΓ hinit hG hz old t hx
  obtain ⟨l, hl⟩ := isInvertible_fderiv_parametricLegendre
    ((hF.contDiffOn_chartEnergy old).contDiffAt
      ((isOpen_chartEnergyDomain old).mem_nhds hphase))
    (fun w hw ↦ hF.chartEnergy_hessian_pos old hphase hw)
  rw [(hF.momentum_slice_differentiable initial old hΓ hG hz t hx).2, ← hd, ← hl]
  exact ⟨d.trans l, rfl⟩

/-- Every differentiable injected seed retains full rank in the actual momentum family. -/
theorem injective_fderiv_seeded_complete_chartMomentumFamily
    [T2Space M] [PreconnectedSpace M] (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ)
    {Γ : (E × E) → ℝ → M}
    (hΓ : ∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain initial,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain initial ×ˢ univ))
    {seed : W → E × E} {w₀ : W} (hs : DifferentiableAt ℝ seed w₀)
    (hinj : Function.Injective (fderiv ℝ seed w₀))
    (hz : seed w₀ ∈ chartEnergyDomain initial) (old : M) (t : ℝ)
    (hx : Γ (seed w₀) t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    Function.Injective
      (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (seed w, t)) w₀) := by
  let A := fun z ↦ F.chartMomentumFamily old Γ (z, t)
  have hA : DifferentiableAt ℝ A (seed w₀) :=
    (hF.momentum_slice_differentiable initial old hΓ hG hz t hx).1
  have hi : Function.Injective (fderiv ℝ A (seed w₀)) := by
    obtain ⟨d, hd⟩ := hF.isInvertible_fderiv_complete_chartMomentumFamily
      hcomplete initial t₀ hΓ hinit hG hz old t hx
    rw [← hd]
    exact d.injective
  change Function.Injective (fderiv ℝ (A ∘ seed) w₀)
  rw [(hA.hasFDerivAt.comp w₀ hs.hasFDerivAt).fderiv]
  exact hi.comp hinj

/-- Original completeness constructs one complete family with exact initial tangents,
jointly C2 actual momenta, original Hamiltonian dynamics and full phase rank at all times. -/
theorem exists_complete_chartMomentumFamily_invertible [T2Space M] [PreconnectedSpace M]
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M) (t₀ : ℝ) :
    ∃ Γ : (E × E) → ℝ → M,
      (∀ z ∈ chartEnergyDomain initial, F.IsEulerLagrangeOn (Γ z) univ) ∧
      (∀ z ∈ chartEnergyDomain initial,
        tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨t₀, (1 : ℝ)⟩ =
          (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
            (⟨initial, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z) ∧
      ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
        (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
        (chartEnergyDomain initial ×ˢ univ) ∧
      (∀ z ∈ chartEnergyDomain initial, ∀ old : M, ∀ t : ℝ,
        Γ z t ∈ (extChartAt 𝓘(ℝ, E) old).source →
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) z).IsInvertible) ∧
      ∀ (old : M) (D : Set ((E × E) × ℝ)), D ⊆ chartEnergyDomain initial ×ˢ univ →
        (∀ q ∈ D, Γ q.1 q.2 ∈ (extChartAt 𝓘(ℝ, E) old).source) →
        ContDiffOn ℝ 2 (F.chartMomentumFamily old Γ) D ∧
        ∀ e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ)),
          (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old) →
          e.source ⊆ chartEnergyDomain old → ∀ q ∈ D,
          F.chartMomentumFamily old Γ q ∈ e.target →
          HasDerivAt (fun s ↦ F.chartMomentumFamily old Γ (q.1, s))
            (localHamiltonianVectorField (F.chartEnergy old) e
              (F.chartMomentumFamily old Γ q)) q.2 := by
  obtain ⟨Γ, hEL, hi, hG⟩ := hF.exists_complete_tangentFamily_C2 hcomplete initial t₀
  refine ⟨Γ, hEL, hi, hG, ?_, ?_⟩
  · exact fun z hz old t hx ↦ hF.isInvertible_fderiv_complete_chartMomentumFamily
      hcomplete initial t₀ hEL hi hG hz old t hx
  · intro old D hD hm
    have hELD (q : (E × E) × ℝ) (hq : q ∈ D) : F.IsEulerLagrangeAt (Γ q.1) q.2 :=
      hEL q.1 (hD hq).1 q.2 (mem_univ _)
    refine ⟨hF.contDiffOn_chartMomentumFamily old hELD (hG.mono hD) hm, ?_⟩
    intro e he hs q hq hp
    exact hF.hasDerivAt_chartMomentum old (hELD q hq) (hm q hq) he hs hp

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
