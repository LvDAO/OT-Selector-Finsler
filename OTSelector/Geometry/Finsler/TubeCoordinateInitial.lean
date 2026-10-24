import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.TangentReadout
import OTSelector.Geometry.Finsler.TubeCoordinateEnergy
import OTSelector.Geometry.Finsler.TubeCoordinateEulerLagrange
import OTSelector.Geometry.Finsler.TubeCoordinateFamily

/-!
# Geometry.Finsler.TubeCoordinateInitial

* **Conditions:** A genuine smooth tube and the actual prescribed initial tangent family; only the central initial point must lie in the tube.
* **Objects:** Injectivity of actual initial tube tangent and momentum derivatives.
* **Proof detail:** Construct a true local left inverse from original initial tangent coordinates, differentiate it and compose with the positive invertible tube Legendre differential.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): Initial phase rank is derived; continuity constructs the neighboring legal domain.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateInitial.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateInitial`; the selected original proof blocks follow. -/
section

/-!
# Initial derivative injectivity in genuine tube coordinates

The original prescribed tangent gives a true local left inverse of the actual initial
tube tangent family. Differentiating this identity proves injectivity without a rank
premise. The original strictly convex energy then preserves this injectivity in the
actual tube position-momentum coordinates. Only the central initial point must lie
in the tube; continuity constructs the necessary neighboring parameter domain.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [FiniteDimensional ℝ E] {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] in
private theorem tube_initial_tangent_differentiable
    (old : M) (a : ℝ) {Y : OpenPartialHomeomorph V M}
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : (E × E) → ℝ → M}
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old) (hx : Γ z a ∈ Y.target) :
    DifferentiableAt ℝ (fun w ↦ tubeCoordinateTangentFamily Y Γ (w, a)) z := by
  let D := (chartEnergyDomain old ×ˢ univ) ∩
    (fun q : (E × E) × ℝ ↦ Γ q.1 q.2) ⁻¹' Y.target
  have hc : ContinuousOn (fun q : (E × E) × ℝ ↦ Γ q.1 q.2)
      (chartEnergyDomain old ×ˢ univ) :=
    (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).comp_continuousOn
      hG.continuousOn
  have hD : IsOpen D := hc.isOpen_inter_preimage
    ((isOpen_chartEnergyDomain old).prod isOpen_univ) Y.open_target
  have hT := contDiffOn_tubeCoordinateTangentFamily hi hD (hG.mono inter_subset_left)
    (fun _ hq ↦ hq.2)
  exact ((hT.contDiffAt (hD.mem_nhds ⟨⟨hz, mem_univ _⟩, hx⟩)).comp z
    (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by norm_num)

private theorem tangentLift_tubeCoordinate_eq_chartPhase
    (hF : F.IsSmoothStronglyConvex) (old : M) {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {c : ℝ → M} {t : ℝ} (hc : F.IsEulerLagrangeAt c t)
    (hx : c t ∈ Y.target) (ho : c t ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    tangentLift (extChartAt 𝓘(ℝ, E) old ∘ Y)
      ((Y.symm ∘ c) t, deriv (Y.symm ∘ c) t) =
      ((extChartAt 𝓘(ℝ, E) old ∘ c) t, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t) := by
  have hcC := hF.contMDiffAt_of_isEulerLagrangeAt hc
  have hiC := hi.contMDiffAt (Y.open_target.mem_nhds hx)
  have hYC := hY.contMDiffAt (Y.open_source.mem_nhds (Y.map_target hx))
  have hχ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) old)
      (Y (Y.symm (c t))) := by
    rw [Y.right_inv hx]
    exact contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using ho)
  have hφ := (hχ.comp (Y.symm (c t)) hYC).contDiffAt
  have hy := (hiC.comp t hcC).contDiffAt
  have heq : ((extChartAt 𝓘(ℝ, E) old ∘ Y) ∘ (Y.symm ∘ c)) =ᶠ[𝓝 t]
      (extChartAt 𝓘(ℝ, E) old ∘ c) := by
    filter_upwards [hcC.continuousAt.preimage_mem_nhds (Y.open_target.mem_nhds hx)]
      with s hs
    change extChartAt 𝓘(ℝ, E) old (Y (Y.symm (c s))) = _
    rw [Y.right_inv hs]
    rfl
  rw [tangentLift_curve_eq (hφ.differentiableAt (by simp))
    (hy.differentiableAt (by simp)), heq.eq_of_nhds, heq.deriv_eq]

/-- Prescribing the original initial tangent forces injectivity of the actual initial
position-velocity derivative in any genuine smooth tube containing that point. -/
theorem injective_fderiv_initial_tubeCoordinateTangentFamily
    (hF : F.IsSmoothStronglyConvex) (old : M) (a : ℝ)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : (E × E) → ℝ → M}
    (hEL : ∀ w ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ w) univ)
    (hinit : ∀ w ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm w)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old) (hx : Γ z a ∈ Y.target) :
    Function.Injective (fderiv ℝ (fun w ↦ tubeCoordinateTangentFamily Y Γ (w, a)) z) := by
  let T := fun w ↦ tubeCoordinateTangentFamily Y Γ (w, a)
  let φ := extChartAt 𝓘(ℝ, E) old ∘ Y
  have hbase (w : E × E) (hw : w ∈ chartEnergyDomain old) :
      Γ w a = (extChartAt 𝓘(ℝ, E) old).symm w.1 := by
    have h := congrArg (fun q : TangentBundle 𝓘(ℝ, E) M ↦ q.1) (hinit w hw)
    rw [tangentChart_symm_eq old hw.1 w.2] at h
    exact h
  have hold (w : E × E) (hw : w ∈ chartEnergyDomain old) :
      Γ w a ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    rw [hbase w hw]
    exact (extChartAt 𝓘(ℝ, E) old).map_target hw.1
  have hT : DifferentiableAt ℝ T z := tube_initial_tangent_differentiable old a hi hG hz hx
  have hc : ContinuousAt (fun w : E × E ↦ Γ w a) z := by
    have h := (hG.contMDiffAt
      (((isOpen_chartEnergyDomain old).prod isOpen_univ).mem_nhds ⟨hz, mem_univ a⟩)).comp z
      ((contDiffAt_id.prodMk (contDiffAt_const (c := a))).contMDiffAt)
    exact (FiberBundle.continuous_proj E (TangentSpace 𝓘(ℝ, E))).continuousAt.comp
      h.continuousAt
  have heq : tangentLift φ ∘ T =ᶠ[𝓝 z] id := by
    filter_upwards [(isOpen_chartEnergyDomain old).mem_nhds hz,
      hc.preimage_mem_nhds (Y.open_target.mem_nhds hx)] with w hw hwY
    exact (hF.tangentLift_tubeCoordinate_eq_chartPhase old hY hi
      (hEL w hw a (mem_univ _)) hwY (hold w hw)).trans
      (hF.chartPhase_of_tangent_eq (hEL w hw a (mem_univ _)) old hw (hinit w hw))
  have hχ : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) old)
      (Y (T z).1) := by
    change ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (extChartAt 𝓘(ℝ, E) old)
      (Y (Y.symm (Γ z a)))
    rw [Y.right_inv hx]
    exact contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hold z hz)
  have hφ : ContDiffAt ℝ ∞ φ (T z).1 :=
    (hχ.comp (T z).1 (hY.contMDiffAt (Y.open_source.mem_nhds (Y.map_target hx)))).contDiffAt
  have hLift : DifferentiableAt ℝ (tangentLift φ) (T z) :=
    ((hφ.differentiableAt (by simp)).comp (T z) differentiableAt_fst).prodMk
      ((((hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).comp
        (T z) differentiableAt_fst).clm_apply differentiableAt_snd)
  have hcomp : (fderiv ℝ (tangentLift φ) (T z)).comp (fderiv ℝ T z) =
      ContinuousLinearMap.id ℝ (E × E) :=
    (hLift.hasFDerivAt.comp z hT.hasFDerivAt).fderiv.symm.trans
      (heq.fderiv_eq.trans fderiv_id)
  intro u v huv
  have h := congrArg (fderiv ℝ (tangentLift φ) (T z)) huv
  change ((fderiv ℝ (tangentLift φ) (T z)).comp (fderiv ℝ T z)) u =
    ((fderiv ℝ (tangentLift φ) (T z)).comp (fderiv ℝ T z)) v at h
  simpa only [hcomp, ContinuousLinearMap.id_apply] using h

/-- Strict convexity of the original fiber energy also forces injectivity of the
actual initial position-momentum derivative in the same genuine smooth tube. -/
theorem injective_fderiv_initial_tubeCoordinateMomentumFamily [FiniteDimensional ℝ V]
    (hF : F.IsSmoothStronglyConvex) (old : M) (a : ℝ)
    {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : (E × E) → ℝ → M}
    (hEL : ∀ w ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ w) univ)
    (hinit : ∀ w ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm w)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z : E × E} (hz : z ∈ chartEnergyDomain old) (hx : Γ z a ∈ Y.target) :
    Function.Injective
      (fderiv ℝ (fun w ↦ F.tubeCoordinateMomentumFamily Y Γ (w, a)) z) := by
  let T := fun w ↦ tubeCoordinateTangentFamily Y Γ (w, a)
  let L := F.tubeCoordinateEnergy Y
  have hT : DifferentiableAt ℝ T z := tube_initial_tangent_differentiable old a hi hG hz hx
  obtain ⟨I, _, ha, _, _, hvel, _⟩ :=
    hF.exists_tubeCoordinateEulerLagrangeOn_of_isEulerLagrangeAt
      hY hi (hEL z hz a (mem_univ _)) hx
  have hphase : T z ∈ Y.source ×ˢ {v : V | v ≠ 0} := ⟨Y.map_target hx, hvel a ha⟩
  have hL : ContDiffAt ℝ ∞ L (T z) :=
    (hF.contDiffOn_tubeCoordinateEnergy Y hY hi).contDiffAt
      ((Y.open_source.prod isOpen_ne).mem_nhds hphase)
  have hPL := (contDiffAt_parametricLegendre hL).differentiableAt (by simp)
  have hpos : ∀ v : V, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun η ↦ L ((T z).1, η))) (T z).2 v v :=
    fun v hv ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi hphase.1 hphase.2 hv
  change Function.Injective (fderiv ℝ (parametricLegendre L ∘ T) z)
  rw [(hPL.hasFDerivAt.comp z hT.hasFDerivAt).fderiv]
  exact (parametricLegendre_fderiv_bijective hL hpos).injective.comp
    (hF.injective_fderiv_initial_tubeCoordinateTangentFamily old a hY hi hEL hinit hG hz hx)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
