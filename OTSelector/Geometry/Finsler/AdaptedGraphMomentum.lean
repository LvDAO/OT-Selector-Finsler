import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.AdaptedGraphLagrangian
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthHomogeneity
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphTime

/-!
# Geometry.Finsler.AdaptedGraphMomentum

* **Conditions:** The original C2 Hamiltonian family, genuine linear splitting and its actual graph inverse with positive longitudinal velocity.
* **Objects:** Adapted graph momentum as original momentum pulled through the inverse splitting and divided by speed, hence a C2 graph phase.
* **Proof detail:** Apply length-momentum homogeneity and the actual inverse graph chain rule to the original phase formula.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedGraphMomentum.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedGraphMomentum`; the selected original proof blocks follow. -/
section

/-!
# Actual graph momentum in adapted linear coordinates

For a genuine linear coordinate splitting of the original Finsler model, graph
momentum is the spatial restriction of the inverse-linear pullback of original energy
momentum, divided by original speed. The same original Hamiltonian phase and graph
inverse therefore give joint C2 graph phase without a C3 position assumption.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual spatial position and length momentum of the same adapted graph family. -/
def adaptedGraphPhase (F : ContinuousFinslerNorm E M) (old : M)
    (A : E ≃L[ℝ] (ℝ × V)) (γ : W × ℝ → ℝ × V)
    (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)) (q : W × ℝ) :
    V × (V →L[ℝ] ℝ) :=
  ((curveGraphPosition γ e q).2,
    fiberLegendre (F.adaptedGraphLagrangian old A)
      ((q.2, (curveGraphPosition γ e q).2),
        deriv (fun s ↦ (curveGraphPosition γ e (q.1, s)).2) q.2))

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- Adapted graph momentum is the true transformed original momentum divided by speed. -/
theorem adaptedGraphMomentum_of_rescaled_velocity (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {z : E × E} (hz : z ∈ chartEnergyDomain old) {a : ℝ} (ha : 0 < a) {η : V}
    (hv : (1, η) = a • A z.2) :
    fiberLegendre (F.adaptedGraphLagrangian old A) (A z.1, η) =
      (((F.chartLength old z : ℝ)⁻¹ • fiberLegendre (F.chartEnergy old) z).comp
        A.symm.toContinuousLinearMap).comp (ContinuousLinearMap.inr ℝ ℝ V) := by
  have hza : (z.1, a • z.2) ∈ chartEnergyDomain old :=
    ⟨hz.1, smul_ne_zero ha.ne' hz.2⟩
  have hv' : A.symm (1, η) = a • z.2 := by
    rw [hv, _root_.map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have hd : HasFDerivAt (fun v ↦ (F.chartLength old (z.1, v) : ℝ))
      (fiberLegendre (fun q ↦ (F.chartLength old q : ℝ)) (z.1, a • z.2))
      (A.symm (1, η)) := by
    rw [hv']
    exact ((hF.contDiffAt_chartFiberLength old hza).differentiableAt (by simp)).hasFDerivAt
  have hi := A.symm.hasFDerivAt.comp η (hasFDerivAt_prodMk_right (𝕜 := ℝ) 1 η)
  have hg := (hd.comp η hi).fderiv
  change fiberLegendre (F.adaptedGraphLagrangian old A) (A z.1, η) = _
  have hgraph : fiberLegendre (F.adaptedGraphLagrangian old A) (A z.1, η) =
      (fiberLegendre (fun q ↦ (F.chartLength old q : ℝ)) (z.1, a • z.2)).comp
        (A.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ V)) := by
    simpa only [fiberLegendre, adaptedGraphLagrangian,
      ContinuousLinearEquiv.symm_apply_apply, Function.comp_def] using hg
  rw [hgraph, hF.chartLength_fiberLegendre_pos_smul old hz ha,
    hF.chartLegendre_eq_length_smul_fderiv old hz]
  have hS : (F.chartLength old z : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (F.chartLength_pos old hz)).ne'
  simp [fiberLegendre, smul_smul, hS, ContinuousLinearMap.comp_assoc]

/-- The actual adapted graph phase is recovered from the same original Hamiltonian phase. -/
theorem adaptedGraphPhase_eq_rescaled_energy (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {ℓ : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hℓ : (ℓ : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : ℓ.source ⊆ chartEnergyDomain old)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun q ↦ A (Ψ q).1))
    {q : W × ℝ} (hq : q ∈ e.target)
    (hΨ : DifferentiableAt ℝ Ψ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hp : Ψ (e.symm q) ∈ ℓ.target)
    (hODE : HasDerivAt (fun s ↦ Ψ ((e.symm q).1, s))
      (localHamiltonianVectorField (F.chartEnergy old) ℓ (Ψ (e.symm q))) (e.symm q).2)
    (hpos : 0 < (fderiv ℝ (fun z ↦ A (Ψ z).1) (e.symm q) (0, 1)).1) :
    F.adaptedGraphPhase old A (fun z ↦ A (Ψ z).1) e q =
      ((A (Ψ (e.symm q)).1).2,
        (((F.chartLength old (ℓ.symm (Ψ (e.symm q))) : ℝ)⁻¹ •
          (Ψ (e.symm q)).2).comp A.symm.toContinuousLinearMap).comp
            (ContinuousLinearMap.inr ℝ ℝ V)) := by
  let γ := fun z ↦ A (Ψ z).1
  let z := ℓ.symm (Ψ (e.symm q))
  let v := fderiv ℝ γ (e.symm q) (0, 1)
  have hz : z ∈ chartEnergyDomain old := hsub (ℓ.map_target hp)
  have hinv := parametricLegendre_inverse_components hℓ hp
  have hγ : DifferentiableAt ℝ γ (e.symm q) := A.differentiableAt.comp _ hΨ.fst
  have hv : v = A z.2 := by
    have h1 := hγ.hasFDerivAt.comp_hasDerivAt (e.symm q).2
      ((hasDerivAt_const (e.symm q).2 (e.symm q).1).prodMk
        (hasDerivAt_id (e.symm q).2))
    exact h1.unique (A.hasFDerivAt.comp_hasDerivAt (e.symm q).2
      (hasDerivAt_hamiltonian_position hODE))
  have hΓ := curveGraphPosition_slice_hasDerivAt he hq hγ hi hpos.ne'
  have hy : HasDerivAt (fun s ↦ (curveGraphPosition γ e (q.1, s)).2)
      (v.1⁻¹ • v).2 q.2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'] using!
      (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt.comp_hasDerivAt q.2 hΓ
  have hvel : (1, deriv (fun s ↦ (curveGraphPosition γ e (q.1, s)).2) q.2) =
      v.1⁻¹ • A z.2 := by
    apply Prod.ext
    · change 1 = v.1⁻¹ * (A z.2).1
      rw [← hv]
      exact (inv_mul_cancel₀ hpos.ne').symm
    · rw [hy.deriv, ← hv]
  have hbase : (q.2, (curveGraphPosition γ e q).2) = A z.1 := by
    apply Prod.ext
    · exact (curveGraph_inverse_components he hq).2.symm.trans
        (congrArg (fun u : E ↦ (A u).1) hinv.1.symm)
    · exact congrArg (fun u : E ↦ (A u).2) hinv.1.symm
  refine Prod.ext ?_ ?_
  · rfl
  change fiberLegendre (F.adaptedGraphLagrangian old A)
    ((q.2, (curveGraphPosition γ e q).2), _) = _
  rw [hbase, hF.adaptedGraphMomentum_of_rescaled_velocity old A hz
    (inv_pos.mpr hpos) hvel, hinv.2]

/-- Joint C2 follows from original momentum and speed, without differentiating position thrice. -/
theorem contDiffOn_adaptedGraphPhase (old : M) (A : E ≃L[ℝ] (ℝ × V))
    {ℓ : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hℓ : (ℓ : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy old))
    (hsub : ℓ.source ⊆ chartEnergyDomain old) (hℓi : ContDiffOn ℝ ∞ ℓ.symm ℓ.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D) (hmap : MapsTo Ψ D ℓ.target)
    (hODE : ∀ p ∈ D, HasDerivAt (fun s ↦ Ψ (p.1, s))
      (localHamiltonianVectorField (F.chartEnergy old) ℓ (Ψ p)) p.2)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ A (Ψ z).1))
    (hesub : e.source ⊆ D) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hpos : ∀ p ∈ e.source, 0 < (fderiv ℝ (fun z ↦ A (Ψ z).1) p (0, 1)).1) :
    ContDiffOn ℝ 2 (F.adaptedGraphPhase old A (fun z ↦ A (Ψ z).1) e) e.target := by
  let R := Ψ ∘ e.symm
  let Z := ℓ.symm ∘ R
  let S := fun q ↦ (F.chartLength old (Z q) : ℝ)
  have hR : ContDiffOn ℝ 2 R e.target :=
    hΨ.comp hi (fun _ hq ↦ hesub (e.map_target hq))
  have hRmap : MapsTo R e.target ℓ.target := fun _ hq ↦ hmap (hesub (e.map_target hq))
  have hZ : ContDiffOn ℝ 2 Z e.target := (hℓi.of_le (by simp)).comp hR hRmap
  have hZmap : MapsTo Z e.target (chartEnergyDomain old) :=
    fun _ hq ↦ hsub (ℓ.map_target (hRmap hq))
  have hS : ContDiffOn ℝ 2 S e.target :=
    ((hF.contDiffOn_chartLength old).of_le (by simp)).comp hZ hZmap
  have hS0 : ∀ q ∈ e.target, S q ≠ 0 := fun q hq ↦
    (NNReal.coe_pos.mpr (F.chartLength_pos old (hZmap hq))).ne'
  have hm : ContDiffOn ℝ 2 (fun q ↦
      (((S q)⁻¹ • (R q).2).comp A.symm.toContinuousLinearMap).comp
        (ContinuousLinearMap.inr ℝ ℝ V)) e.target :=
    (((hS.inv hS0).smul hR.snd).clm_comp contDiffOn_const).clm_comp contDiffOn_const
  apply ((A.contDiff.comp_contDiffOn hR.fst).snd.prodMk hm).congr
  intro q hq
  exact hF.adaptedGraphPhase_eq_rescaled_energy old A hℓ hsub he hq
    ((hΨ.contDiffAt (hD.mem_nhds (hesub (e.map_target hq)))).differentiableAt
      (by norm_num))
    ((hi.contDiffAt (e.open_target.mem_nhds hq)).differentiableAt (by norm_num))
    (hRmap hq) (hODE _ (hesub (e.map_target hq))) (hpos _ (e.map_target hq))

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
