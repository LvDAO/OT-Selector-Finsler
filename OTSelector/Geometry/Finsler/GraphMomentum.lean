import OTSelector.Analysis.Calculus.Variational.GraphEulerLagrange
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Graph
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthHomogeneity
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphTime
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerGraphMomentum.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerGraphMomentum`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.GraphMomentum

* **Conditions:** An actual C2 Hamiltonian phase family, its graph inverse, positive longitudinal velocity and the same inverse Legendre branch.
* **Objects:** Graph momentum as spatial original momentum divided by original speed, and joint C2 regularity of its actual graph phase.
* **Proof detail:** Use degree-zero length momentum under positive rescaling, identify it with energy momentum/speed and compose the actual C2 phase with its graph inverse.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The momentum formula avoids requiring C3 regularity of the position projection.
-/

/-!
# Actual graph momentum from the original Hamiltonian phase

Graph length momentum is the spatial restriction of original energy momentum divided
by original speed. Positive reparameterization leaves length momentum unchanged.
For the same actual Hamiltonian family and graph inverse, this formula proves joint C2
regularity of the graph phase without assuming C3 regularity of its position projection.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ℝ × V) M]
  [IsManifold 𝓘(ℝ, ℝ × V) ∞ M]

/-- Position and actual graph-length momentum of the same reparameterized family. -/
def chartGraphPhase (F : ContinuousFinslerNorm (ℝ × V) M) (x₀ : M)
    (γ : W × ℝ → ℝ × V) (e : OpenPartialHomeomorph (W × ℝ) (W × ℝ))
    (q : W × ℝ) : V × (V →L[ℝ] ℝ) :=
  ((curveGraphPosition γ e q).2,
    fiberLegendre (F.chartGraphLagrangian x₀)
      ((q.2, (curveGraphPosition γ e q).2),
        deriv (fun s ↦ (curveGraphPosition γ e (q.1, s)).2) q.2))

namespace IsSmoothStronglyConvex
variable {F : ContinuousFinslerNorm (ℝ × V) M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- Actual graph momentum is energy momentum divided by old speed and restricted to space. -/
theorem chartGraphMomentum_of_rescaled_velocity (x₀ : M) {z : (ℝ × V) × (ℝ × V)}
    (hz : z ∈ chartEnergyDomain x₀) {a : ℝ} (ha : 0 < a) {η : V}
    (hv : (1, η) = a • z.2) :
    fiberLegendre (F.chartGraphLagrangian x₀) (z.1, η) =
      ((F.chartLength x₀ z : ℝ)⁻¹ • fiberLegendre (F.chartEnergy x₀) z).comp
        (ContinuousLinearMap.inr ℝ ℝ V) := by
  have hza : (z.1, (1, η)) ∈ chartEnergyDomain x₀ :=
    ⟨hz.1, hv ▸ smul_ne_zero ha.ne' hz.2⟩
  have hd := ((hF.contDiffOn_chartLength x₀).contDiffAt
    ((isOpen_chartEnergyDomain x₀).mem_nhds hza)).differentiableAt (by simp)
  have hg := fiberLegendre_graphRestriction
    (L := fun q ↦ (F.chartLength x₀ q : ℝ)) (z := (z.1, η)) hd
  change fiberLegendre (fun q : (ℝ × V) × V ↦
    (F.chartLength x₀ (q.1, (1, q.2)) : ℝ)) (z.1, η) = _
  rw [hg]
  congr 1
  rw [hv, hF.chartLength_fiberLegendre_pos_smul x₀ hz ha,
    hF.chartLegendre_eq_length_smul_fderiv x₀ hz]
  have hS : (F.chartLength x₀ z : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (F.chartLength_pos x₀ hz)).ne'
  simp [fiberLegendre, smul_smul, hS]

/-- The same original Hamiltonian family and graph inverse recover the actual graph momentum. -/
theorem chartGraphPhase_eq_rescaled_energy (x₀ : M)
    {ℓ : OpenPartialHomeomorph (((ℝ × V) × (ℝ × V)))
      ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))}
    (hℓ : (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀)
    {Ψ : W × ℝ → (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ (Ψ z).1))
    {q : W × ℝ} (hq : q ∈ e.target)
    (hΨ : DifferentiableAt ℝ Ψ (e.symm q)) (hi : DifferentiableAt ℝ e.symm q)
    (hp : Ψ (e.symm q) ∈ ℓ.target)
    (hODE : HasDerivAt (fun s ↦ Ψ ((e.symm q).1, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ (e.symm q))) (e.symm q).2)
    (hpos : 0 < (fderiv ℝ (fun z ↦ (Ψ z).1) (e.symm q) (0, 1)).1) :
    F.chartGraphPhase x₀ (fun z ↦ (Ψ z).1) e q =
      ((Ψ (e.symm q)).1.2,
        ((F.chartLength x₀ (ℓ.symm (Ψ (e.symm q))) : ℝ)⁻¹ •
          (Ψ (e.symm q)).2).comp (ContinuousLinearMap.inr ℝ ℝ V)) := by
  let γ := fun z ↦ (Ψ z).1
  let z := ℓ.symm (Ψ (e.symm q))
  let v := fderiv ℝ γ (e.symm q) (0, 1)
  have hz : z ∈ chartEnergyDomain x₀ := hsub (ℓ.map_target hp)
  have hinv := parametricLegendre_inverse_components hℓ hp
  have hv : v = z.2 := by
    have h1 := hΨ.fst.hasFDerivAt.comp_hasDerivAt (e.symm q).2
      ((hasDerivAt_const (e.symm q).2 (e.symm q).1).prodMk
        (hasDerivAt_id (e.symm q).2))
    exact h1.unique (hasDerivAt_hamiltonian_position hODE)
  have hΓ := curveGraphPosition_slice_hasDerivAt he hq hΨ.fst hi hpos.ne'
  have hy : HasDerivAt (fun s ↦ (curveGraphPosition γ e (q.1, s)).2)
      (v.1⁻¹ • v).2 q.2 := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_snd'] using!
      (ContinuousLinearMap.snd ℝ ℝ V).hasFDerivAt.comp_hasDerivAt q.2 hΓ
  have hvel : (1, deriv (fun s ↦ (curveGraphPosition γ e (q.1, s)).2) q.2) =
      v.1⁻¹ • z.2 := by
    apply Prod.ext
    · change 1 = v.1⁻¹ * z.2.1
      rw [← hv]
      exact (inv_mul_cancel₀ hpos.ne').symm
    · rw [hy.deriv, ← hv]
  have hbase : (q.2, (curveGraphPosition γ e q).2) = z.1 := by
    apply Prod.ext
    · exact (curveGraph_inverse_components he hq).2.symm.trans
        (congrArg Prod.fst hinv.1.symm)
    · have hh := congrArg (fun b : ℝ × V ↦ b.2) hinv.1.symm
      exact hh
  refine Prod.ext ?_ ?_
  · rfl
  change fiberLegendre (F.chartGraphLagrangian x₀)
    ((q.2, (curveGraphPosition γ e q).2), _) = _
  rw [hbase, hF.chartGraphMomentum_of_rescaled_velocity x₀ hz (inv_pos.mpr hpos) hvel]
  rw [hinv.2]

/-- The actual graph phase is jointly C2 by its original energy-momentum representation. -/
theorem contDiffOn_chartGraphPhase (x₀ : M)
    {ℓ : OpenPartialHomeomorph ((ℝ × V) × (ℝ × V))
      ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))}
    (hℓ : (ℓ : ((ℝ × V) × (ℝ × V)) → ((ℝ × V) × ((ℝ × V) →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀) (hℓi : ContDiffOn ℝ ∞ ℓ.symm ℓ.target)
    {Ψ : W × ℝ → (ℝ × V) × ((ℝ × V) →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hD : IsOpen D) (hΨ : ContDiffOn ℝ 2 Ψ D) (hmap : MapsTo Ψ D ℓ.target)
    (hODE : ∀ p ∈ D, HasDerivAt (fun s ↦ Ψ (p.1, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ p)) p.2)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ (Ψ z).1))
    (hesub : e.source ⊆ D) (hi : ContDiffOn ℝ 2 e.symm e.target)
    (hpos : ∀ p ∈ e.source, 0 < (fderiv ℝ (fun z ↦ (Ψ z).1) p (0, 1)).1) :
    ContDiffOn ℝ 2 (F.chartGraphPhase x₀ (fun z ↦ (Ψ z).1) e) e.target := by
  let R := Ψ ∘ e.symm
  let Z := ℓ.symm ∘ R
  let S := fun q ↦ (F.chartLength x₀ (Z q) : ℝ)
  have hR : ContDiffOn ℝ 2 R e.target :=
    hΨ.comp hi (fun _ hq ↦ hesub (e.map_target hq))
  have hRmap : MapsTo R e.target ℓ.target := fun _ hq ↦ hmap (hesub (e.map_target hq))
  have hZ : ContDiffOn ℝ 2 Z e.target := (hℓi.of_le (by simp)).comp hR hRmap
  have hZmap : MapsTo Z e.target (chartEnergyDomain x₀) :=
    fun _ hq ↦ hsub (ℓ.map_target (hRmap hq))
  have hS : ContDiffOn ℝ 2 S e.target :=
    ((hF.contDiffOn_chartLength x₀).of_le (by simp)).comp hZ hZmap
  have hS0 : ∀ q ∈ e.target, S q ≠ 0 := fun q hq ↦
    (NNReal.coe_pos.mpr (F.chartLength_pos x₀ (hZmap hq))).ne'
  have hm : ContDiffOn ℝ 2
      (fun q ↦ ((S q)⁻¹ • (R q).2).comp (ContinuousLinearMap.inr ℝ ℝ V)) e.target :=
    ((hS.inv hS0).smul hR.snd).clm_comp contDiffOn_const
  apply (hR.fst.snd.prodMk hm).congr
  intro q hq
  exact hF.chartGraphPhase_eq_rescaled_energy x₀ hℓ hsub he hq
    ((hΨ.contDiffAt (hD.mem_nhds (hesub (e.map_target hq)))).differentiableAt
      (by norm_num))
    ((hi.contDiffAt (e.open_target.mem_nhds hq)).differentiableAt (by norm_num))
    (hRmap hq) (hODE _ (hesub (e.map_target hq))) (hpos _ (e.map_target hq))

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
