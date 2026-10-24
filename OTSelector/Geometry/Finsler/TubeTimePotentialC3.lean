import OTSelector.Analysis.Calculus.FlowJetMatching
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.ManifoldTubeCalibration
import OTSelector.Geometry.Manifold.ManifoldFlowTimePotential

/-!
# Geometry.Finsler.TubeTimePotentialC3

* **Conditions:** The actual C2 tube inverse and jointly C2 tangent family, with the proved original momentum differential identity.
* **Objects:** C3 regularity of the actual inverse-time potential.
* **Proof detail:** Compose actual C2 chart momentum with the same inverse tube, identify the true coordinate differential and upgrade potential regularity.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (derived): No C3 family or independently more regular inverse is assumed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeTimePotentialC3.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeTimePotentialC3`; the selected original proof blocks follow. -/
section

/-!
# C3 regularity of the actual Finsler tube time potential

The original chart energy momentum is C2 along the same actual C2 tangent family.
Composing it with the C2 inverse tube makes the true coordinate differential C2,
so the actual time potential is C3. No C3 family or inverse regularity is assumed.
All chart calculations are local at the point under consideration.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_chartPotential_of_mfderiv
    {ψ : M → ℝ} (old : M) {z : E}
    (hz : z ∈ (extChartAt 𝓘(ℝ, E) old).target)
    (hψ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓘(ℝ, E) old).symm z))
    (p : E →L[ℝ] ℝ)
    (hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓘(ℝ, E) old).symm z) =
      p.comp (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old)
        ((extChartAt 𝓘(ℝ, E) old).symm z))) :
    HasFDerivAt (ψ ∘ (extChartAt 𝓘(ℝ, E) old).symm) p z := by
  have hs : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old).symm z :=
    ((contMDiffOn_extChartAt_symm (n := 1) old).contMDiffAt
      ((isOpen_extChartAt_target old).mem_nhds hz)).mdifferentiableAt (by norm_num)
  have hinv := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hinv
  have heq : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ψ ((extChartAt 𝓘(ℝ, E) old).symm z)).comp
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old).symm z) = p := by
    rw [hd]
    ext v
    have hv := congrArg (fun A : E →L[ℝ] E ↦ A v) hinv
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old)
      ((extChartAt 𝓘(ℝ, E) old).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old).symm z v) = v at hv
    change p (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old)
      ((extChartAt 𝓘(ℝ, E) old).symm z)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old).symm z v)) = p v
    rw [hv]
  exact heq ▸ (hψ.hasMFDerivAt.comp z hs.hasMFDerivAt).hasFDerivAt

/-- The actual chart momentum composed with the same C2 tube inverse is C2 locally. -/
theorem contDiffAt_manifoldTube_chartMomentum (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (e : OpenPartialHomeomorph (ℝ × W) M)
    (heq : (e : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    (hsource : e.source ⊆ univ ×ˢ B)
    (hinverse : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) 2 e.symm e.target)
    (old : M) {z : E} (hz : z ∈ (extChartAt 𝓘(ℝ, E) old).target)
    (hx : (extChartAt 𝓘(ℝ, E) old).symm z ∈ e.target) :
    ContDiffAt ℝ 2 (fun y ↦ (F.chartMomentumFamily old Γ
      ((e.symm ((extChartAt 𝓘(ℝ, E) old).symm y)).2,
        (e.symm ((extChartAt 𝓘(ℝ, E) old).symm y)).1)).2) z := by
  let x := (extChartAt 𝓘(ℝ, E) old).symm z
  let q := e.symm x
  have hqx : Γ q.2 q.1 = x := by
    rw [← congrFun heq q]
    exact e.right_inv hx
  have hm := hF.contDiffAt_chartMomentumFamily_of_tangentFamily hB hEL hG
    (hsource (e.map_target hx)).2 old q.1
    (hqx ▸ (extChartAt 𝓘(ℝ, E) old).map_target hz)
  have hs : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 2
      (extChartAt 𝓘(ℝ, E) old).symm z :=
    (contMDiffOn_extChartAt_symm old).contMDiffAt
      ((isOpen_extChartAt_target old).mem_nhds hz)
  have hi := (hinverse.contMDiffAt (e.open_target.mem_nhds hx)).comp z hs
  have h := hm.snd.comp z (hi.contDiffAt.snd.prodMk hi.contDiffAt.fst)
  exact h

/-- The same original unit normal family has a C3 inverse-time potential on the
whole actual tube. Only its actual tangent family and inverse tube are assumed C2. -/
theorem contMDiffOn_manifoldTubeTime_C3 (hF : F.IsSmoothStronglyConvex)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    (e : OpenPartialHomeomorph (ℝ × W) M)
    (heq : (e : ℝ × W → M) = fun q ↦ Γ q.2 q.1)
    (hsource : e.source ⊆ univ ×ˢ B)
    (hinverse : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) 2 e.symm e.target)
    (hunit : ∀ q ∈ e.source,
      (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) : ℝ) = 1)
    (hnormal : ∀ q ∈ e.source, ∀ old : M,
      Γ q.2 q.1 ∈ (extChartAt 𝓘(ℝ, E) old).source → ∀ ξ : W,
      (F.chartMomentumFamily old Γ (q.2, q.1)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w q.1)) q.2 ξ) = 0)
    (t₀ : ℝ) :
    ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 3 (manifoldFlowTimePotential e 1 t₀) e.target := by
  let ψ := manifoldFlowTimePotential e 1 t₀
  have hψ : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 2 ψ e.target :=
    contMDiffOn_manifoldFlowTimePotential e hinverse 1 t₀
  have hder (old : M) (z : E) (hz : z ∈ (extChartAt 𝓘(ℝ, E) old).target)
      (hx : (extChartAt 𝓘(ℝ, E) old).symm z ∈ e.target) :
      HasFDerivAt (ψ ∘ (extChartAt 𝓘(ℝ, E) old).symm)
        (F.chartMomentumFamily old Γ
          ((e.symm ((extChartAt 𝓘(ℝ, E) old).symm z)).2,
            (e.symm ((extChartAt 𝓘(ℝ, E) old).symm z)).1)).2 z := by
    let x := (extChartAt 𝓘(ℝ, E) old).symm z
    let q := e.symm x
    have hq : q ∈ e.source := e.map_target hx
    have hqx : Γ q.2 q.1 = x := by
      rw [← congrFun heq q]
      exact e.right_inv hx
    have hlegal : Γ q.2 q.1 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
      rw [hqx]
      exact (extChartAt 𝓘(ℝ, E) old).map_target hz
    have hd := hF.mfderiv_manifoldTubeTime_eq_chartMomentum hB hEL hG e heq hsource
      hinverse hq t₀ old hlegal (hunit q hq) (hnormal q hq old hlegal)
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ψ (Γ q.2 q.1) =
      (F.chartMomentumFamily old Γ (q.2, q.1)).2.comp
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) (Γ q.2 q.1)) at hd
    rw [hqx] at hd
    exact hasFDerivAt_chartPotential_of_mfderiv old hz
      ((hψ.contMDiffAt (e.open_target.mem_nhds hx)).mdifferentiableAt (by norm_num)) _ hd
  intro x hx
  let c := extChartAt 𝓘(ℝ, E) x
  let U := c.target ∩ c.symm ⁻¹' e.target
  have hU : IsOpen U := (contMDiffOn_extChartAt_symm (n := 2) x).continuousOn
    |>.isOpen_inter_preimage (isOpen_extChartAt_target x) e.open_target
  have hz : c x ∈ c.target := mem_extChartAt_target x
  have hzU : c x ∈ U := by
    refine ⟨hz, ?_⟩
    change c.symm (c x) ∈ e.target
    rw [c.left_inv (mem_extChartAt_source x)]
    exact hx
  have hC3 : ContDiffAt ℝ 3 (ψ ∘ c.symm) (c x) := by
    apply (contDiffAt_succ_iff_hasFDerivAt (n := 2)).2
    refine ⟨fun y ↦ (F.chartMomentumFamily x Γ
      ((e.symm (c.symm y)).2, (e.symm (c.symm y)).1)).2,
      ⟨U, hU.mem_nhds hzU, fun y hy ↦ hder x y hy.1 hy.2⟩, ?_⟩
    exact hF.contDiffAt_manifoldTube_chartMomentum hB hEL hG e heq hsource hinverse
      x hz hzU.2
  have hm : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 3 ψ x := by
    apply contMDiffAt_iff_source.mpr
    simpa only [modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ] using
      hC3.contMDiffAt
  exact hm.contMDiffWithinAt

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
