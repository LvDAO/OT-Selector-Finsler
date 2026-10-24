import OTSelector.Analysis.Calculus.Variational.HamiltonianFlatBase
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.Hessian
import OTSelector.Geometry.Finsler.TubeCoordinateEnergy
import OTSelector.Geometry.Finsler.TubeCoordinateEulerLagrange
import OTSelector.Geometry.Finsler.TubeCoordinateFamily

/-!
# Geometry.Finsler.TubeCoordinateVariation

* **Conditions:** Actual tube coordinates of an intrinsic C2 family, original strict convexity and the stated vanishing actual base Hessian columns.
* **Objects:** The true parameter momentum-variation equation with inverse actual vertical tube Hessian.
* **Proof detail:** Construct a local Legendre inverse from tube energy positivity, restrict the actual family into it and differentiate its derived Euler–Lagrange equation.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerTubeCoordinateVariation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerTubeCoordinateVariation`; the selected original proof blocks follow. -/
section

/-!
# Actual momentum variations in genuine tube coordinates

The true tube energy constructs a smooth local Legendre inverse. Restricting the
actual tangent family to the inverse source identifies its true momentum dynamics.
Joint C2 regularity and the actual Euler--Lagrange equation then give the parameter
variation equation, with the inverse actual fiber Hessian when base columns vanish.
No inverse branch, Hamiltonian ODE, momentum regularity or variation equation is assumed.
-/

open Set Filter Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E V W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- The actual parameter variation of the original family's tube momentum obeys the
inverse-fiber-Hessian equation when the true scalar energy has zero base Hessian columns. -/
theorem hasDerivAt_tubeCoordinateMomentumVariation_of_hessian_base_zero
    (hF : F.IsSmoothStronglyConvex) {Y : OpenPartialHomeomorph V M}
    (hY : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ Y Y.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, V) ∞ Y.symm Y.target)
    {Γ : W → ℝ → M} {D : Set (W × ℝ)} (hD : IsOpen D)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) D)
    (hmap : ∀ q ∈ D, Γ q.1 q.2 ∈ Y.target)
    (hEL : ∀ q ∈ D, F.IsEulerLagrangeAt (Γ q.1) q.2)
    {w : W} {t : ℝ} (hq : (w, t) ∈ D)
    (hzero : ∀ u : V, fderiv ℝ (fderiv ℝ (F.tubeCoordinateEnergy Y))
      (tubeCoordinateTangentFamily Y Γ (w, t)) (u, 0) = 0) (ξ : W) :
    HasDerivAt
      (fun s ↦ fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, s)) w ξ)
      (ContinuousLinearMap.inverse (verticalEnergyHessian (F.tubeCoordinateEnergy Y)
        (tubeCoordinateTangentFamily Y Γ (w, t)))
        (fderiv ℝ (fun v ↦ F.tubeCoordinateMomentumFamily Y Γ (v, t)) w ξ).2, 0) t := by
  let L := F.tubeCoordinateEnergy Y
  let T := tubeCoordinateTangentFamily Y Γ
  let Ψ := F.tubeCoordinateMomentumFamily Y Γ
  let U := Y.source ×ˢ {v : V | v ≠ 0}
  have hU : IsOpen U := Y.open_source.prod isOpen_ne
  have hL : ContDiffOn ℝ ∞ L U := hF.contDiffOn_tubeCoordinateEnergy Y hY hi
  have hpos : ∀ z ∈ U, ∀ v : V, v ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun η ↦ L (z.1, η))) z.2 v v :=
    fun z hz v hv ↦ hF.tubeCoordinateEnergy_fiber_hessian_pos hY hi hz.1 hz.2 hv
  have hT : ContDiffOn ℝ 2 T D :=
    contDiffOn_tubeCoordinateTangentFamily hi hD hG hmap
  have hΨ : ContDiffOn ℝ 2 Ψ D :=
    hF.contDiffOn_tubeCoordinateMomentumFamily hY hi hD hG hmap hEL
  have hz : T (w, t) ∈ U :=
    tubeCoordinateTangentFamily_mem_domain hY hi hD hG hq (hmap _ hq) (hEL _ hq)
  obtain ⟨e, he, hsource, _, hsub, hInv, _, hX, _⟩ :=
    exists_smooth_localHamiltonian hU hL hpos hz
  let N := D ∩ T ⁻¹' e.source
  have hN : IsOpen N := hT.continuousOn.isOpen_inter_preimage hD e.open_source
  have hqN : (w, t) ∈ N := ⟨hq, hsource⟩
  have htarget : MapsTo Ψ N e.target := by
    intro q hq'
    change parametricLegendre L (T q) ∈ e.target
    rw [← he]
    exact e.map_source hq'.2
  have hODE (q : W × ℝ) (hq' : q ∈ N) :
      HasDerivAt (fun s ↦ Ψ (q.1, s))
        (localHamiltonianVectorField L e (Ψ q)) q.2 := by
    obtain ⟨I, hI, ht, _, hy, _, hEq⟩ :=
      hF.exists_tubeCoordinateEulerLagrangeOn_of_isEulerLagrangeAt
        hY hi (hEL q hq'.1) (hmap q hq'.1)
    exact hasDerivAt_eulerLagrangePhaseLift he
      ((hy.contDiffAt (hI.mem_nhds ht)).differentiableAt (by norm_num)) hq'.2 (hEq q.2 ht)
  have hvar := hasDerivAt_parameterVariation_of_nonautonomousODE
    (X := fun _ ↦ localHamiltonianVectorField L e) hN (hΨ.mono inter_subset_left)
    hODE hqN
    ((hX.contDiffAt (e.open_target.mem_nhds (htarget hqN))).differentiableAt (by simp)) ξ
  have hident : e.symm (Ψ (w, t)) = T (w, t) := by
    change e.symm (parametricLegendre L (T (w, t))) = T (w, t)
    rw [← he]
    exact e.left_inv hsource
  have hflat : ∀ u : V, fderiv ℝ (fderiv ℝ L) (e.symm (Ψ (w, t))) (u, 0) = 0 := by
    simpa only [hident] using hzero
  have hpositive : ∀ v : V, v ≠ 0 →
      0 < verticalEnergyHessian L (e.symm (Ψ (w, t))) v v := by
    rw [hident]
    exact hpos _ hz
  rw [localHamiltonianVectorField_fderiv_of_hessian_base_zero he
    (hL.mono hsub) hInv (htarget hqN) hflat hpositive, hident] at hvar
  exact hvar

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
