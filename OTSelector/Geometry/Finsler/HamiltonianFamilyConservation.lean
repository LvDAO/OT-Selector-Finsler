import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Jacobi.Pairing
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerHamiltonianFamilyConservation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerHamiltonianFamilyConservation`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.HamiltonianFamilyConservation

* **Conditions:** A C2 actual Hamiltonian family on a connected open time interval whose original energy is common at one time.
* **Objects:** Constant original energy/speed on the whole domain and canonical orthogonality of the actual parameter variation to the Hamiltonian field.
* **Proof detail:** Differentiate Hamiltonian energy along each solution, use connectedness for constancy, then differentiate the proved parameter-independent energy identity.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A derived specialization of the cited differential/ODE principles to the exact Finsler data; constructed branches, phase maps and parameter derivatives belong to the same family throughout.
-/

/-!
# Original energy and speed of the same Hamiltonian family

Common original energy at one initial time propagates on the connected open time domain
by the actual Hamiltonian equation. Equality of original energies gives equality of old
Finsler speeds, with no unit-speed normalization. On an open parameter domain, joint C2
regularity lets us differentiate this proved identity: the actual parameter derivative
is canonically orthogonal to the actual Hamiltonian field. Energy tangency is a conclusion.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

omit [NormedAddCommGroup W] [NormedSpace ℝ W] in
/-- Common original initial energy gives common energy and old speed for the entire family. -/
theorem chartHamiltonianFamily_energy_speed_eq (x₀ : M)
    {ℓ : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hℓ : (ℓ : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀) (hℓi : ContDiffOn ℝ ∞ ℓ.symm ℓ.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {B : Set W} {I : Set ℝ}
    (hI : IsOpen I) (hconn : IsPreconnected I) (hmap : MapsTo Ψ (B ×ˢ I) ℓ.target)
    (hODE : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt (fun s ↦ Ψ (w, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ (w, t))) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) {z₀ : E × E}
    (henergy : ∀ w ∈ B, F.chartEnergy x₀ (ℓ.symm (Ψ (w, t₀))) = F.chartEnergy x₀ z₀) :
    ∀ q ∈ B ×ˢ I,
      F.chartEnergy x₀ (ℓ.symm (Ψ q)) = F.chartEnergy x₀ z₀ ∧
      F.chartLength x₀ (ℓ.symm (Ψ q)) = F.chartLength x₀ z₀ := by
  intro q hq
  have hc := localHamiltonian_eq_of_integralCurve
    (γ := fun t : ℝ ↦ Ψ (q.1, t)) (s := q.2) (t := t₀) hℓ
    ((hF.contDiffOn_chartEnergy x₀).mono hsub) hℓi hI hconn
    (fun t ht ↦ hmap ⟨hq.1, ht⟩) (hODE q.1 hq.1) hq.2 ht₀
  rw [hF.localHamiltonian_chartEnergy_eq x₀ hℓ hsub (hmap hq),
    hF.localHamiltonian_chartEnergy_eq x₀ hℓ hsub (hmap (x := (q.1, t₀)) ⟨hq.1, ht₀⟩)] at hc
  have heq := hc.trans (henergy q.1 hq.1)
  exact ⟨heq, F.chartLength_eq_of_chartEnergy_eq x₀ heq⟩

/-- Differentiating the propagated original energy proves canonical orthogonality of
actual parameter derivatives to the same Hamiltonian field; it is not a premise. -/
theorem chartHamiltonianFamily_parameter_pairing_zero (x₀ : M)
    {ℓ : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (hℓ : (ℓ : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀) (hℓi : ContDiffOn ℝ ∞ ℓ.symm ℓ.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hΨ : ContDiffOn ℝ 2 Ψ (B ×ˢ I)) (hmap : MapsTo Ψ (B ×ˢ I) ℓ.target)
    (hODE : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt (fun s ↦ Ψ (w, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ (w, t))) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) {z₀ : E × E}
    (henergy : ∀ w ∈ B, F.chartEnergy x₀ (ℓ.symm (Ψ (w, t₀))) = F.chartEnergy x₀ z₀)
    {q : W × ℝ} (hq : q ∈ B ×ˢ I) (ξ : W) :
    canonicalPhasePairing (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ q))
      (fderiv ℝ (fun w ↦ Ψ (w, q.2)) q.1 ξ) = 0 := by
  let L := F.chartEnergy x₀
  let H := localHamiltonian L ℓ
  have hL : ContDiffOn ℝ ∞ L ℓ.source := (hF.contDiffOn_chartEnergy x₀).mono hsub
  have hΨa := (hΨ.contDiffAt ((hB.prod hI).mem_nhds hq)).differentiableAt (by norm_num)
  have hPa : DifferentiableAt ℝ (fun w ↦ Ψ (w, q.2)) q.1 :=
    (hΨa.hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left q.1 q.2)).differentiableAt
  have hHa : DifferentiableAt ℝ H (Ψ q) :=
    ((contDiffOn_localHamiltonian hL hℓi).contDiffAt
      (ℓ.open_target.mem_nhds (hmap hq))).differentiableAt (by simp)
  have hHa' : HasFDerivAt H (fderiv ℝ H (Ψ q)) (Ψ (q.1, q.2)) := by
    simpa only [Prod.eta] using hHa.hasFDerivAt
  have hd : HasFDerivAt (fun w ↦ H (Ψ (w, q.2)))
      ((fderiv ℝ H (Ψ q)).comp (fderiv ℝ (fun w ↦ Ψ (w, q.2)) q.1)) q.1 :=
    by
    simpa only [Function.comp_def] using hHa'.comp q.1 hPa.hasFDerivAt
  have hc : HasFDerivAt (fun w ↦ H (Ψ (w, q.2))) (0 : W →L[ℝ] ℝ) q.1 := by
    apply (hasFDerivAt_const (𝕜 := ℝ) (F.chartEnergy x₀ z₀) q.1).congr_of_eventuallyEq
    filter_upwards [hB.mem_nhds hq.1] with w hw
    change localHamiltonian (F.chartEnergy x₀) ℓ (Ψ (w, q.2)) = _
    rw [hF.localHamiltonian_chartEnergy_eq x₀ hℓ hsub (hmap (x := (w, q.2)) ⟨hw, hq.2⟩)]
    exact (hF.chartHamiltonianFamily_energy_speed_eq x₀ hℓ hsub hℓi hI hconn
      hmap hODE ht₀ henergy (w, q.2) ⟨hw, hq.2⟩).1
  have hzero := congrArg (fun D : W →L[ℝ] ℝ ↦ D ξ) (hd.unique hc)
  have hLa := (hL.contDiffAt (ℓ.open_source.mem_nhds (ℓ.map_target (hmap hq))))
    |>.differentiableAt (by simp)
  have hGi := (hℓi.contDiffAt (ℓ.open_target.mem_nhds (hmap hq))).differentiableAt
    (by simp)
  change fderiv ℝ H (Ψ q) (fderiv ℝ (fun w ↦ Ψ (w, q.2)) q.1 ξ) = 0 at hzero
  rw [localHamiltonianVectorField_identity hℓ (hmap hq) hLa hGi] at hzero
  exact hzero

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
