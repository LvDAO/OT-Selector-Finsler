import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
import OTSelector.Geometry.Finsler.AdaptedGraphMomentum
import OTSelector.Geometry.Finsler.AdaptedPhaseDerivative
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.HamiltonianFamilyConservation
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.RegraphedPhaseDerivative
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Symplectic.LinearCotangentPhase
import OTSelector.Geometry.Symplectic.RegraphedPairingAlgebra
import OTSelector.Geometry.Symplectic.RegraphedRank

/-!
# Geometry.Finsler.AdaptedGraphStructure

* **Conditions:** Original common initial energy, actual phase rank/isotropy and normality, with the same adapted graph inverse.
* **Objects:** Injectivity and canonical isotropy of the true adapted graph parameter derivative.
* **Proof detail:** Use energy-tangent orthogonality and the computed time correction to transfer rank/pairing through the same coordinates.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAdaptedGraphStructure.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAdaptedGraphStructure`; the selected original proof blocks follow. -/
section

/-!
# Rank and canonical pairing in adapted graph coordinates

Common original initial energy gives constant old speed and energy-tangent variations.
The true phase chain rule then transfers original normal injectivity and zero pairing
to the actual graph parameter derivative, through the same graph inverse.
-/

open Set Filter Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} (hF : F.IsSmoothStronglyConvex)
include hF

/-- Original normal phase injectivity and zero pairing transfer to the true graph
parameter derivative. Speed constancy and energy tangency are derived internally. -/
theorem adaptedGraphPhase_rank_pairing (x₀ : M) (T : E ≃L[ℝ] (ℝ × V))
    {ℓ : OpenPartialHomeomorph (E × E)
      (E × (E →L[ℝ] ℝ))}
    (hℓ : (ℓ : (E × E) → (E × (E →L[ℝ] ℝ))) =
      parametricLegendre (F.chartEnergy x₀))
    (hsub : ℓ.source ⊆ chartEnergyDomain x₀) (hℓi : ContDiffOn ℝ ∞ ℓ.symm ℓ.target)
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {B : Set W} {I : Set ℝ}
    (hB : IsOpen B) (hI : IsOpen I) (hconn : IsPreconnected I)
    (hΨ : ContDiffOn ℝ 2 Ψ (B ×ˢ I)) (hmap : MapsTo Ψ (B ×ˢ I) ℓ.target)
    (hODE : ∀ w ∈ B, ∀ t ∈ I, HasDerivAt (fun s ↦ Ψ (w, s))
      (localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ (w, t))) t)
    {t₀ : ℝ} (ht₀ : t₀ ∈ I) {z₀ : E × E}
    (henergy : ∀ w ∈ B, F.chartEnergy x₀ (ℓ.symm (Ψ (w, t₀))) = F.chartEnergy x₀ z₀)
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ T (Ψ z).1))
    (hesub : e.source ⊆ B ×ˢ I) {Q : Set (W × ℝ)} (hQ : IsOpen Q) (hQt : Q ⊆ e.target)
    (hi : DifferentiableOn ℝ e.symm Q)
    (hpos : ∀ p ∈ Q, 0 < (fderiv ℝ (fun z ↦ T (Ψ z).1) (e.symm p) (0, 1)).1)
    {q : W × ℝ} (hq : q ∈ Q)
    (hinj : Function.Injective
      (fderiv ℝ (fun w ↦ Ψ (w, (e.symm q).2)) (e.symm q).1))
    (hpair : ∀ u v : W, canonicalPhasePairing
      (fderiv ℝ (fun w ↦ Ψ (w, (e.symm q).2)) (e.symm q).1 u)
      (fderiv ℝ (fun w ↦ Ψ (w, (e.symm q).2)) (e.symm q).1 v) = 0)
    (hnormal : ∀ u : W, (Ψ (e.symm q)).2
      (fderiv ℝ (fun w ↦ Ψ (w, (e.symm q).2)) (e.symm q).1 u).1 = 0) :
    let P := F.adaptedGraphPhase x₀ T (fun z ↦ T (Ψ z).1) e
    let R := fderiv ℝ (fun w ↦ P (w, q.2)) q.1
    Function.Injective R ∧ ∀ u v : W, canonicalPhasePairing (R u) (R v) = 0 := by
  let K := linearCotangentPhase T
  let Φ := K ∘ Ψ
  let z := e.symm q
  let Y := localHamiltonianVectorField (F.chartEnergy x₀) ℓ (Ψ z)
  let X := K Y
  let A₀ := fderiv ℝ (fun w ↦ Ψ (w, z.2)) z.1
  let A := fderiv ℝ (fun w ↦ Φ (w, z.2)) z.1
  let S : ℝ := F.chartLength x₀ z₀
  let γ := fun z ↦ T (Ψ z).1
  let P := F.adaptedGraphPhase x₀ T γ e
  let R := fderiv ℝ (fun w ↦ P (w, q.2)) q.1
  have hz : z ∈ B ×ˢ I := hesub (e.map_target (hQt hq))
  have ha₀ : DifferentiableAt ℝ Ψ z :=
    (hΨ.contDiffAt ((hB.prod hI).mem_nhds hz)).differentiableAt (by norm_num)
  have ha : DifferentiableAt ℝ Φ z := K.differentiableAt.comp z ha₀
  have hA (u : W) : A u = K (A₀ u) := by
    have hp : DifferentiableAt ℝ (fun w ↦ Ψ (w, z.2)) z.1 :=
      ha₀.comp z.1 (differentiableAt_id.prodMk (differentiableAt_const z.2))
    exact congrArg (fun D ↦ D u) (K.hasFDerivAt.comp z.1 hp.hasFDerivAt).fderiv
  have htime : fderiv ℝ Φ z (0, 1) = X := by
    have hd := ha.hasFDerivAt.comp_hasDerivAt z.2
      ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
    exact hd.unique (K.hasFDerivAt.comp_hasDerivAt z.2 (hODE z.1 hz.1 z.2 hz.2))
  have hfst (u : W × ℝ) : fderiv ℝ γ z u = (fderiv ℝ Φ z u).1 := by
    exact congrArg (fun D ↦ D u) ha.hasFDerivAt.fst.fderiv
  have hfstΦ (u : W × ℝ) :
      fderiv ℝ (fun z ↦ (Φ z).1) z u = (fderiv ℝ Φ z u).1 := by
    exact congrArg (fun D ↦ D u) ha.hasFDerivAt.fst.fderiv
  have hparam (u : W) : fderiv ℝ Φ z (u, 0) = A u :=
    (parameterVariation_eq_fderiv ha u).symm
  have hc : X.1.1 ≠ 0 := by
    have h := (hpos q hq).ne'
    rwa [hfst, htime] at h
  have hs (p : W × ℝ) (hp : p ∈ B ×ˢ I) :
      (F.chartLength x₀ (ℓ.symm (Ψ p)) : ℝ) = S :=
    congrArg (fun a : ℝ≥0 ↦ (a : ℝ))
      (hF.chartHamiltonianFamily_energy_speed_eq x₀ hℓ hsub hℓi hI hconn
        hmap hODE ht₀ henergy p hp).2
  have hP := hF.adaptedGraphPhase_differential_on_of_constant_speed x₀ T hℓ hsub
    (hB.prod hI) (hΨ.differentiableOn (by norm_num)) hmap
    (fun p hp ↦ hODE p.1 hp.1 p.2 hp.2) he hesub hQ hQt hi hpos hs hq
  have heΦ : (e : W × ℝ → W × ℝ) =
      curveGraphCoordinateMap (fun z ↦ (Φ z).1) := he
  have hR (u : W) : R u = RegraphedPairing.reducedPhase X S (A u) := by
    change fderiv ℝ (fun w ↦ P (w, q.2)) q.1 u = _
    rw [parameterVariation_eq_fderiv hP.1 u, hP.2 u,
      regraphedPhase_parameter_fderiv heΦ (hQt hq) ha
        ((hi q hq).differentiableAt (hQ.mem_nhds hq)) (hpos q hq).ne' u,
      hfstΦ, hfstΦ, htime, hparam]
    rfl
  have hE (u : W) : canonicalPhasePairing X (A u) = 0 := by
    rw [hA, linearCotangentPhase_pairing]
    exact hF.chartHamiltonianFamily_parameter_pairing_zero x₀ hℓ hsub hℓi
      hB hI hconn hΨ hmap hODE ht₀ henergy hz u
  have hslit := hsub (ℓ.map_target (hmap hz))
  have hS : S ≠ 0 := by
    rw [← hs z hz]
    exact (NNReal.coe_pos.mpr (F.chartLength_pos x₀ hslit)).ne'
  have hpv₀ : (Ψ z).2 Y.1 ≠ 0 := by
    have h := hF.chartLegendre_self_eq_chartLength_sq x₀ hslit
    rw [(parametricLegendre_inverse_components hℓ (hmap hz)).2] at h
    change (Ψ z).2 (ℓ.symm (Ψ z)).2 ≠ 0
    rw [h, hs z hz]
    exact pow_ne_zero _ hS
  have hpv : ((Ψ z).2.comp T.symm.toContinuousLinearMap) X.1 ≠ 0 := by
    simpa only [X, K, linearCotangentPhase_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using hpv₀
  have hn (u : W) : ((Ψ z).2.comp T.symm.toContinuousLinearMap) (A u).1 = 0 := by
    rw [hA]
    simpa only [K, linearCotangentPhase_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using hnormal u
  have hinjA : Function.Injective A := by
    intro u v huv
    apply hinj
    exact K.injective (by simpa only [hA] using huv)
  refine ⟨?_, ?_⟩
  · apply injective_regraphed_phase_derivative hinjA hc hS hpv hn hE
    intro u
    exact hR u
  · intro u v
    change canonicalPhasePairing (R u) (R v) = 0
    rw [hR u, hR v, RegraphedPairing.reducedPhase_pairing X (A u) (A v) S hc
      (hE u) (hE v), hA, hA, linearCotangentPhase_pairing, hpair u v, mul_zero]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
