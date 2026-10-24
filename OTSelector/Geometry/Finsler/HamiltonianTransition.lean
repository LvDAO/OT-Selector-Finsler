import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeCovariance
import OTSelector.Geometry.Finsler.Jacobi.Pairing
import OTSelector.Geometry.Finsler.LegendreInjectivity
import OTSelector.Geometry.Symplectic.CotangentChartPairing
import OTSelector.Geometry.Symplectic.CotangentFamilyTransition
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerHamiltonianTransition.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerHamiltonianTransition`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.HamiltonianTransition

* **Conditions:** Two actual manifold charts and genuine Legendre branches on the explicit overlap; vector-field covariance uses the stated finite dimension.
* **Objects:** Compatibility of inverse Legendre branches, Hamiltonians, actual vector fields and integral-curve families under the genuine cotangent lift.
* **Proof detail:** Use nonlinear Legendre injectivity to match inverses, transform original energy, and differentiate the Hamiltonian identity using preservation/nondegeneracy of canonical pairing.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=253): Section 8.4, pp. 242–243, equations (8.53)–(8.58): canonical coordinate changes and preservation of the symplectic two-form.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).

Source relation (derived): Cotangent covariance and inverse compatibility are proved from actual chart maps rather than assumed as flow properties.
-/

/-!
# Actual Finsler Hamiltonian dynamics across charts

The actual nonlinear Legendre map is injective on each slit chart domain. Consequently
the cotangent chart change identifies any two genuine local inverse branches wherever
their targets overlap. The original energy then identifies the two Hamiltonians.
Differentiating this identity and using the canonical pairing proves covariance of the
actual vector fields, hence of their integral curves. No field covariance or inverse
compatibility is assumed.
-/

open Set Filter Function Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

private theorem phase_eq_of_pairing_eq {u v : E × (E →L[ℝ] ℝ)}
    (h : ∀ w, canonicalPhasePairing u w = canonicalPhasePairing v w) : u = v := by
  have hx : u.1 - v.1 = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero
      (R := ℝ) fun p ↦ by
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa [canonicalPhasePairing] using h (0, p))
  have hp : u.2 = v.2 := by
    ext x
    simpa [canonicalPhasePairing] using h (x, 0)
  exact Prod.ext (sub_eq_zero.mp hx) hp

/-- Actual Legendre inverses in overlapping charts represent the same tangent vector.
Nonlinear injectivity removes any need to prescribe compatibility of inverse branches. -/
theorem chartLegendre_inverse_cotangentLift (hF : F.IsSmoothStronglyConvex) (old new : M)
    {e g : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy new))
    (hg : (g : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hes : e.source ⊆ chartEnergyDomain new) (hgs : g.source ⊆ chartEnergyDomain old)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hx : p.1 ∈ chartTransitionDomain old new)
    (ht : cotangentLift (chartTransition old new) (chartTransition new old) p ∈ g.target) :
    g.symm (cotangentLift (chartTransition old new) (chartTransition new old) p) =
      tangentLift (chartTransition old new) (e.symm p) := by
  have hz := hes (e.map_target hp)
  have hb := (parametricLegendre_inverse_components he hp).1
  have hx' : (e.symm p).1 ∈ chartTransitionDomain old new := hb ▸ hx
  have hd := mapsTo_chartTransition_energyDomain old new ⟨hx', hz.2⟩
  apply hF.injOn_parametricLegendre_chartEnergy old (hgs (g.map_target ht)) hd
  have heq : parametricLegendre (F.chartEnergy new) (e.symm p) = p := by
    rw [← he]
    exact e.right_inv hp
  have hcov := hF.chartLegendre_cotangentLift old new hx' hz.2
  change cotangentLift (chartTransition old new) (chartTransition new old)
      (parametricLegendre (F.chartEnergy new) (e.symm p)) =
    parametricLegendre (F.chartEnergy old) (tangentLift (chartTransition old new) (e.symm p))
      at hcov
  rw [heq] at hcov
  have hginv : parametricLegendre (F.chartEnergy old)
      (g.symm (cotangentLift (chartTransition old new) (chartTransition new old) p)) =
        cotangentLift (chartTransition old new) (chartTransition new old) p := by
    rw [← hg]
    exact g.right_inv ht
  exact hginv.trans hcov

/-- The actual local Hamiltonian is unchanged by the genuine cotangent chart change. -/
theorem chartHamiltonian_cotangentLift (hF : F.IsSmoothStronglyConvex) (old new : M)
    {e g : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy new))
    (hg : (g : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hes : e.source ⊆ chartEnergyDomain new) (hgs : g.source ⊆ chartEnergyDomain old)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hx : p.1 ∈ chartTransitionDomain old new)
    (ht : cotangentLift (chartTransition old new) (chartTransition new old) p ∈ g.target) :
    localHamiltonian (F.chartEnergy old) g
      (cotangentLift (chartTransition old new) (chartTransition new old) p) =
        localHamiltonian (F.chartEnergy new) e p := by
  rw [hF.localHamiltonian_chartEnergy_eq old hg hgs ht,
    hF.localHamiltonian_chartEnergy_eq new he hes hp,
    hF.chartLegendre_inverse_cotangentLift old new he hg hes hgs hp hx ht]
  have hx' : (e.symm p).1 ∈ chartTransitionDomain old new := by
    rw [(parametricLegendre_inverse_components he hp).1]
    exact hx
  exact (F.chartEnergy_chartTransition old new hx' (e.symm p).2).symm

/-- The derivative of the actual cotangent change carries the original Hamiltonian
field to its expression in the other chart. All compatibility is derived from Finsler data. -/
theorem chartHamiltonianVectorField_cotangentLift [FiniteDimensional ℝ E]
    (hF : F.IsSmoothStronglyConvex) (old new : M)
    {e g : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy new))
    (hg : (g : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hes : e.source ⊆ chartEnergyDomain new) (hgs : g.source ⊆ chartEnergyDomain old)
    (heG : ContDiffOn ℝ ∞ e.symm e.target) (hgG : ContDiffOn ℝ ∞ g.symm g.target)
    {p : E × (E →L[ℝ] ℝ)} (hp : p ∈ e.target)
    (hx : p.1 ∈ chartTransitionDomain old new)
    (ht : cotangentLift (chartTransition old new) (chartTransition new old) p ∈ g.target) :
    let T := cotangentLift (chartTransition old new) (chartTransition new old)
    fderiv ℝ T p (localHamiltonianVectorField (F.chartEnergy new) e p) =
      localHamiltonianVectorField (F.chartEnergy old) g (T p) := by
  let T := cotangentLift (chartTransition (E := E) old new) (chartTransition new old)
  have hT : DifferentiableAt ℝ T p :=
    ((contDiffOn_chartCotangentLift old new).contDiffAt
      (((isOpen_chartTransitionDomain old new).prod isOpen_univ).mem_nhds
        ⟨hx, mem_univ _⟩)).differentiableAt (by simp)
  have hLe := (hF.contDiffOn_chartEnergy new).mono hes
  have hLg := (hF.contDiffOn_chartEnergy old).mono hgs
  have hHg := ((contDiffOn_localHamiltonian hLg hgG).contDiffAt
    (g.open_target.mem_nhds ht)).differentiableAt (by simp)
  have heq : localHamiltonian (F.chartEnergy old) g ∘ T =ᶠ[𝓝 p]
      localHamiltonian (F.chartEnergy new) e := by
    filter_upwards [e.open_target.mem_nhds hp,
      continuous_fst.continuousAt.eventually
        ((isOpen_chartTransitionDomain old new).mem_nhds hx),
      hT.continuousAt.eventually (g.open_target.mem_nhds ht)] with q hqe hqx hqg
    exact hF.chartHamiltonian_cotangentLift old new he hg hes hgs hqe hqx hqg
  have hchain : (fderiv ℝ (localHamiltonian (F.chartEnergy old) g) (T p)).comp
      (fderiv ℝ T p) = fderiv ℝ (localHamiltonian (F.chartEnergy new) e) p :=
    (hHg.hasFDerivAt.comp p hT.hasFDerivAt).fderiv.symm.trans heq.fderiv_eq
  have hpair := chartCotangentLift_fderiv_pairing old new (z := p) hx
  have hinj := injective_of_canonicalPhasePairing_preserved (fderiv ℝ T p) hpair
  have hsurj : Surjective (fderiv ℝ T p) :=
    LinearMap.injective_iff_surjective.mp hinj
  have hde := (hLe.contDiffAt (e.open_source.mem_nhds (e.map_target hp))).differentiableAt
    (by simp)
  have hdg := (hLg.contDiffAt (g.open_source.mem_nhds (g.map_target ht))).differentiableAt
    (by simp)
  have hie := (heG.contDiffAt (e.open_target.mem_nhds hp)).differentiableAt (by simp)
  have hig := (hgG.contDiffAt (g.open_target.mem_nhds ht)).differentiableAt (by simp)
  apply phase_eq_of_pairing_eq
  intro v
  obtain ⟨u, rfl⟩ := hsurj v
  calc
    canonicalPhasePairing
        (fderiv ℝ T p (localHamiltonianVectorField (F.chartEnergy new) e p))
        (fderiv ℝ T p u) =
      canonicalPhasePairing (localHamiltonianVectorField (F.chartEnergy new) e p) u :=
        hpair _ _
    _ = fderiv ℝ (localHamiltonian (F.chartEnergy new) e) p u :=
      (localHamiltonianVectorField_identity he hp hde hie u).symm
    _ = fderiv ℝ (localHamiltonian (F.chartEnergy old) g) (T p) (fderiv ℝ T p u) :=
      (congrArg (fun A : (E × (E →L[ℝ] ℝ)) →L[ℝ] ℝ ↦ A u) hchain).symm
    _ = canonicalPhasePairing (localHamiltonianVectorField (F.chartEnergy old) g (T p))
        (fderiv ℝ T p u) := localHamiltonianVectorField_identity hg ht hdg hig _

/-- A true Hamiltonian solution still solves the original dynamics after changing chart. -/
theorem hasDerivAt_chartHamiltonian_cotangentLift [FiniteDimensional ℝ E]
    (hF : F.IsSmoothStronglyConvex) (old new : M)
    {e g : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy new))
    (hg : (g : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hes : e.source ⊆ chartEnergyDomain new) (hgs : g.source ⊆ chartEnergyDomain old)
    (heG : ContDiffOn ℝ ∞ e.symm e.target) (hgG : ContDiffOn ℝ ∞ g.symm g.target)
    {γ : ℝ → E × (E →L[ℝ] ℝ)} {t : ℝ} (hp : γ t ∈ e.target)
    (hx : (γ t).1 ∈ chartTransitionDomain old new)
    (ht : cotangentLift (chartTransition old new) (chartTransition new old) (γ t) ∈ g.target)
    (hγ : HasDerivAt γ (localHamiltonianVectorField (F.chartEnergy new) e (γ t)) t) :
    let T := cotangentLift (chartTransition old new) (chartTransition new old)
    HasDerivAt (T ∘ γ) (localHamiltonianVectorField (F.chartEnergy old) g (T (γ t))) t := by
  have hT := ((contDiffOn_chartCotangentLift old new).contDiffAt
    (((isOpen_chartTransitionDomain old new).prod isOpen_univ).mem_nhds
      ⟨hx, mem_univ (γ t).2⟩)).differentiableAt (by simp)
  have h := hT.hasFDerivAt.comp_hasDerivAt t hγ
  rw [hF.chartHamiltonianVectorField_cotangentLift old new he hg hes hgs heG hgG hp hx ht]
    at h
  exact h

/-- The same C2 family, after actual cotangent recharting, satisfies the genuine
Hamiltonian equation for every parameter. Target overlap is only a coordinate domain. -/
theorem chartHamiltonianFamily_cotangentLift [FiniteDimensional ℝ E]
    (hF : F.IsSmoothStronglyConvex) (old new : M)
    {e g : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy new))
    (hg : (g : (E × E) → (E × (E →L[ℝ] ℝ))) = parametricLegendre (F.chartEnergy old))
    (hes : e.source ⊆ chartEnergyDomain new) (hgs : g.source ⊆ chartEnergyDomain old)
    (heG : ContDiffOn ℝ ∞ e.symm e.target) (hgG : ContDiffOn ℝ ∞ g.symm g.target)
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {Ψ : W × ℝ → E × (E →L[ℝ] ℝ)} {D : Set (W × ℝ)}
    (hΨ : ContDiffOn ℝ 2 Ψ D) (hp : MapsTo Ψ D e.target)
    (hx : ∀ q ∈ D, (Ψ q).1 ∈ chartTransitionDomain old new)
    (ht : ∀ q ∈ D,
      cotangentLift (chartTransition old new) (chartTransition new old) (Ψ q) ∈ g.target)
    (hODE : ∀ q ∈ D, HasDerivAt (fun s ↦ Ψ (q.1, s))
      (localHamiltonianVectorField (F.chartEnergy new) e (Ψ q)) q.2) :
    let Γ := cotangentLift (chartTransition old new) (chartTransition new old) ∘ Ψ
    ContDiffOn ℝ 2 Γ D ∧ ∀ q ∈ D, HasDerivAt (fun s ↦ Γ (q.1, s))
      (localHamiltonianVectorField (F.chartEnergy old) g (Γ q)) q.2 := by
  refine ⟨contDiffOn_rechartedPhase old new hΨ hx, ?_⟩
  intro q hq
  simpa only [Function.comp_def, Prod.eta] using
    hF.hasDerivAt_chartHamiltonian_cotangentLift old new he hg hes hgs heG hgG
      (γ := fun t ↦ Ψ (q.1, t)) (hp hq) (hx q hq) (ht q hq) (hODE q hq)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
