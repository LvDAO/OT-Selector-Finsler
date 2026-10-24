import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OTSelector.Analysis.Convex.HomogeneousEnergy

/-!
## Lemma skeleton

* **Conditions:** A smooth scalar energy on the slit of a finite-dimensional real normed fiber, with positive actual Hessian. Positive degree-two homogeneity is needed only for the nonzero-covector and slit-target conclusions.
* **Objects:** An open partial homeomorphism whose forward map is the actual derivative DL; smooth inverse and inverse-Hessian derivative on its target.
* **Proof detail:** Turn the actual positive Hessian into an invertible derivative, apply the inverse function theorem, restrict the source to the slit, and use the inverse identity throughout the open target. Euler homogeneity excludes zero momentum.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
  https://www.jirka.org/ra/realanal2.pdf#page=51

**Relationship to the sources:** This is a local scalar-energy version of the smooth Legendre inverse argument. Dahl proves a global inverse for a Minkowski norm; the Lean theorem uses local hypotheses and does not assert that global conclusion.
-/

/-!
# Smooth local inverses for the actual Legendre map

A smooth scalar energy on the slit fiber has a smooth actual derivative map. Positive
diagonal pairing of its actual Hessian makes the derivative invertible by
`HomogeneousEnergy`; the inverse function theorem then constructs a genuine open
partial homeomorphism whose forward map is `fderiv ℝ L`. Restricting its source to
the slit and applying the smooth inverse theorem at every target point gives a smooth
inverse throughout the target, with derivative equal to the inverse actual Hessian.

For positive degree-two homogeneous energies, the radial Hessian identity additionally
proves that nonzero vectors map to nonzero covectors. The final theorem therefore gives
a local smooth inverse between open subsets of the slit fiber and slit continuous dual.

No inner-product identification of the dual and no nonlinear inverse are assumed.
Finite-dimensionality supplies completeness and invertibility of the positive Hessian.
The conclusions are local in a fixed fiber; no global Legendre inverse, dependence on
manifold base coordinates, or geodesic flow is asserted.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A smooth energy on the slit with positive actual Hessian has a genuine smooth local
Legendre inverse. Both the forward map and every inverse derivative are identified. -/
theorem exists_smooth_legendre_local_inverse [FiniteDimensional ℝ E]
    {L : E → ℝ}
    (hL : ContDiffOn ℝ ∞ L {v : E | v ≠ 0})
    (hpos : ∀ v : E, v ≠ 0 → ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ L) v w w)
    {v : E} (hv : v ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (E →L[ℝ] ℝ),
      (e : E → (E →L[ℝ] ℝ)) = fderiv ℝ L ∧
      v ∈ e.source ∧ fderiv ℝ L v ∈ e.target ∧
      e.source ⊆ {x : E | x ≠ 0} ∧
      ContDiffOn ℝ ∞ (fderiv ℝ L) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ p ∈ e.target, HasFDerivAt e.symm
        (ContinuousLinearMap.inverse (fderiv ℝ (fderiv ℝ L) (e.symm p))) p := by
  have hs : IsOpen {x : E | x ≠ 0} := isOpen_ne
  have hg : ContDiffOn ℝ ∞ (fderiv ℝ L) {x : E | x ≠ 0} :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hL).2
  have hgAt := hg.contDiffAt (hs.mem_nhds hv)
  let d := positive_dualMap_equiv (fderiv ℝ (fderiv ℝ L) v) (hpos v hv)
  have hd : HasFDerivAt (fderiv ℝ L) d.toContinuousLinearMap v :=
    hgAt.differentiableAt (by simp) |>.hasFDerivAt
  let e₀ := hgAt.toOpenPartialHomeomorph (fderiv ℝ L) hd (by simp)
  let e := e₀.restrOpen {x : E | x ≠ 0} hs
  have he : (e : E → (E →L[ℝ] ℝ)) = fderiv ℝ L := rfl
  have hvsource : v ∈ e.source :=
    ⟨hgAt.mem_toOpenPartialHomeomorph_source hd (by simp), hv⟩
  have hsource : e.source ⊆ {x : E | x ≠ 0} := inter_subset_right
  have htarget : fderiv ℝ L v ∈ e.target := by
    rw [← he]
    exact e.map_source hvsource
  refine ⟨e, he, hvsource, htarget, hsource, hg.mono hsource, ?_, ?_⟩
  · apply e.open_target.contDiffOn_iff.mpr
    intro p hp
    have hne : e.symm p ≠ 0 := hsource (e.map_target hp)
    have hgp := hg.contDiffAt (hs.mem_nhds hne)
    let dp := positive_dualMap_equiv (fderiv ℝ (fderiv ℝ L) (e.symm p))
      (hpos (e.symm p) hne)
    have hdp : HasFDerivAt e dp.toContinuousLinearMap (e.symm p) := by
      rw [he]
      exact hgp.differentiableAt (by simp) |>.hasFDerivAt
    exact e.contDiffAt_symm hp hdp (by rw [he]; exact hgp)
  · intro p hp
    have hne : e.symm p ≠ 0 := hsource (e.map_target hp)
    have hgp := hg.contDiffAt (hs.mem_nhds hne)
    let dp := positive_dualMap_equiv (fderiv ℝ (fderiv ℝ L) (e.symm p))
      (hpos (e.symm p) hne)
    have hdp : HasFDerivAt e dp.toContinuousLinearMap (e.symm p) := by
      rw [he]
      exact hgp.differentiableAt (by simp) |>.hasFDerivAt
    have hi : ContinuousLinearMap.inverse (fderiv ℝ (fderiv ℝ L) (e.symm p)) =
        dp.symm.toContinuousLinearMap := ContinuousLinearMap.inverse_equiv dp
    rw [hi]
    exact e.hasFDerivAt_symm hp hdp

/-- For a smooth degree-two energy with positive Hessian, the actual Legendre map
sends each nonzero fiber vector to a nonzero continuous covector. -/
theorem twoHomogeneous_legendre_ne_zero
    {L : E → ℝ}
    (hL : ContDiffOn ℝ ∞ L {v : E | v ≠ 0})
    (hhom : ∀ r : ℝ, 0 < r → ∀ x : E, L (r • x) = r ^ 2 * L x)
    {v : E} (hv : v ≠ 0)
    (hpos : ∀ w : E, w ≠ 0 → 0 < fderiv ℝ (fderiv ℝ L) v w w) :
    fderiv ℝ L v ≠ 0 := by
  have hs : IsOpen {x : E | x ≠ 0} := isOpen_ne
  have hd : ∀ x : E, x ≠ 0 → DifferentiableAt ℝ L x :=
    fun x hx ↦ (hL.contDiffAt (hs.mem_nhds hx)).differentiableAt (by simp)
  have hg : ContDiffOn ℝ ∞ (fderiv ℝ L) {x : E | x ≠ 0} :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hs).mp hL).2
  have h2 := (hg.contDiffAt (hs.mem_nhds hv)).differentiableAt (by simp)
  have hr := twoHomogeneous_fderiv2_radial hhom hd hv h2
  intro hzero
  have hp := hpos v hv
  rw [hr, hzero] at hp
  simp at hp

/-- The genuine local Legendre inverse of a smooth strongly convex degree-two energy
is a smooth inverse between open subsets of the slit fiber and the slit continuous dual. -/
theorem exists_smooth_legendre_local_inverse_slit [FiniteDimensional ℝ E]
    {L : E → ℝ}
    (hL : ContDiffOn ℝ ∞ L {v : E | v ≠ 0})
    (hhom : ∀ r : ℝ, 0 < r → ∀ x : E, L (r • x) = r ^ 2 * L x)
    (hpos : ∀ v : E, v ≠ 0 → ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ L) v w w)
    {v : E} (hv : v ≠ 0) :
    ∃ e : OpenPartialHomeomorph E (E →L[ℝ] ℝ),
      (e : E → (E →L[ℝ] ℝ)) = fderiv ℝ L ∧
      v ∈ e.source ∧ fderiv ℝ L v ∈ e.target ∧
      e.source ⊆ {x : E | x ≠ 0} ∧
      e.target ⊆ {p : E →L[ℝ] ℝ | p ≠ 0} ∧
      ContDiffOn ℝ ∞ (fderiv ℝ L) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ p ∈ e.target, HasFDerivAt e.symm
        (ContinuousLinearMap.inverse (fderiv ℝ (fderiv ℝ L) (e.symm p))) p := by
  obtain ⟨e, he, hvsource, htarget, hsource, hforward, hinverse, hderiv⟩ :=
    exists_smooth_legendre_local_inverse hL hpos hv
  refine ⟨e, he, hvsource, htarget, hsource, ?_, hforward, hinverse, hderiv⟩
  intro p hp
  have hne : e.symm p ≠ 0 := hsource (e.map_target hp)
  have hcov := twoHomogeneous_legendre_ne_zero hL hhom hne (hpos (e.symm p) hne)
  rwa [← he, e.right_inv hp] at hcov

end OTSelector.Geometry
