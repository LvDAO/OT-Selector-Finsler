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

* **Conditions:** A smooth energy L : B × E → R on an arbitrary open domain. The actual vertical Hessian has positive diagonal pairing. The final nonlinear inverse theorem assumes finite-dimensional base and fiber.
* **Objects:** The vertical differential fiberLegendre L and the base-preserving map (b,v) ↦ (b,d_vL); its block derivative and a jointly smooth local inverse.
* **Proof detail:** Compute the derivative with identity base row and actual vertical-Hessian diagonal block. Solve the unrestricted mixed-block linear system, apply the inverse function theorem, and differentiate the true inverse identity.

## Mathematical sources

* Matias Dahl, *An brief introduction to Finsler geometry (12 July 2006)*, Section 1.2, Definition 1.8, Propositions 1.9–1.10, pp. 6–8; equations (3)–(8).
  https://math.aalto.fi/~fdahl/finsler/finsler.pdf#page=6
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55.
  https://www.jirka.org/ra/realanal2.pdf#page=55
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
  https://www.jirka.org/ra/realanal2.pdf#page=51

**Relationship to the sources:** The parametric, base-preserving coordinate construction combines the Legendre argument with the block form used in the implicit function theorem. It needs no homogeneity and is more general than a fixed Finsler fiber.
-/

/-!
# Joint local Legendre inverses for smooth coordinate energies

For an actual scalar energy `L : B × E → ℝ`, `fiberLegendre L` is its true vertical
Fréchet derivative and `parametricLegendre L` retains the base coordinate. Smoothness
of `L` implies joint smoothness of these maps. Their actual derivatives are computed:
the base row is the identity and the vertical block is exactly the fiber Hessian.

Positivity of that actual vertical Hessian makes the block derivative bijective; the
mixed block is unrestricted. The inverse function theorem constructs an actual local
inverse on an arbitrary open coordinate domain. Both directions are jointly smooth,
the inverse preserves the base coordinate, and its derivative is the inverse of the
actual joint derivative.

No nonlinear inverse, product-domain geometry, base-independent coefficient, inner
product, or homogeneity is assumed. The final theorem uses finite-dimensional base
and fiber spaces. Identifying a coordinate energy with a manifold Finsler structure
and constructing a Hamiltonian flow are separate subsequent steps.
-/

open Set Filter
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {B E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual vertical differential of a scalar energy in base-fiber coordinates. -/
noncomputable def fiberLegendre (L : B × E → ℝ) (z : B × E) : E →L[ℝ] ℝ :=
  fderiv ℝ (fun w ↦ L (z.1, w)) z.2

/-- The actual Legendre map retaining the base coordinate. -/
noncomputable def parametricLegendre (L : B × E → ℝ) (z : B × E) : B × (E →L[ℝ] ℝ) :=
  (z.1, fiberLegendre L z)

/-- Joint smoothness of the scalar energy gives joint smoothness of its vertical differential. -/
theorem contDiffAt_fiberLegendre {L : B × E → ℝ} {z : B × E}
    (hL : ContDiffAt ℝ ∞ L z) : ContDiffAt ℝ ∞ (fiberLegendre L) z := by
  have h : ContDiffAt ℝ ∞ (fun p : (B × E) × E ↦ L (p.1.1, p.2)) (z, z.2) :=
    hL.comp (z, z.2) (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact h.fderiv contDiffAt_snd (by simp)

/-- The base-preserving Legendre map is jointly smooth wherever the energy is smooth. -/
theorem contDiffAt_parametricLegendre {L : B × E → ℝ} {z : B × E}
    (hL : ContDiffAt ℝ ∞ L z) : ContDiffAt ℝ ∞ (parametricLegendre L) z :=
  contDiffAt_fst.prodMk (contDiffAt_fiberLegendre hL)

/-- The actual total derivative has identity base row and actual vertical-differential row. -/
theorem hasFDerivAt_parametricLegendre {L : B × E → ℝ} {z : B × E}
    (hL : ContDiffAt ℝ ∞ L z) :
    HasFDerivAt (parametricLegendre L)
      ((ContinuousLinearMap.fst ℝ B E).prod (fderiv ℝ (fiberLegendre L) z)) z :=
  hasFDerivAt_fst.prodMk ((contDiffAt_fiberLegendre hL).differentiableAt (by simp)).hasFDerivAt

/-- The vertical block of the actual total derivative is exactly the actual fiber Hessian. -/
theorem fiberLegendre_fderiv_vertical {L : B × E → ℝ} {z : B × E}
    (hL : ContDiffAt ℝ ∞ L z) :
    (fderiv ℝ (fiberLegendre L) z).comp (ContinuousLinearMap.inr ℝ B E) =
      fderiv ℝ (fderiv ℝ (fun w ↦ L (z.1, w))) z.2 := by
  have hd := ((contDiffAt_fiberLegendre hL).differentiableAt (by simp)).hasFDerivAt
  have hcomp := hd.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  exact hcomp.fderiv.symm

/-- A block map preserving its first coordinate is bijective if its vertical block is. -/
theorem base_preserving_block_bijective
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (K : (B × E) →L[ℝ] V) (h : E ≃L[ℝ] V)
    (hK : ∀ w, K (0, w) = h w) :
    Function.Bijective ((ContinuousLinearMap.fst ℝ B E).prod K) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨b, w⟩ hzero
    have hb : b = 0 := congrArg Prod.fst hzero
    have hw : K (b, w) = 0 := congrArg Prod.snd hzero
    subst b
    have hw0 : w = 0 := h.map_eq_zero_iff.mp ((hK w).symm.trans hw)
    simp [hw0]
  · rintro ⟨b, p⟩
    refine ⟨(b, h.symm (p - K (b, 0))), ?_⟩
    refine Prod.ext ?_ ?_
    · rfl
    change K (b, h.symm (p - K (b, 0))) = p
    calc
      K (b, h.symm (p - K (b, 0))) =
          K (b, 0) + K (0, h.symm (p - K (b, 0))) := by
        rw [← map_add]
        simp
      _ = p := by rw [hK, h.apply_symm_apply, add_comm, sub_add_cancel]


/-- The actual total Fréchet derivative is the lower triangular base-preserving block map. -/
theorem parametricLegendre_fderiv_eq {L : B × E → ℝ} {z : B × E}
    (hL : ContDiffAt ℝ ∞ L z) :
    fderiv ℝ (parametricLegendre L) z =
      (ContinuousLinearMap.fst ℝ B E).prod (fderiv ℝ (fiberLegendre L) z) :=
  (hasFDerivAt_parametricLegendre hL).fderiv

/-- The mixed block is the base derivative of the vertical differential, and the
vertical block is the actual fiber Hessian. -/
theorem parametricLegendre_fderiv_apply {L : B × E → ℝ} {z : B × E}
    (hL : ContDiffAt ℝ ∞ L z) (b : B) (w : E) :
    fderiv ℝ (parametricLegendre L) z (b, w) =
      (b, fderiv ℝ (fiberLegendre L) z (b, 0) +
        fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w) := by
  rw [parametricLegendre_fderiv_eq hL]
  apply Prod.ext
  · rfl
  · change fderiv ℝ (fiberLegendre L) z (b, w) = _
    have hsplit : (b, w) = (b, 0) + (0, w) := by simp
    rw [hsplit, map_add]
    congr 1
    exact congrArg (fun T : E →L[ℝ] (E →L[ℝ] ℝ) ↦ T w)
      (fiberLegendre_fderiv_vertical hL)

/-- Positive actual vertical Hessian makes the actual joint Legendre derivative bijective. -/
theorem parametricLegendre_fderiv_bijective [FiniteDimensional ℝ E]
    {L : B × E → ℝ} {z : B × E} (hL : ContDiffAt ℝ ∞ L z)
    (hpos : ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w) :
    Function.Bijective (fderiv ℝ (parametricLegendre L) z) := by
  rw [parametricLegendre_fderiv_eq hL]
  let H := fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2
  let d := positive_dualMap_equiv H hpos
  apply base_preserving_block_bijective _ d
  intro w
  exact congrArg (fun T : E →L[ℝ] (E →L[ℝ] ℝ) ↦ T w)
    (fiberLegendre_fderiv_vertical hL)

/-- A smooth scalar energy with positive vertical Hessian has a jointly smooth actual
local Legendre inverse on an arbitrary open coordinate domain. Its inverse preserves
base coordinates and has derivative the inverse of the actual joint derivative. -/
theorem exists_smooth_parametricLegendre_local_inverse
    [FiniteDimensional ℝ B] [FiniteDimensional ℝ E]
    {L : B × E → ℝ} {U : Set (B × E)} (hU : IsOpen U)
    (hL : ContDiffOn ℝ ∞ L U)
    (hpos : ∀ z ∈ U, ∀ w : E, w ≠ 0 →
      0 < fderiv ℝ (fderiv ℝ (fun u ↦ L (z.1, u))) z.2 w w)
    {z : B × E} (hz : z ∈ U) :
    ∃ e : OpenPartialHomeomorph (B × E) (B × (E →L[ℝ] ℝ)),
      (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L ∧
      z ∈ e.source ∧ parametricLegendre L z ∈ e.target ∧ e.source ⊆ U ∧
      ContDiffOn ℝ ∞ (parametricLegendre L) e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ p ∈ e.target, (e.symm p).1 = p.1) ∧
      ∀ p ∈ e.target, HasFDerivAt e.symm
        (ContinuousLinearMap.inverse (fderiv ℝ (parametricLegendre L) (e.symm p))) p := by
  have hLAt : ∀ x ∈ U, ContDiffAt ℝ ∞ L x := fun x hx ↦ hL.contDiffAt (hU.mem_nhds hx)
  have hgAt : ∀ x ∈ U, ContDiffAt ℝ ∞ (parametricLegendre L) x :=
    fun x hx ↦ contDiffAt_parametricLegendre (hLAt x hx)
  have hbij : ∀ x ∈ U, Function.Bijective (fderiv ℝ (parametricLegendre L) x) :=
    fun x hx ↦ parametricLegendre_fderiv_bijective (hLAt x hx) (hpos x hx)
  let d := (LinearEquiv.ofBijective (fderiv ℝ (parametricLegendre L) z).toLinearMap
    (hbij z hz)).toContinuousLinearEquiv
  have hd : HasFDerivAt (parametricLegendre L) d.toContinuousLinearMap z :=
    (hgAt z hz).differentiableAt (by simp) |>.hasFDerivAt
  let e₀ := (hgAt z hz).toOpenPartialHomeomorph (parametricLegendre L) hd (by simp)
  let e := e₀.restrOpen U hU
  have he : (e : (B × E) → (B × (E →L[ℝ] ℝ))) = parametricLegendre L := rfl
  have hzsource : z ∈ e.source :=
    ⟨(hgAt z hz).mem_toOpenPartialHomeomorph_source hd (by simp), hz⟩
  have hsource : e.source ⊆ U := inter_subset_right
  have htarget : parametricLegendre L z ∈ e.target := by
    rw [← he]
    exact e.map_source hzsource
  refine ⟨e, he, hzsource, htarget, hsource, ?_, ?_, ?_, ?_⟩
  · exact fun x hx ↦ (hgAt x (hsource hx)).contDiffWithinAt
  · apply e.open_target.contDiffOn_iff.mpr
    intro p hp
    have hx : e.symm p ∈ U := hsource (e.map_target hp)
    let dp := (LinearEquiv.ofBijective
      (fderiv ℝ (parametricLegendre L) (e.symm p)).toLinearMap
      (hbij (e.symm p) hx)).toContinuousLinearEquiv
    have hdp : HasFDerivAt e dp.toContinuousLinearMap (e.symm p) := by
      rw [he]
      exact (hgAt (e.symm p) hx).differentiableAt (by simp) |>.hasFDerivAt
    exact e.contDiffAt_symm hp hdp (by rw [he]; exact hgAt (e.symm p) hx)
  · intro p hp
    have h := congrArg Prod.fst (e.right_inv hp)
    change (parametricLegendre L (e.symm p)).1 = p.1 at h
    exact h
  · intro p hp
    have hx : e.symm p ∈ U := hsource (e.map_target hp)
    let dp := (LinearEquiv.ofBijective
      (fderiv ℝ (parametricLegendre L) (e.symm p)).toLinearMap
      (hbij (e.symm p) hx)).toContinuousLinearEquiv
    have hdp : HasFDerivAt e dp.toContinuousLinearMap (e.symm p) := by
      rw [he]
      exact (hgAt (e.symm p) hx).differentiableAt (by simp) |>.hasFDerivAt
    have hi : ContinuousLinearMap.inverse (fderiv ℝ (parametricLegendre L) (e.symm p)) =
        dp.symm.toContinuousLinearMap := ContinuousLinearMap.inverse_equiv dp
    rw [hi]
    exact e.hasFDerivAt_symm hp hdp

end OTSelector.Geometry
