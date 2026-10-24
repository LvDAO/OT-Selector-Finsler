import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Geometry.Manifold.RegularLevelChart

## Lemma skeleton

* **Conditions:** A finite-dimensional real normed space and a C^n scalar function on an open set, n≥1, with nonzero actual derivative at the center.

* **Objects:** A regular level coordinate homeomorphism and a local level chart modeled on the derivative kernel, retaining the supplied regularity.

* **Proof detail:** Complement the nonzero scalar derivative’s kernel by one vector, apply the inverse-function theorem to value-plus-kernel coordinates, and slice its inverse at the original scalar value. Compute the center derivative from the inverse identity and use rank-nullity.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf#page=55): Section 8.5.1, Theorem 8.5.6 (Implicit function theorem), pp. 55–56.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=38): Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity).
- [Stephen Boyd; Lieven Vandenberghe, Convex Optimization (2004)](https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=662): Appendix A.5.1, pp. 645–646 (range/nullspace/rank); A.5.2, p. 647 (positive square root); A.5.4, pp. 648–649 (SVD and the nonzero spectra of A^T A and A A^T).

Source relation (generalization): Formal finite-dimensional C^n level-coordinate version, including arbitrary supported differentiability orders; the cited C1 local inverse/implicit principles are the foundation, while the exact kernel model and regularity packaging are provided by the Lean construction.
-/

/-!
# Regular level coordinates at every differentiable regularity order

The actual scalar function is the first coordinate of a genuine local coordinate
map. A nonzero derivative supplies its complemented kernel as the remaining model
space. Both directions retain the given regularity order, including C1. Slicing
the inverse at the original function value gives the exact regular level set and
its actual kernel-inclusion derivative at the center.
-/

open Set Filter
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A regular scalar function is the exact first coordinate of a local coordinate
map with both directions of the same regularity, including C1. The inverse section
at its center has the actual kernel inclusion as derivative. -/
theorem exists_contDiff_levelCoordinates {n : ℕ∞ω} (hn : 1 ≤ n)
    {f : E → ℝ} {Ω : Set E} {a : E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ n f Ω) (ha : a ∈ Ω)
    (hp : fderiv ℝ f a ≠ 0) :
    let p := fderiv ℝ f a
    ∃ e : OpenPartialHomeomorph E (ℝ × p.ker),
      a ∈ e.source ∧ e.source ⊆ Ω ∧ ContDiffOn ℝ n e e.source ∧
      ContDiffOn ℝ n e.symm e.target ∧ e a = (f a, 0) ∧
      (∀ x : E, (e x).1 = f x) ∧
      HasFDerivAt (fun w : p.ker ↦ e.symm (f a, w)) p.ker.subtypeL 0 ∧
      Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E := by
  have hn0 : n ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hn)
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  let p := fderiv ℝ f a
  have hpn : p.toLinearMap ≠ 0 := by
    intro h
    apply hp
    exact ContinuousLinearMap.coe_injective h
  have hsurj : p.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hpn
  have hker : p.ker.ClosedComplemented :=
    p.ker_closedComplemented_of_finiteDimensional_range
  have hfa : ContDiffAt ℝ n f a := hf.contDiffAt (hΩ.mem_nhds ha)
  have hs : HasStrictFDerivAt f p a := hfa.hasStrictFDerivAt hn0
  let φ := hs.implicitFunctionDataOfComplemented f p hsurj hker
  let e₀ := φ.toOpenPartialHomeomorph
  have hprod : ContDiffOn ℝ n φ.prodFun Ω := by
    exact hf.prodMk (((Classical.choose hker).contDiff.comp
      (contDiff_id.sub contDiff_const)).contDiffOn)
  let T := φ.leftDeriv.equivProdOfSurjectiveOfIsCompl φ.rightDeriv
    φ.range_leftDeriv φ.range_rightDeriv φ.isCompl_ker
  have hTa : fderiv ℝ φ.prodFun a = T := φ.hasStrictFDerivAt.hasFDerivAt.fderiv
  let V := Ω ∩ (fderiv ℝ φ.prodFun) ⁻¹'
    range ((↑) : (E ≃L[ℝ] (ℝ × p.ker)) → E →L[ℝ] (ℝ × p.ker))
  have hV : IsOpen V :=
    (hprod.continuousOn_fderiv_of_isOpen hΩ hn)
      |>.isOpen_inter_preimage hΩ ContinuousLinearEquiv.isOpen
  have haV : a ∈ V := ⟨ha, T, hTa.symm⟩
  let e := e₀.restrOpen V hV
  have he : (e : E → ℝ × p.ker) = φ.prodFun := rfl
  have haS : a ∈ e.source := ⟨φ.pt_mem_toOpenPartialHomeomorph_source, haV⟩
  have hSΩ : e.source ⊆ Ω := fun _ hx ↦ hx.2.1
  have hfirst (x : E) : (e x).1 = f x := rfl
  have hea : e a = (f a, 0) := by
    change (f a, (Classical.choose hker) (a - a)) = (f a, 0)
    simp
  have hInv : ContDiffOn ℝ n e.symm e.target := by
    apply e.open_target.contDiffOn_iff.mpr
    intro q hq
    have hx := e.map_target hq
    obtain ⟨A, hA⟩ := hx.2.2
    have hfx := hprod.contDiffAt (hΩ.mem_nhds (hSΩ hx))
    have hd : HasFDerivAt e A.toContinuousLinearMap (e.symm q) := by
      rw [he, hA]
      exact hfx.differentiableAt hn0 |>.hasFDerivAt
    exact e.contDiffAt_symm hq hd (by rw [he]; exact hfx)
  refine ⟨e, haS, hSΩ, ?_, hInv, hea, hfirst, ?_, ?_⟩
  · rw [he]
    exact hprod.mono hSΩ
  · exact (hs.to_implicitFunctionOfComplemented hsurj hker).hasFDerivAt
  · exact Module.Dual.finrank_ker_add_one_of_ne_zero hpn

/-- A regular level of the actual function has a kernel chart of the same
regularity, with its center derivative and exact local level-set image. -/
theorem exists_contDiff_levelChart {n : ℕ∞ω} (hn : 1 ≤ n)
    {f : E → ℝ} {Ω : Set E} {a : E}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ n f Ω) (ha : a ∈ Ω)
    (hp : fderiv ℝ f a ≠ 0) :
    let p := fderiv ℝ f a
    ∃ (B : Set p.ker) (σ : p.ker → E) (U : Set E),
      IsOpen B ∧ (0 : p.ker) ∈ B ∧ ContDiffOn ℝ n σ B ∧ σ 0 = a ∧
      MapsTo σ B Ω ∧ (∀ w ∈ B, f (σ w) = f a) ∧
      HasFDerivAt σ p.ker.subtypeL 0 ∧ Function.Injective (fderiv ℝ σ 0) ∧
      InjOn σ B ∧ IsOpen U ∧ a ∈ U ∧ U ⊆ Ω ∧
      σ '' B = U ∩ {x | f x = f a} ∧
      Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E := by
  obtain ⟨e, haS, hSΩ, _, hInv, hea, hfirst, hdsection, hdim⟩ :=
    exists_contDiff_levelCoordinates hn hΩ hf ha hp
  let p := fderiv ℝ f a
  let B := {w : p.ker | (f a, w) ∈ e.target}
  let σ := fun w : p.ker ↦ e.symm (f a, w)
  have hB : IsOpen B := e.open_target.preimage (continuous_const.prodMk continuous_id)
  have h0 : (0 : p.ker) ∈ B := by
    change (f a, 0) ∈ e.target
    rw [← hea]
    exact e.map_source haS
  have hσ : ContDiffOn ℝ n σ B :=
    hInv.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ hw)
  have hσ0 : σ 0 = a := by
    dsimp only [σ]
    rw [← hea, e.left_inv haS]
  have hσS : MapsTo σ B e.source := fun _ hw ↦ e.map_target hw
  have hlevel (w : p.ker) (hw : w ∈ B) : f (σ w) = f a := by
    have h := congrArg Prod.fst (e.right_inv hw)
    simpa only [hfirst] using h
  have hdσ : HasFDerivAt σ p.ker.subtypeL 0 :=
    hdsection
  have hinj : Function.Injective (fderiv ℝ σ 0) := by
    rw [hdσ.fderiv]
    exact Subtype.val_injective
  have hσinj : InjOn σ B := by
    intro u hu v hv huv
    exact congrArg Prod.snd (e.symm.injOn hu hv huv)
  refine ⟨B, σ, e.source, hB, h0, hσ, hσ0, (fun _ hw ↦ hSΩ (hσS hw)), hlevel,
    hdσ, hinj, hσinj, e.open_source, haS, hSΩ, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨hσS hw, hlevel w hw⟩
    · rintro ⟨hx, hlevelx⟩
      have hex : e x = (f a, (e x).2) := Prod.ext ((hfirst x).trans hlevelx) rfl
      refine ⟨(e x).2, ?_, ?_⟩
      · change (f a, (e x).2) ∈ e.target
        rw [← hex]
        exact e.map_source hx
      · dsimp only [σ]
        rw [← hex, e.left_inv hx]
  · exact hdim

end OTSelector.Geometry
