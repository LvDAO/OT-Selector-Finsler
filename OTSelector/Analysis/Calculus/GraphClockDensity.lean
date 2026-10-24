import OTSelector.Analysis.ODE.Hamiltonian.MatrixCoordinates
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.CurveGraphJacobian
import OTSelector.MeasureTheory.AreaFormula.ParameterizedJacobiDeterminant
import OTSelector.MeasureTheory.AreaFormula.ParameterizedLipschitzJacobian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.JacobiGraphClock.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.JacobiGraphClock`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual graph-coordinate map with its own partial inverse, nonzero longitudinal derivative and the stated interval regularity.

Objects: Actual graph-clock derivative, injectivity/inverse identities, interval image and physical normalized Jacobian data.

Proof detail: Differentiate the original longitudinal coordinate, use positivity for interval monotonicity, differentiate the same inverse and apply the block determinant formula.

Sources: Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); D. H. Fremlin, Theorem 263A, pp. 22–24: linear change of variables and absolute determinant (https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=22).
Relation: Graph-clock adapter; the clock and density data are calculated from the same actual position family.
-/

/-!
# The actual graph clock supplies the measure-transfer data

The original position family and its graph-coordinate inverse determine the scalar
clock, its derivative, its inverse, and the physical Jacobian in one fixed frame.
Injectivity and interval images follow from these actual coordinates.
-/

open Set Filter Matrix Module
open scoped Topology

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry

variable {E W V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι] [DecidableEq ι]

/-- The scalar graph clock is the actual first-coordinate derivative of the
same position family; it is not replaced by an affine clock. -/
theorem curveGraphClock_hasDerivAt
    {γ : W × ℝ → ℝ × V} {w : W} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ (w, t)) :
    HasDerivAt (fun r ↦ (γ (w, r)).1) (fderiv ℝ γ (w, t) (0, 1)).1 t := by
  exact (hγ.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t w).prodMk (hasDerivAt_id t))).fst

omit [NormedSpace ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V] in
/-- A fixed-label slice of the actual graph coordinate map is injective on
every part of its source, and its actual inverse recovers the original time. -/
theorem curveGraphClock_injOn_leftInverse
    {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {w : W} {I : Set ℝ} (hI : ∀ t ∈ I, (w, t) ∈ e.source) :
    InjOn (fun t ↦ (γ (w, t)).1) I ∧
      ∀ t ∈ I, (e.symm (w, (γ (w, t)).1)).2 = t := by
  have hleft (t : ℝ) (ht : t ∈ I) : e.symm (w, (γ (w, t)).1) = (w, t) := by
    have h := e.left_inv (hI t ht)
    rwa [he] at h
  refine ⟨?_, fun t ht ↦ congrArg Prod.snd (hleft t ht)⟩
  intro t ht r hr htr
  change (γ (w, t)).1 = (γ (w, r)).1 at htr
  have heq : e.symm (w, (γ (w, t)).1) = e.symm (w, (γ (w, r)).1) := by rw [htr]
  rw [hleft t ht, hleft r hr] at heq
  exact congrArg Prod.snd heq

/-- A positive actual longitudinal velocity identifies the whole graph-time
interval, with its actual endpoint values rather than a prescribed rescaling. -/
theorem curveGraphClock_image_Ioo
    {γ : W × ℝ → ℝ × V} {w : W} {a b : ℝ} (hab : a ≤ b)
    (hγ : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ (w, t))
    (hv : ∀ t ∈ Ioo a b, 0 < (fderiv ℝ γ (w, t) (0, 1)).1) :
    (fun t ↦ (γ (w, t)).1) '' Ioo a b = Ioo (γ (w, a)).1 (γ (w, b)).1 := by
  have hc : ContinuousOn (fun t ↦ (γ (w, t)).1) (Icc a b) :=
    fun t ht ↦ (curveGraphClock_hasDerivAt (hγ t ht)).continuousAt.continuousWithinAt
  apply hc.image_Ioo_of_strictMonoOn hab
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hc
  intro t ht
  rw [interior_Icc] at ht
  rw [(curveGraphClock_hasDerivAt (hγ t (Ioo_subset_Icc_self ht))).deriv]
  exact hv t ht

/-- The actual adapted graph inverse supplies all scalar change-of-time data
and the physical Jacobian, retaining the same graph-position matrix and fixed bases. -/
theorem physicalGraphClock_densityData
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V)
    (A : E ≃L[ℝ] (ℝ × V)) (ℓ : (ℝ × W) ≃L[ℝ] E)
    {γ : W × ℝ → E} {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (A ∘ γ))
    {w : W} {I : Set ℝ} (hsource : ∀ t ∈ I, (w, t) ∈ e.source)
    (hγ : ∀ t ∈ I, DifferentiableAt ℝ γ (w, t))
    (hi : ∀ t ∈ I, DifferentiableAt ℝ e.symm (w, (A (γ (w, t))).1))
    (hv : ∀ t ∈ I, (fderiv ℝ (A ∘ γ) (w, t) (0, 1)).1 ≠ 0) :
    let s := fun t ↦ (A (γ (w, t))).1
    let v := fun t ↦ (fderiv ℝ (A ∘ γ) (w, t) (0, 1)).1
    let τ := fun r ↦ (e.symm (w, r)).2
    let J := fun r ↦ vectorFamilyMatrix bV (fun i ↦
      fderiv ℝ (fun z ↦ (curveGraphPosition (A ∘ γ) e (z, r)).2) w (bW i))
    let κ := |(LinearMap.toMatrix (timeLabelBasis bV) (timeLabelBasis bW)
      (ℓ.trans A).symm.toLinearEquiv.toLinearMap).det|
    InjOn s I ∧ ∀ t ∈ I, τ (s t) = t ∧ HasDerivAt s (v t) t ∧
      HasDerivAt τ (v t)⁻¹ (s t) ∧
      parameterizedJacobian (fun p : ℝ × W ↦ γ (p.2, p.1)) ℓ (t, w) =
        |v t| * |(J (s t)).det| * κ := by
  dsimp only
  have hc := curveGraphClock_injOn_leftInverse he hsource
  refine ⟨hc.1, ?_⟩
  intro t ht
  have hdata := parameterizedJacobian_adaptedGraphTime_data bW bV A ℓ he
    (hsource t ht) (hγ t ht) (hi t ht) (hv t ht)
  exact ⟨hc.2 t ht,
    curveGraphClock_hasDerivAt (A.differentiableAt.comp (w, t) (hγ t ht)), hdata⟩

end OTSelector.Reconstruction

end
end
