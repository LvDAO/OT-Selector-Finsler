import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Riemannian.PathELength

/-!
## Lemma skeleton

* **Conditions:** Assigned tangent ENorms and an explicitly differentiable tangent-length contraction; C1 diffeomorphism and norm preservation for equality. No finite-distance, convexity, completeness or nondegeneracy hypothesis.
* **Objects:** Path lower-integrals and their induced extended length-distance infimum.
* **Proof detail:** Apply the manifold chain rule inside every path integral, take the infimum over admissible C1 paths, and use the inverse derivative identity for the reverse comparison.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, pp. 313–314, length distance, Definition 4.1 and Lemma 4.2, equations (4–1)–(4–4).
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf
* John M. Lee, *Introduction to Smooth Manifolds, second edition (2013)*, Chapter 3, sections “The Differential of a Smooth Map” pp. 55–59, “Computations in Coordinates” pp. 60–64, “The Tangent Bundle” pp. 65–67, “Velocity Vectors of Curves” pp. 68–70.
  https://sites.math.washington.edu/~lee/Books/ISM/front-matter.pdf#page=10

**Relationship to the sources:** Shen describes the smooth Finsler length construction. These contraction/isometry lemmas are derived chain-rule consequences in a weaker assigned-ENorm setting; they are not attributed as verbatim classical Finsler statements.
-/

/-!
# Tangent-length contractions and induced length isometries

A differentiable tangent-length contraction contracts actual path integrals.
A C1 map then contracts their infimum; a tangent-length-preserving C1
manifold diffeomorphism preserves the induced extended length distance.
These statements require only assigned tangent ENorms and their explicit
contraction identity. Finiteness, nondegeneracy, strong convexity and
completeness are not assumed.

The transport consequence for coupling costs and whole optimal-coupling
sets is in `OTSelector.Transport.Coupling.LengthIsometry`.
-/

open Set MeasureTheory
open scoped Manifold ENNReal ContDiff Topology

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [∀ x : M, ENorm (TangentSpace I x)] [normN : ∀ y : N, ENorm (TangentSpace J y)]

/-- Pointwise contraction of tangent norms contracts the length of every differentiable curve
on its parameter interval. The endpoints of the interval have zero measure. -/
theorem pathELength_comp_le {f : M → N} (hf : MDifferentiable I J f)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J f x v‖ₑ ≤ ‖v‖ₑ)
    {γ : ℝ → M} {a b : ℝ} (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Icc a b)) :
    Manifold.pathELength J (f ∘ γ) a b ≤ Manifold.pathELength I γ a b := by
  simp only [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_mono' measurableSet_Ioo
  intro t ht
  rw [mfderiv_comp_apply t (hf (γ t))
    ((hγ t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt (Icc_mem_nhds ht.1 ht.2))]
  exact hbound _ _

/-- Pointwise preservation of tangent norms preserves actual curve length, with no assumption
about the distances induced by those norms. -/
theorem pathELength_comp_eq {f : M → N} (hf : MDifferentiable I J f)
    (hpres : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J f x v‖ₑ = ‖v‖ₑ)
    {γ : ℝ → M} {a b : ℝ} (hγ : MDifferentiableOn 𝓘(ℝ, ℝ) I γ (Icc a b)) :
    Manifold.pathELength J (f ∘ γ) a b = Manifold.pathELength I γ a b := by
  simp only [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp only
  rw [mfderiv_comp_apply t (hf (γ t))
    ((hγ t ⟨ht.1.le, ht.2.le⟩).mdifferentiableAt (Icc_mem_nhds ht.1 ht.2))]
  exact hpres _ _

/-- A C¹ tangent-norm contraction contracts the infimum of lengths of admissible C¹ paths.
The proof maps each admissible path and compares its actual derivative integral. No finite-distance
or path-existence hypothesis is needed. -/
theorem riemannianEDist_comp_le {f : M → N} (hf : ContMDiff I J 1 f)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J f x v‖ₑ ≤ ‖v‖ₑ)
    (x y : M) : Manifold.riemannianEDist J (f x) (f y) ≤
      Manifold.riemannianEDist I x y := by
  conv_rhs => rw [Manifold.riemannianEDist]
  refine le_iInf fun γ ↦ le_iInf fun hγ ↦ ?_
  calc
    Manifold.riemannianEDist J (f x) (f y) ≤
        ∫⁻ t, ‖mfderiv% (f ∘ γ) t 1‖ₑ := by
      rw [Manifold.riemannianEDist]
      exact iInf_le_of_le (γ.map hf.continuous) (iInf_le _ (hf.comp hγ))
    _ ≤ ∫⁻ t, ‖mfderiv% γ t 1‖ₑ := by
      apply lintegral_mono
      intro t
      dsimp only
      rw [mfderiv_comp_apply t (hf.mdifferentiable one_ne_zero (γ t))
        (hγ.mdifferentiable one_ne_zero t)]
      exact hbound _ _

/-- Norm preservation for the inverse is derived from the forward identity and the chain rule;
it is not an additional geometric assumption. -/
theorem enorm_mfderiv_symm (e : Diffeomorph I J M N 1)
    (hpres : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J e x v‖ₑ = ‖v‖ₑ)
    (y : N) (v : TangentSpace J y) : ‖mfderiv J I e.symm y v‖ₑ = ‖v‖ₑ := by
  have hcomp : (e : M → N) ∘ e.symm = id := by
    ext z
    exact e.apply_symm_apply z
  have hderiv := mfderiv_comp y (e.mdifferentiable one_ne_zero (e.symm y))
    (e.symm.mdifferentiable one_ne_zero y)
  rw [hcomp, mfderiv_id] at hderiv
  have hvec : mfderiv I J e (e.symm y) (mfderiv J I e.symm y v) = v :=
    congrArg (fun L ↦ L v) hderiv.symm
  have h := hpres (e.symm y) (mfderiv J I e.symm y v)
  rw [hvec] at h
  -- The tangent types coincide, but the norm instance still carries its base point.
  convert h.symm using 1
  exact congrArg (fun z : N ↦ @enorm (TangentSpace J z) (normN z) v)
    (e.apply_symm_apply y).symm

/-- A C¹ diffeomorphism preserving tangent norms preserves the induced extended length distance
exactly. This conclusion includes infinite values and does not assert nondegeneracy. -/
theorem riemannianEDist_diffeomorph (e : Diffeomorph I J M N 1)
    (hpres : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J e x v‖ₑ = ‖v‖ₑ)
    (x y : M) : Manifold.riemannianEDist J (e x) (e y) =
      Manifold.riemannianEDist I x y := by
  apply le_antisymm
  · exact riemannianEDist_comp_le e.contMDiff (fun x v ↦ (hpres x v).le) x y
  · simpa only [e.symm_apply_apply] using
      riemannianEDist_comp_le e.symm.contMDiff
        (fun z v ↦ (enorm_mfderiv_symm e hpres z v).le) (e x) (e y)

end OTSelector.Geometry
