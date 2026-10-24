import OTSelector.Geometry.Manifold.CurveGraphCoordinates
import OTSelector.Geometry.Manifold.SameGraphInverse
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CurveGraphRegularDomain.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CurveGraphRegularDomain`; the selected original proof blocks follow. -/
section

/-!
Conditions: The actual C2 graph family has continuous longitudinal velocity, positive at the center, and a prescribed open graph domain.

Objects: An open regular subdomain on which the same inverse is differentiable with the stated formula.

Proof detail: Intersect the positive-velocity preimage with the original domain and apply the pointwise inverse formula at every point.

Sources: Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Jiří Lebl, Section 8.5.1, Proposition 8.5.5 and the following block-operator argument, p. 55 (https://www.jirka.org/ra/realanal2.pdf#page=55); D. H. Fremlin, Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products) (https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6).
Relation: Open-domain adapter for actual graph-coordinate derivatives.
-/

/-!
# An open regular domain for the same graph inverse

The actual longitudinal time derivative is continuous for a C2 position family.
Its positive locus inside a given graph domain is an explicit open neighborhood of
any positive central point. The same graph inverse is differentiable throughout it.
-/

open Set
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Shrinking to the positive longitudinal locus recovers regularity of the given
actual graph inverse without replacing it or assuming its differentiability. -/
theorem curveGraph_regular_domain {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)} {U D : Set (W × ℝ)} {q₀ : W × ℝ}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    (hU : IsOpen U) (hsource : e.source ⊆ U) (hγ : ContDiffOn ℝ 2 γ U)
    (hD : IsOpen D) (hsub : D ⊆ e.target) (hq₀ : q₀ ∈ D)
    (hv₀ : 0 < (fderiv ℝ γ (e.symm q₀) (0, 1)).1) :
    let Q := D ∩ {q | 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1}
    IsOpen Q ∧ q₀ ∈ Q ∧ Q ⊆ D ∧
      (∀ q ∈ Q, 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1) ∧
      DifferentiableOn ℝ e.symm Q := by
  let Q := D ∩ {q | 0 < (fderiv ℝ γ (e.symm q) (0, 1)).1}
  have hmap : MapsTo e.symm D U := fun q hq ↦ hsource (e.map_target (hsub hq))
  have hd := ((hγ.fderiv_of_isOpen hU (by norm_num : (1 : ℕ∞ω) + 1 ≤ 2)).clm_apply
    (contDiffOn_const (c := ((0 : W), (1 : ℝ))))).fst.continuousOn
  have hv : ContinuousOn (fun q ↦ (fderiv ℝ γ (e.symm q) (0, 1)).1) D :=
    hd.comp (e.symm.continuousOn.mono hsub) hmap
  have hQ : IsOpen Q := hv.isOpen_inter_preimage hD isOpen_Ioi
  refine ⟨hQ, ⟨hq₀, hv₀⟩, inter_subset_left, fun _ hq ↦ hq.2, ?_⟩
  intro q hq
  exact (differentiableAt_curveGraphInverse_of_regular he (hsub hq.1)
    ((hγ.contDiffAt (hU.mem_nhds (hmap hq.1))).differentiableAt (by norm_num))
    (ne_of_gt hq.2)).differentiableWithinAt

end OTSelector.Geometry

end
end
