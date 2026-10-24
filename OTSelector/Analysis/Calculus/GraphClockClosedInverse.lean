import OTSelector.Analysis.Calculus.GraphClockDensity
import OTSelector.Geometry.Manifold.CurveGraphCoordinates
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.GraphClockClosedInverse.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.GraphClockClosedInverse`; the selected original proof blocks follow. -/
section

/-!
# Analysis.Calculus.GraphClockClosedInverse

Conditions: A genuine open partial homeomorphism of graph coordinates, differentiability on the closed interval and strictly positive scalar graph speed on its interior.
Objects: The increasing scalar graph clock and the scalar component of the given inverse, including both endpoint images.
Proof detail: Use the positive-derivative monotonicity criterion and intermediate values to identify interval images; restrict continuity of the already given inverse to that image.

## Mathematical sources

- Jiří Lebl, *Basic Analysis I, version 6.3 (15 May 2026)*: Section 4.2, Proposition 4.2.8, p. 166 (positive derivative implies strict increase); Section 3.3, Theorem 3.3.8, pp. 133–134 (intermediate values). https://www.jirka.org/ra/realanal.pdf#page=166
- D. H. Fremlin, *Measure Theory, Volume 4, Appendix 4A*: Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products). https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6

Source relation: A one-dimensional monotonicity and inverse-restriction corollary in product coordinates. It proves closed-interval control of the specified inverse, not a new global inverse function theorem.
-/

/-!
# Closed-interval data of the actual graph inverse

Positive actual graph speed identifies both endpoint images. The original graph
homeomorphism then supplies its same inverse clock continuously up to either end,
with no separate inverse regularity or endpoint image assumption.
-/

open Set
open scoped Topology

namespace OTSelector.Reconstruction
open OTSelector.Geometry

variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The actual positive graph clock and its actual inverse carry the complete closed
physical interval to the complete closed graph interval, continuously in both directions. -/
theorem curveGraphClock_closedInverse_data
    {γ : W × ℝ → ℝ × V}
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap γ)
    {w : W} {a b : ℝ} (hab : a ≤ b)
    (hsource : ∀ t ∈ Icc a b, (w, t) ∈ e.source)
    (hγ : ∀ t ∈ Icc a b, DifferentiableAt ℝ γ (w, t))
    (hv : ∀ t ∈ Ioo a b, 0 < (fderiv ℝ γ (w, t) (0, 1)).1) :
    let s := fun t ↦ (γ (w, t)).1
    let τ := fun r ↦ (e.symm (w, r)).2
    s '' Icc a b = Icc (s a) (s b) ∧
      s '' Ioo a b = Ioo (s a) (s b) ∧
      ContinuousOn τ (Icc (s a) (s b)) ∧
      MapsTo τ (Icc (s a) (s b)) (Icc a b) ∧
      ∀ t ∈ Icc a b, τ (s t) = t := by
  let s := fun t ↦ (γ (w, t)).1
  have hc : ContinuousOn s (Icc a b) :=
    fun t ht ↦ (curveGraphClock_hasDerivAt (hγ t ht)).continuousAt.continuousWithinAt
  have hm : StrictMonoOn s (Icc a b) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a b) hc
    intro t ht
    rw [interior_Icc] at ht
    rw [(curveGraphClock_hasDerivAt (hγ t (Ioo_subset_Icc_self ht))).deriv]
    exact hv t ht
  have himage := hc.image_Icc_of_monotoneOn hab hm.monotoneOn
  have hinv := (curveGraphClock_injOn_leftInverse he hsource).2
  have htarget : MapsTo (fun r ↦ (w, r)) (Icc (s a) (s b)) e.target := by
    intro r hr
    rw [← himage] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    simpa only [he, curveGraphCoordinateMap, s] using e.map_source (hsource t ht)
  refine ⟨himage, hc.image_Ioo_of_strictMonoOn hab hm, ?_, ?_, hinv⟩
  · exact (e.symm.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id) htarget).snd
  · intro r hr
    rw [← himage] at hr
    obtain ⟨t, ht, rfl⟩ := hr
    change (e.symm (w, (γ (w, t)).1)).2 ∈ Icc a b
    rwa [hinv t ht]

end OTSelector.Reconstruction

end
