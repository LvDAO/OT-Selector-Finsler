import OTSelector.MeasureTheory.CountableScalarSectionNull
import OTSelector.Transport.Kantorovich.CalibratedEndpoints
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.EndpointScalarSection.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.EndpointScalarSection`; the selected original proof blocks follow. -/
section

/-!
# Transport.Calibration.EndpointScalarSection

* **Conditions:** Ordered calibration represents label equality and clock order; a backward endpoint map has fixed clock displacement and lands at calibrated initial endpoints. Joint label–clock absolute continuity is assumed for the nullity statement.
* **Objects:** At most one clock per label on a fixed-time backward endpoint slice, and zero input mass of that slice.
* **Proof detail:** Calibration preserves labels of endpoints, initial-endpoint uniqueness identifies their clock, and Fubini makes singleton clock sections null under the supplied product absolute continuity.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (derived): The endpoint framework comes from transport rays; the fixed-time scalar-section argument is a local criterion using explicit order and AC premises.
-/

/-!
# Null clock sections of fixed-time backward endpoint slices

Ordered calibration identifies the label of each point with that of its calibrated
initial endpoint. Uniqueness of initial endpoints for a label then forces one clock
value per label on every fixed-time slice. The existing joint absolute-continuity
criterion gives nullity for the same input measure, including a Haar core restriction.
-/

open Set MeasureTheory OTSelector.Geometry

noncomputable section
namespace OTSelector.Reconstruction

variable {X M Z : Type*} [MetricSpace M]

/-- Points a fixed calibrated time after genuine regular initial endpoints have
one clock value per label. This uses actual endpoint uniqueness for the ordered relation. -/
theorem single_clock_of_backward_initial_endpoint
    {u : M → ℝ} {a : M → Z} {N : Set M} {S : Set X} {φ R : X → M} {t : ℝ}
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hφ : MapsTo φ S N) (hR : MapsTo R S (calibratedInitialEndpoints u ∩ N))
    (hshift : ∀ x ∈ S, u (φ x) - u (R x) = t)
    (hcal : ∀ x ∈ S, u (φ x) - u (R x) = dist (R x) (φ x)) :
    ∀ x ∈ S, ∀ y ∈ S, a (φ x) = a (φ y) → u (φ x) = u (φ y) := by
  intro x hx y hy hlabel
  have hleft := ((horder (R x) (hR hx).2 (φ x) (hφ hx)).mpr (hcal x hx)).1
  have hright := ((horder (R y) (hR hy).2 (φ y) (hφ hy)).mpr (hcal y hy)).1
  have he := injOn_label_calibratedInitialEndpoints horder (hR hx) (hR hy)
    (hleft.trans (hlabel.trans hright.symm))
  have hu := congrArg u he
  linarith [hshift x hx, hshift y hy]

variable [MeasurableSpace X] [MeasurableSpace Z]

/-- Joint label-clock absolute continuity makes a measurable fixed-time backward
initial-endpoint slice null. The actual maps, clock and input measure are preserved. -/
theorem measure_eq_zero_of_backward_initial_endpoint_section
    (ν : Measure X) {u : M → ℝ} {a : M → Z} {N : Set M}
    {φ R : X → M} {S C : Set X} {t : ℝ}
    (ha : AEMeasurable (a ∘ φ) ν) (hu : AEMeasurable (u ∘ φ) ν)
    (hac : ν.map (fun x ↦ (a (φ x), u (φ x))) ≪ (ν.map (a ∘ φ)).prod volume)
    (hS : MeasurableSet S) (hSC : S ⊆ C)
    (hemb : MeasurableEmbedding (fun x : C ↦ (a (φ x.val), u (φ x.val))))
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hφ : MapsTo φ S N) (hR : MapsTo R S (calibratedInitialEndpoints u ∩ N))
    (hshift : ∀ x ∈ S, u (φ x) - u (R x) = t)
    (hcal : ∀ x ∈ S, u (φ x) - u (R x) = dist (R x) (φ x)) : ν S = 0 :=
  measure_eq_zero_of_single_clock_per_label ν ha hu hac hS hSC hemb
    (single_clock_of_backward_initial_endpoint (u := u) (a := a) (φ := φ) (R := R)
      horder hφ hR hshift hcal)

end OTSelector.Reconstruction

end
end
