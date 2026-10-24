import LeanPool.Vlasov.OT.Coupling
import OTSelector.Transport.Kantorovich.CalibratedEndpoints
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CalibratedInteriorMass.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CalibratedInteriorMass`; the selected original proof blocks follow. -/
section

/-!
# Transport.Calibration.InteriorFullMass

* **Conditions:** An actual calibrated coupling with almost-everywhere distinct endpoints, null initial/terminal endpoint sets and a measurable calibrated interior.
* **Objects:** Both original marginals give full mass to the two-sided calibrated interior; disjoint carriers provide distinctness.
* **Proof detail:** Push calibrated successor/predecessor properties to the respective marginals and remove the corresponding null endpoint events.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.

Source relation (derived): An elementary marginal-support corollary of endpoint nullity; no smoothness, density or limiting-plan assumption is used.
-/

/-!
# Full original marginal mass in the calibrated interior

An original calibrated coupling with distinct endpoints supplies a successor to almost
every source point and a predecessor to almost every target point. If the corresponding
one-sided endpoint sets have zero marginal mass, both original marginals are carried by
the two-sided calibrated interior. Disjoint carriers imply the required distinctness.
The argument uses arbitrary original measures and no geometric or density regularity.
-/

open Set Filter MeasureTheory
open OTSelector.Geometry

namespace OTSelector.Reconstruction

variable {M : Type*} [MetricSpace M] [MeasurableSpace M]

/-- A calibrated original coupling with nontrivial pairs and null one-sided endpoints
carries both original marginals on the measurable two-sided calibrated interior. -/
theorem ae_calibratedInterior_of_isCoupling
    {μ ν : Measure M} {π : Measure (M × M)} {u : M → ℝ}
    (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    (hne : ∀ᵐ p ∂π, p.1 ≠ p.2)
    (hInterior : MeasurableSet (calibratedInterior u))
    (hInitialZero : μ (calibratedInitialEndpoints u) = 0)
    (hTerminalZero : ν (calibratedTerminalEndpoints u) = 0) :
    (∀ᵐ x ∂μ, x ∈ calibratedInterior u) ∧
      ∀ᵐ y ∂ν, y ∈ calibratedInterior u := by
  classical
  have hsource : ∀ᵐ p ∂π, p.1 ∉ calibratedInitialEndpoints u :=
    ae_of_ae_map (μ := π) measurable_fst.aemeasurable
      (by simpa only [hπ.1] using measure_eq_zero_iff_ae_notMem.mp hInitialZero)
  have htarget : ∀ᵐ p ∂π, p.2 ∉ calibratedTerminalEndpoints u :=
    ae_of_ae_map (μ := π) measurable_snd.aemeasurable
      (by simpa only [hπ.2] using measure_eq_zero_iff_ae_notMem.mp hTerminalZero)
  have hpair : ∀ᵐ p ∂π,
      p.1 ∈ calibratedInterior u ∧ p.2 ∈ calibratedInterior u := by
    filter_upwards [hsource, htarget, hcal, hne] with p hs ht hc hn
    have hf : ∃ y, p.1 ≠ y ∧ u y - u p.1 = dist p.1 y := ⟨p.2, hn, hc⟩
    have hb : ∃ x, x ≠ p.2 ∧ u p.2 - u x = dist x p.2 := ⟨p.1, hn, hc⟩
    constructor
    · refine ⟨?_, hf⟩
      by_contra hback
      exact hs ⟨hf, hback⟩
    · refine ⟨hb, ?_⟩
      by_contra hforward
      exact ht ⟨hb, hforward⟩
  constructor
  · rw [← hπ.1]
    exact (ae_map_iff measurable_fst.aemeasurable hInterior).mpr
      (hpair.mono fun _ hp ↦ hp.1)
  · rw [← hπ.2]
    exact (ae_map_iff measurable_snd.aemeasurable hInterior).mpr
      (hpair.mono fun _ hp ↦ hp.2)

/-- Disjoint original marginal carriers force nontrivial calibrated pairs, so null
initial and terminal endpoints give full marginal mass in the calibrated interior.
Neither compactness nor measurability of the carriers is required. -/
theorem ae_calibratedInterior_of_disjoint_carriers
    {μ ν : Measure M} {π : Measure (M × M)} {u : M → ℝ}
    (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : ∀ᵐ p ∂π, u p.2 - u p.1 = dist p.1 p.2)
    {A B : Set M} (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hInterior : MeasurableSet (calibratedInterior u))
    (hInitialZero : μ (calibratedInitialEndpoints u) = 0)
    (hTerminalZero : ν (calibratedTerminalEndpoints u) = 0) :
    (∀ᵐ x ∂μ, x ∈ calibratedInterior u) ∧
      ∀ᵐ y ∂ν, y ∈ calibratedInterior u := by
  have hfst : ∀ᵐ p ∂π, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (by rwa [hπ.1])
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (by rwa [hπ.2])
  apply ae_calibratedInterior_of_isCoupling hπ hcal _ hInterior hInitialZero hTerminalZero
  filter_upwards [hfst, hsnd] with p hp hq
  intro heq
  exact Set.disjoint_left.mp hAB hp (heq.symm ▸ hq)

end OTSelector.Reconstruction

end
