import OTSelector.Transport.Coupling.CostEquivalence
import OTSelector.Transport.Coupling.OptimalPlanExistence
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.CompactCalibrationPartners.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.CompactCalibrationPartners`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.CompactCalibrationPartners

**Conditions:** A continuous calibrated potential and compact endpoint carriers; probability dual/primal attainment is used in the final existence consumer.

**Objects:** Closed/compact measurable domains of calibrated partners and almost-everywhere nontrivial partners on disjoint carriers.

**Proof detail:** Project the closed calibration relation through the compact partner subtype; coupling marginals transfer its full support to each endpoint, and disjoint compact carriers exclude equal endpoints.

**Sources:** [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110), Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products); [D. H. Fremlin, Measure Theory, Volume 4, Appendix 4A](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6), Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products); [Gabriel Peyré; Marco Cuturi, Computational Optimal Transport (2019 author version)](https://optimaltransport.github.io/pdf/ComputationalOT.pdf#page=110), Section 6.1, Proposition 6.1 and equation (6.1), pp. 106–107 (PDF pages 110–111).

Source relation (corollary): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
# Compact measurable domains of original calibrated partners

Calibration against a compact target has a closed existence domain, by projection
along the compact target subtype. Actual calibrated couplings then give full-marginal
partner domains. Disjoint compact carriers exclude trivial partners. Combining primal
and dual attainment constructs an original optimal potential with these properties,
without selecting partners or assuming a measurable transport decomposition.
-/

open Set MeasureTheory Filter

namespace OTSelector.Reconstruction

variable {M : Type*} [MetricSpace M]

/-- The points admitting a forward calibrated partner in a compact set form a closed
set. No choice or measurability of a partner map is used. -/
theorem isClosed_exists_forward_calibrated_partner {f : M → ℝ} (hf : Continuous f)
    {B : Set M} (hB : IsCompact B) :
    IsClosed {x | ∃ y ∈ B, f y - f x = dist x y} := by
  let _instForwardCalibratedCompact : CompactSpace B := isCompact_iff_compactSpace.mp hB
  let S : Set (M × B) := {p | f p.2 - f p.1 = dist p.1 p.2}
  have hS : IsClosed S := isClosed_eq
    ((hf.comp (continuous_subtype_val.comp continuous_snd)).sub (hf.comp continuous_fst))
    (continuous_fst.dist (continuous_subtype_val.comp continuous_snd))
  have heq : Prod.fst '' S = {x | ∃ y ∈ B, f y - f x = dist x y} := by
    ext x
    constructor
    · rintro ⟨⟨z, y⟩, hp, rfl⟩
      exact ⟨y, y.property, hp⟩
    · rintro ⟨y, hy, hcal⟩
      exact ⟨(x, ⟨y, hy⟩), hcal, rfl⟩
  rw [← heq]
  exact isClosedMap_fst_of_compactSpace S hS

/-- Backward calibrated partner existence over a compact source is closed. -/
theorem isClosed_exists_backward_calibrated_partner {f : M → ℝ} (hf : Continuous f)
    {A : Set M} (hA : IsCompact A) :
    IsClosed {y | ∃ x ∈ A, f y - f x = dist x y} := by
  simpa only [Pi.neg_apply, neg_sub_neg, dist_comm] using
    isClosed_exists_forward_calibrated_partner hf.neg hA

/-- Restricting the forward partner domain to a compact source gives a compact
geometric carrier for the original source marginal. -/
theorem isCompact_forward_calibrated_domain {f : M → ℝ} (hf : Continuous f)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact {x | x ∈ A ∧ ∃ y ∈ B, f y - f x = dist x y} :=
  hA.inter_right (isClosed_exists_forward_calibrated_partner hf hB)

/-- The analogous backward domain is compact in the original target space. -/
theorem isCompact_backward_calibrated_domain {f : M → ℝ} (hf : Continuous f)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) :
    IsCompact {y | y ∈ B ∧ ∃ x ∈ A, f y - f x = dist x y} :=
  hB.inter_right (isClosed_exists_backward_calibrated_partner hf hA)

variable [MeasurableSpace M] [BorelSpace M]

/-- The forward partner existence domain is Borel measurable. -/
theorem measurableSet_exists_forward_calibrated_partner {f : M → ℝ}
    (hf : Continuous f) {B : Set M} (hB : IsCompact B) :
    MeasurableSet {x | ∃ y ∈ B, f y - f x = dist x y} :=
  (isClosed_exists_forward_calibrated_partner hf hB).measurableSet

/-- The backward partner existence domain is Borel measurable. -/
theorem measurableSet_exists_backward_calibrated_partner {f : M → ℝ}
    (hf : Continuous f) {A : Set M} (hA : IsCompact A) :
    MeasurableSet {y | ∃ x ∈ A, f y - f x = dist x y} :=
  (isClosed_exists_backward_calibrated_partner hf hA).measurableSet

/-- An actual calibrated coupling gives forward partners for almost every original
source point. The target carrier is compact, and the source law is unchanged. -/
theorem ae_exists_forward_calibrated_partner_of_isCoupling
    {μ ν : Measure M} {π : Measure (M × M)} {f : M → ℝ}
    (hf : Continuous f) {B : Set M} (hB : IsCompact B)
    (hν : ∀ᵐ y ∂ν, y ∈ B) (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : ∀ᵐ p ∂π, f p.2 - f p.1 = dist p.1 p.2) :
    ∀ᵐ x ∂μ, ∃ y ∈ B, f y - f x = dist x y := by
  rw [← hπ.1]
  apply (ae_map_iff measurable_fst.aemeasurable
    (measurableSet_exists_forward_calibrated_partner hf hB)).mpr
  have hsnd : ∀ᵐ p ∂π, p.2 ∈ B :=
    ae_of_ae_map measurable_snd.aemeasurable (by rwa [hπ.2])
  filter_upwards [hsnd, hcal] with p hp hc
  exact ⟨p.2, hp, hc⟩

/-- The same original calibrated coupling gives backward partners almost everywhere
under its original target marginal. -/
theorem ae_exists_backward_calibrated_partner_of_isCoupling
    {μ ν : Measure M} {π : Measure (M × M)} {f : M → ℝ}
    (hf : Continuous f) {A : Set M} (hA : IsCompact A)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : ∀ᵐ p ∂π, f p.2 - f p.1 = dist p.1 p.2) :
    ∀ᵐ y ∂ν, ∃ x ∈ A, f y - f x = dist x y := by
  rw [← hπ.2]
  apply (ae_map_iff measurable_snd.aemeasurable
    (measurableSet_exists_backward_calibrated_partner hf hA)).mpr
  have hfst : ∀ᵐ p ∂π, p.1 ∈ A :=
    ae_of_ae_map measurable_fst.aemeasurable (by rwa [hπ.1])
  filter_upwards [hfst, hcal] with p hp hc
  exact ⟨p.1, hp, hc⟩

/-- Disjoint carriers force every almost-everywhere calibrated partner obtained from
an original coupling to be different from the point being transported. -/
theorem ae_exists_nontrivial_calibrated_partners_of_isCoupling
    {μ ν : Measure M} {π : Measure (M × M)} {f : M → ℝ}
    (hf : Continuous f) {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hAB : Disjoint A B) (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hπ : Vlasov.IsCoupling π μ ν)
    (hcal : ∀ᵐ p ∂π, f p.2 - f p.1 = dist p.1 p.2) :
    (∀ᵐ x ∂μ, x ∈ A ∧ ∃ y ∈ B, x ≠ y ∧ f y - f x = dist x y) ∧
      ∀ᵐ y ∂ν, y ∈ B ∧ ∃ x ∈ A, x ≠ y ∧ f y - f x = dist x y := by
  constructor
  · filter_upwards [hμ,
      ae_exists_forward_calibrated_partner_of_isCoupling hf hB hν hπ hcal] with x hx hp
    obtain ⟨y, hy, hc⟩ := hp
    refine ⟨hx, y, hy, ?_, hc⟩
    intro heq
    exact Set.disjoint_left.mp hAB hx (heq.symm ▸ hy)
  · filter_upwards [hν,
      ae_exists_backward_calibrated_partner_of_isCoupling hf hA hμ hπ hcal] with y hy hp
    obtain ⟨x, hx, hc⟩ := hp
    refine ⟨hy, x, hx, ?_, hc⟩
    intro heq
    exact Set.disjoint_left.mp hAB hx (heq.symm ▸ hy)

/-- Disjoint compactly carried probabilities admit an actual global optimal potential
with nontrivial partners almost everywhere under both original marginals. The same
potential characterizes their entire original distance-optimal face. -/
theorem exists_optimal_calibration_with_partners_of_disjoint_compact_carriers
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    ∃ f : M → ℝ, LipschitzWith 1 f ∧
      (∀ᵐ x ∂μ, x ∈ A ∧ ∃ y ∈ B, x ≠ y ∧ f y - f x = dist x y) ∧
      (∀ᵐ y ∂ν, y ∈ B ∧ ∃ x ∈ A, x ≠ y ∧ f y - f x = dist x y) ∧
      ∀ π : Measure (M × M), Vlasov.IsCoupling π μ ν →
        (IsOptimalCoupling edist μ ν π ↔
          ∀ᵐ p ∂π, f p.2 - f p.1 = dist p.1 p.2) := by
  obtain ⟨f, π, hf, hπ, hcal, hface⟩ :=
    exists_calibrated_optimalCoupling_of_compact_carrier μ ν (hA.union hB)
      (hμ.mono fun _ hx ↦ Or.inl hx) (hν.mono fun _ hy ↦ Or.inr hy)
  obtain ⟨hforward, hbackward⟩ := ae_exists_nontrivial_calibrated_partners_of_isCoupling
    hf.continuous hA hB hAB hμ hν hπ.1 hcal
  exact ⟨f, hf, hforward, hbackward, hface⟩

end OTSelector.Reconstruction

end
