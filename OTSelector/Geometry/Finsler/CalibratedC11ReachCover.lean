import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedC11Cover
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedC11ReachCover

* **Conditions:** The actual countable C1,1 contact cover and compact positive-reach trim sets.
* **Objects:** The same extensions on refined compact cores with fixed positive reaches and compact partner carriers, still exactly covering the interior.
* **Proof detail:** Intersect old cores with actual trim sets and retain matching value/derivative identities by restriction.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Lemmas 4.9–4.10, p. 33 (Borel strain/end times and closed trimmed strain sets).
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedC11ReachCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedC11ReachCover`; the selected original proof blocks follow. -/
section

/-!
# Countable C1,1 contact cores with uniform positive calibrated reach

Intersect the actual C1,1 coordinate cores with the original compact trimmed contact
sets. The same extensions retain their values and actual derivatives, while every new
core has a fixed positive calibrated length and compact carriers for both partners.
The inverse chart images still cover exactly the entire calibrated interior. Smoothness
outside a newly shrunken core is not asserted.
-/

open Set Manifold Metric
open scoped Topology ContDiff NNReal

noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual calibrated interior has a countable exact C1,1 contact cover retaining
uniform positive two-sided calibrated reach and compact original partner carriers on
each core. All geometry and extensions are constructed from the original potential. -/
theorem exists_countable_trimmed_calibrated_C11_cover (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {f : M → ℝ} (hf : let _instC11ReachLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 f) :
    let _instC11ReachMetric : MetricSpace M := F.metricSpace
    ∃ ι : Type (max u v), Countable ι ∧
      ∃ (old : ι → M) (K : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (δ : ι → ℝ) (B : ι → Set M),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (f ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) =
          OTSelector.Geometry.calibratedInterior f ∧
        ∀ i, 0 < δ i ∧ IsCompact (B i) ∧
          ∀ x ∈ K i, ∃ a ∈ B i, ∃ b ∈ B i,
            dist a ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i ∧
            f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - f a = δ i ∧
            dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) b = δ i ∧
            f b - f ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i := by
  classical
  let _instC11ReachMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, G, L, hdata, hcover⟩ :=
    hF.exists_countable_calibrated_C11_cover hcomplete hf
  let _instC11ReachCountable : Countable ι := hcount
  obtain ⟨A, B, hcompact, htrimcover, hreach⟩ :=
    hF.exists_compact_regular_trimmed_contact_cover hcomplete hf
  let J := ι × (ℕ × ℕ)
  let C : J → Set E := fun j ↦ K j.1 ∩
    (extChartAt 𝓘(ℝ, E) (old j.1)).symm ⁻¹' A j.2
  have hC (j : J) : IsCompact (C j) := by
    have hc : ContinuousOn (extChartAt 𝓘(ℝ, E) (old j.1)).symm (K j.1) :=
      (continuousOn_extChartAt_symm (old j.1)).mono (hdata j.1).2.1
    exact (hdata j.1).1.of_isClosed_subset
      (hc.preimage_isClosed_of_isClosed (hdata j.1).1.isClosed (hcompact j.2).1.isClosed)
      inter_subset_left
  refine ⟨J, inferInstance, (fun j ↦ old j.1), C, (fun j ↦ G j.1),
    (fun j ↦ L j.1), (fun j ↦ 1 / (j.2.1 + 1 : ℝ)), (fun j ↦ B j.2), ?_, ?_, ?_⟩
  · intro j
    obtain ⟨_, htarget, hG, hsupp, _, hLip, hval, hder, hactual⟩ := hdata j.1
    exact ⟨hC j, fun x hx ↦ htarget hx.1, hG, hsupp, hLip,
      hval.mono inter_subset_left, hder.mono inter_subset_left,
      fun x hx ↦ hactual x hx.1⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨j, z, hz, rfl⟩ := mem_iUnion.mp hx
      rw [← hcover]
      exact mem_iUnion.mpr ⟨j.1, z, hz.1, rfl⟩
    · intro x hx
      have hxC := hx
      rw [← hcover] at hxC
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hxC
      rw [← htrimcover] at hx
      obtain ⟨n, hn⟩ := mem_iUnion.mp hx
      refine mem_iUnion.mpr ⟨(i, n), z, ⟨hz, ?_⟩, hzx⟩
      change (extChartAt 𝓘(ℝ, E) (old i)).symm z ∈ A n
      rwa [hzx]
  · intro j
    refine ⟨by positivity, (hcompact j.2).2.1, ?_⟩
    intro x hx
    exact hreach j.2 ((extChartAt 𝓘(ℝ, E) (old j.1)).symm x) hx.2

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
