import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedCoverage
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.RationalLevelSeeds
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.CalibratedAtlas

* **Conditions:** Complete original Finsler geometry and a 1-Lipschitz potential.
* **Objects:** An exact countable Borel injective calibrated-window atlas covering its whole two-sided calibrated interior.
* **Proof detail:** Combine actual rational-level seeds, rational calibrated endpoints and the existing countable local chart-ball cover, proving both coverage inclusions.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.

Source relation (derived): The explicit atlas is derived from original geometry rather than supplied as a foliation assumption.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedAtlas.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedAtlas`; the selected original proof blocks follow. -/
section

/-!
# An exact countable atlas of the original calibrated interior

Actual rational-level seeds, rational calibration endpoints, and their countable
local coordinate balls produce measurable injective windows covering precisely
the two-sided calibrated interior of the original Lipschitz potential.
-/

open Set Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Countably many actual calibrated seed windows cover exactly the original
calibrated interior, with no additional coverage or level-saturation premise. -/
theorem exists_countable_calibratedWindow_atlas (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instAtlasLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instAtlasMetric : MetricSpace M := F.metricSpace
    ∃ κ : Type (max u v), Countable κ ∧ ∃ P : κ → CalibratedSeedWindow F u,
      (⋃ k, (P k).toManifold '' (P k).domain) = calibratedInterior u := by
  classical
  let _instAtlasMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, A, hA⟩ :=
    hF.exists_countable_rational_levelSeedPatches hcomplete hu
  let _instAtlasCountable : Countable ι := hcount
  let _instAtlasCenters (i : ι) : Countable (A i).centers :=
    (A i).centers_countable.to_subtype
  let κ := Σ i : ι, ({a : ℚ // a < 0} × {b : ℚ // 0 < b}) × (A i).centers
  let P : κ → CalibratedSeedWindow F u := fun k ↦
    { seed := A k.1
      left := k.2.1.1.val
      right := k.2.1.2.val
      left_neg := k.2.1.1.property
      right_pos := k.2.1.2.property
      center := k.2.2.val
      center_mem := k.2.2.property }
  have hcover (q : ℚ) (z : M) (hz : z ∈ calibratedInterior u)
      (hq : u z = (q : ℝ)) : ∃ i, ∃ w ∈ (A i).labels, (A i).curve w 0 = z := by
    have hm : z ∈ ⋃ i, (fun w ↦ (A i).curve w 0) '' (A i).labels := by
      rw [hA]
      exact ⟨hz, q, hq⟩
    obtain ⟨i, w, hw, heq⟩ := mem_iUnion.mp hm
    exact ⟨i, w, hw, heq⟩
  refine ⟨κ, inferInstance, P, Set.Subset.antisymm ?_ ?_⟩
  · intro y hy
    obtain ⟨k, z, hz, rfl⟩ := mem_iUnion.mp hy
    exact (P k).mapsTo_calibratedInterior hF hu hz
  · intro y hy
    obtain ⟨i, w, hw, t, a, b, ha, hb, ht, hpoint, hleft, hright⟩ :=
      hF.exists_calibrated_window_seed_of_rational_initial_cover hcomplete hu A hcover hy
    have hm : (t, w) ∈ ⋃ q ∈ (A i).centers, ball q ((A i).radius q) := by
      rw [(A i).local_cover]
      exact ⟨mem_univ _, (A i).labels_subset hw⟩
    obtain ⟨q, hq, hball⟩ := mem_iUnion₂.mp hm
    let k : κ := ⟨i, (⟨⟨a, ha⟩, ⟨b, hb⟩⟩, ⟨q, hq⟩)⟩
    apply mem_iUnion.mpr
    refine ⟨k, (t, w), ?_, hpoint⟩
    exact ⟨hball, ht, hw, hleft, hright⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
