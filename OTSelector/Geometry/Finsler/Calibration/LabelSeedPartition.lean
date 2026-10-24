import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedSeedRecovery
import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Geometry.Finsler.CalibratedSeedWindowLabels
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.MeasureTheory.MeasurableFirstRangeInverse
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerLabelSeedPartition.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerLabelSeedPartition`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.LabelSeedPartition

* **Conditions:** A countable actual calibrated atlas covers both populations, and measurable labels with the potential separate regular points and encode ordered calibration.
* **Objects:** A disjoint Borel partition of label space and measurable complete-seed labels recovering every interior point with its original potential clock.
* **Proof detail:** Enumerate the atlas, take the first label-image occurrence, invert each injective Borel seed label map and use uniqueness of the complete calibrated ray.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap42.pdf#page=22): Theorem 423I(a)–(b), pp. 22–23; Proposition 424G, p. 31.

Source relation (derived): A measurable atlas/seed implementation of the ray-cluster construction; a single selected local window is not asserted to contain the whole ray.
-/

/-!
# Measurable complete seeds for the original geometric label classes

The actual countable calibrated atlas selects complete seeds on a disjoint Borel
partition of the existing label space. Both original marginals give full mass to
that partition, and each selected seed recovers every calibrated interior point
with its label at the original potential difference. Local windows are retained;
the selected seed is not asserted to cover its whole class in a single window.
-/

open Set MeasureTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff

noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

variable {E M Z ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [Countable ι]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The existing countable atlas and original label system construct a first-eligible
Borel seed partition carrying both full marginals, with exact complete-curve recovery. -/
theorem exists_finsler_label_seed_partition (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instSeedPartitionLip : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {a : M → Z} (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instSeedPartitionOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (P : ι → F.CalibratedSeedWindow u) (μ ν : Measure M) [IsProbabilityMeasure μ]
    (hμcover : ∀ᵐ x ∂μ, x ∈ ⋃ i, (P i).toManifold '' (P i).domain)
    (hνcover : ∀ᵐ x ∂ν, x ∈ ⋃ i, (P i).toManifold '' (P i).domain) :
    let _instSeedPartitionMetric : MetricSpace M := F.metricSpace
    ∃ r : ℕ → ι, Function.Surjective r ∧
      let e := fun n (w : (P (r n)).labels) ↦ a ((P (r n)).seed.curve w 0)
      let B : ℕ → Set Z := disjointed (fun n ↦ Set.range (e n))
      (∀ n, MeasurableSet (B n)) ∧
      Pairwise (fun n k ↦ Disjoint (B n) (B k)) ∧
      (∀ᵐ x ∂μ, a x ∈ ⋃ n, B n) ∧ (∀ᵐ y ∂ν, a y ∈ ⋃ n, B n) ∧
      ∃ w : ∀ n, B n → (P (r n)).labels,
        (∀ n, Measurable (w n)) ∧ (∀ n z, e n (w n z) = z.val) ∧
        ∀ n (z : B n) x, x ∈ calibratedInterior u → a x = z.val →
          (P (r n)).seed.curve (w n z)
            (u x - ((P (r n)).seed.level : ℝ)) = x := by
  classical
  let _instSeedPartitionMetric : MetricSpace M := F.metricSpace
  obtain ⟨x, hx⟩ := hμcover.exists
  obtain ⟨i, hi⟩ := mem_iUnion.mp hx
  let _instSeedPartitionIndex : Nonempty ι := ⟨i⟩
  obtain ⟨r, hr⟩ := exists_surjective_nat ι
  let e := fun n (w : (P (r n)).labels) ↦ a ((P (r n)).seed.curve w 0)
  let B : ℕ → Set Z := disjointed (fun n ↦ Set.range (e n))
  have he (n : ℕ) : MeasurableEmbedding (e n) :=
    (P (r n)).measurableEmbedding_seedLabel hF hcomplete hu ha hinj
  obtain ⟨hB, hdis, _, _, w, hw, hwe⟩ :=
    exists_measurable_first_range_inverse e he
  let f := fun n (z : (P (r n)).domain) ↦ (P (r n)).toManifold z
  let p := fun n (z : (P (r n)).domain) ↦
    (⟨z.val.2, z.property.2.2⟩ : (P (r n)).labels)
  have hlabel (n : ℕ) (z : (P (r n)).domain) : a (f n z) = e n (p n z) :=
    (P (r n)).label_toManifold_eq_initial hF hcomplete hu horder z.property
  have hfull (η : Measure M)
      (hη : ∀ᵐ x ∂η, x ∈ ⋃ i, (P i).toManifold '' (P i).domain) :
      ∀ᵐ x ∂η, a x ∈ ⋃ n, B n := by
    have hcov : ∀ᵐ x ∂η, x ∈ ⋃ n, Set.range (f n) := by
      filter_upwards [hη] with x hx
      obtain ⟨i, z, hz, hzx⟩ := mem_iUnion.mp hx
      obtain ⟨n, rfl⟩ := hr i
      exact mem_iUnion.mpr ⟨n, ⟨⟨z, hz⟩, hzx⟩⟩
    have hlaw := ae_mem_label_ranges_of_ae_window_cover η a ha f p e he hlabel hcov
    have hpieces : ∀ᵐ z ∂η.map a, z ∈ ⋃ n, B n := by
      simpa only [B, iUnion_disjointed] using hlaw
    exact ae_of_ae_map ha.aemeasurable hpieces
  refine ⟨r, hr, hB, hdis, hfull μ hμcover, hfull ν hνcover, w, hw, hwe, ?_⟩
  intro n z x hx hax
  apply (P (r n)).seed.curve_eq_point_of_same_geometricLabel hF hcomplete hu horder
    (w n z).property.1 hx
  exact hax.trans (hwe n z).symm

end OTSelector.Reconstruction

end
end
