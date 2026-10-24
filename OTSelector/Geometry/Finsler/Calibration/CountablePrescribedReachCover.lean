import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.Calibration.PrescribedReach
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11PrescribedReachCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11PrescribedReachCover`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.CountablePrescribedReachCover

* **Conditions:** The complete Finsler/potential hypotheses for the original countable C1,1 cover and arbitrary chartwise absolutely continuous populations.
* **Objects:** One family of cores/extensions/complete curves, restricted to every positive rational reach, with simultaneous population AE witness implications.
* **Proof detail:** Keep the original cover, intersect its cores with each rational two-sided reach set and take countably many AE coordinate-to-physical transfers.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Lemmas 4.9–4.10, p. 33 (Borel strain/end times and closed trimmed strain sets).
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.

Source relation (derived): Countability yields all rational reach implications together; no full mass or positive mass on a selected reach set is asserted.
-/

/-!
# One original family cover with all positive rational calibrated reaches

Restrict one selected original C1,1 cover to each two-sided rational reach set, retaining
its extensions and complete families. The restricted cores cover that reach set exactly.
Countably many coordinate-to-physical AE transfers give actual good core witnesses for
all positive rational reaches, without a full-mass assumption on a reach set.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
universe uE uM
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [OpensMeasurableSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- One original family cover has good restricted cores at every positive rational
reach, simultaneously almost everywhere for each chart-absolutely-continuous law. -/
theorem exists_countable_original_prescribed_reach_good_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    letI : MetricSpace M := F.metricSpace
    ∃ ι : Type (max uE uM), Countable ι ∧
      ∃ (old : ι → M) (K U : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (A : ι → E → ℝ → M),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) =
          OTSelector.Geometry.calibratedInterior u ∧
        (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧
          U i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ∀ x ∈ U i,
            A i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
            F.IsEulerLagrangeOn (A i x) univ ∧
            ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (A i x) ∧
            F.chartMomentumFamily (old i) (A i) (x, 0) = (x, fderiv ℝ (G i) x)) ∧
        let S : ℚ → Set M := fun q ↦
          OTSelector.Geometry.calibratedReachLevel u (q : ℝ) ∩
            OTSelector.Geometry.calibratedReachLevel (-u) (q : ℝ)
        let C : ι → ℚ → Set E := fun i q ↦
          K i ∩ (extChartAt 𝓘(ℝ, E) (old i)).symm ⁻¹' S q
        (∀ q : ℚ, 0 < q →
          (∀ i, IsCompact (C i q) ∧ ∀ x ∈ C i q, ∃ l r : M,
            dist l ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ) ∧
            u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - u l = (q : ℝ) ∧
            dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) r = (q : ℝ) ∧
            u r - u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ)) ∧
          (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' C i q) = S q) ∧
        ∀ η : Measure M,
          (∀ old : M, (η.restrict (extChartAt 𝓘(ℝ, E) old).source).map
            (extChartAt 𝓘(ℝ, E) old) ≪ m) →
          ∀ᵐ y ∂η, ∀ q : ℚ, 0 < q → y ∈ S q →
            ∃ (i : ι) (x : E), x ∈ C i q ∧
              (extChartAt 𝓘(ℝ, E) (old i)).symm x = y ∧
              F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (C i q) x ∧
              F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (q : ℝ) x := by
  classical
  let : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, δ, B, A, hdata, hcover, hreach, hUA⟩ :=
    hF.exists_countable_calibrated_C11_family_cover hcomplete hu
  let : Countable ι := hcount
  let S : ℚ → Set M := fun q ↦
    OTSelector.Geometry.calibratedReachLevel u (q : ℝ) ∩
      OTSelector.Geometry.calibratedReachLevel (-u) (q : ℝ)
  let C : ι → ℚ → Set E := fun i q ↦
    K i ∩ (extChartAt 𝓘(ℝ, E) (old i)).symm ⁻¹' S q
  have htrim (i : ι) (q : ℚ) (hq : 0 < q) :=
    hF.ae_good_on_prescribed_calibrated_reach_core hcomplete (old i) m
      (hdata i).1 (hUA i).1 (hUA i).2.1 (hUA i).2.2.1 hu
      (hdata i).2.2.1 (hdata i).2.2.2.2.1 (hdata i).2.2.2.2.2.1
      (hdata i).2.2.2.2.2.2.2
      (A := A i) (fun x hx ↦ ((hUA i).2.2.2 x hx).2.1)
      (fun x hx ↦ ((hUA i).2.2.2 x hx).1)
      (fun x hx ↦ ((hUA i).2.2.2 x hx).2.2.2)
      (Δ := (q : ℝ)) (by exact_mod_cast hq)
  have himage (q : ℚ) (hq : 0 < q) :
      (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' C i q) = S q := by
    apply Subset.antisymm
    · intro y hy
      obtain ⟨i, x, hx, rfl⟩ := mem_iUnion.mp hy
      exact hx.2
    · intro y hy
      have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
      obtain ⟨r, hr, hur⟩ := hy.1
      obtain ⟨l, hl, hul⟩ := hy.2
      have hl' : dist l y = (q : ℝ) := by simpa only [dist_comm] using hl
      have hul' : u y - u l = (q : ℝ) := by
        simpa only [Pi.neg_apply, neg_sub_neg] using hul
      have hyI : y ∈ OTSelector.Geometry.calibratedInterior u :=
        ⟨⟨l, dist_pos.mp (hl'.symm ▸ hqR), hul'.trans hl'.symm⟩,
          ⟨r, dist_pos.mp (hr.symm ▸ hqR), hur.trans hr.symm⟩⟩
      rw [← hcover] at hyI
      obtain ⟨i, x, hxK, hxy⟩ := mem_iUnion.mp hyI
      refine mem_iUnion.mpr ⟨i, x, ⟨hxK, ?_⟩, hxy⟩
      change (extChartAt 𝓘(ℝ, E) (old i)).symm x ∈ S q
      rwa [hxy]
  refine ⟨ι, hcount, old, K, U, G, L, A, hdata, hcover, hUA, ?_, ?_⟩
  · intro q hq
    exact ⟨fun i ↦ ⟨(htrim i q hq).1, (htrim i q hq).2.1⟩, himage q hq⟩
  · intro η hηchart
    let χ (i : ι) := extChartAt 𝓘(ℝ, E) (old i)
    let ξ (i : ι) := (η.restrict (χ i).source).map (χ i)
    let Q (i : ι) (q : ℚ) (x : E) :=
      F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (C i q) x ∧
        F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (q : ℝ) x
    have hphysical (j : ι × {q : ℚ // 0 < q}) : ∀ᵐ y ∂η,
        y ∈ (χ j.1).source → χ j.1 y ∈ C j.1 j.2.val → Q j.1 j.2.val (χ j.1 y) := by
      have hcore : ∀ᵐ x ∂(ξ j.1).restrict (C j.1 j.2.val), Q j.1 j.2.val x :=
        (htrim j.1 j.2.val j.2.property).2.2 (ξ j.1) (hηchart (old j.1))
      have hχ : AEMeasurable (χ j.1) (η.restrict (χ j.1).source) :=
        (continuousOn_extChartAt (old j.1)).aemeasurable
          (isOpen_extChartAt_source (old j.1)).measurableSet
      exact ae_imp_of_ae_restrict (ae_of_ae_map hχ (ae_imp_of_ae_restrict hcore))
    filter_upwards [ae_all_iff.mpr hphysical] with y hy
    intro q hq hyS
    change y ∈ S q at hyS
    rw [← himage q hq] at hyS
    obtain ⟨i, x, hxC, hxy⟩ := mem_iUnion.mp hyS
    have hxT : x ∈ (χ i).target := (hdata i).2.1 hxC.1
    have hxQ : Q i q x := by
      have h := hy (i, ⟨q, hq⟩) (hxy ▸ (χ i).map_target hxT)
      rw [← hxy, (χ i).right_inv hxT] at h
      exact h hxC
    exact ⟨i, x, hxC, hxy, hxQ.1, hxQ.2⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
