import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelPositionRank
import OTSelector.Geometry.Finsler.C11PotentialFamily
import OTSelector.Geometry.Finsler.CalibratedReach
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11PrescribedReach.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11PrescribedReach`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.PrescribedReach

* **Conditions:** A compact C1,1 contact core, an actual complete family matching its original covector, and a specified positive two-sided reach.
* **Objects:** The compact core restricted to that exact reach and actual AE good-potential/position comparisons on the full prescribed interval.
* **Proof detail:** Intersect with closed forward/backward reach levels, reconstruct the restricted-core AE derivatives and use actual curve uniqueness on the prescribed segment.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Lemmas 4.9–4.10, p. 33 (Borel strain/end times and closed trimmed strain sets).
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.

Source relation (derived): A reach-specific refinement of the original core. The prescribed reach need not be bounded by the former cover radius.
-/

/-!
# Original C1,1 cores at a prescribed calibrated reach

Intersect an existing compact core with the original two-sided reach set. The same
extension and complete family yield actual potential-family good points and position
comparison on the prescribed interval. Goodness is derived anew for the restricted
core; the prescribed positive reach need not be bounded by the old cover radius.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- Restrict the actual core to prescribed two-sided reach, retaining its extension
and complete family and deriving new good points for the restricted core. -/
theorem ae_good_on_prescribed_calibrated_reach_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ x ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G x) x)
    {A : E → ℝ → M} (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (A x) univ)
    (hinit : ∀ x ∈ U, A x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily old A (x, 0) = (x, fderiv ℝ G x))
    {Δ : ℝ} (hΔ : 0 < Δ) :
    letI : MetricSpace M := F.metricSpace
    let S := OTSelector.Geometry.calibratedReachLevel u Δ ∩
      OTSelector.Geometry.calibratedReachLevel (-u) Δ
    let C := K ∩ (extChartAt 𝓘(ℝ, E) old).symm ⁻¹' S
    IsCompact C ∧
      (∀ x ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm x) = Δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u l = Δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) r = Δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm x) = Δ) ∧
      ∀ ν : Measure E, ν ≪ m →
        ∀ᵐ x ∂ν.restrict C,
          F.HasC11PotentialFamilyAt m old 0 u G C x ∧
          F.HasC11LevelPositionComparisonAt old G A Δ x
 := by
  let _instPrescribedReachMetric : MetricSpace M := F.metricSpace
  let S := OTSelector.Geometry.calibratedReachLevel u Δ ∩
    OTSelector.Geometry.calibratedReachLevel (-u) Δ
  let C := K ∩ (extChartAt 𝓘(ℝ, E) old).symm ⁻¹' S
  have hS : IsClosed S :=
    (F.isClosed_calibratedReachLevel hcomplete hu Δ).inter
      (F.isClosed_calibratedReachLevel hcomplete hu.neg Δ)
  have hc : ContinuousOn (extChartAt 𝓘(ℝ, E) old).symm K :=
    (continuousOn_extChartAt_symm old).mono (hKU.trans hUt)
  have hC : IsCompact C :=
    hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed hS)
      inter_subset_left
  have hpartners : ∀ x ∈ C, ∃ l r : M,
      dist l ((extChartAt 𝓘(ℝ, E) old).symm x) = Δ ∧
      u ((extChartAt 𝓘(ℝ, E) old).symm x) - u l = Δ ∧
      dist ((extChartAt 𝓘(ℝ, E) old).symm x) r = Δ ∧
      u r - u ((extChartAt 𝓘(ℝ, E) old).symm x) = Δ := by
    intro x hx
    obtain ⟨r, hr, hur⟩ := hx.2.1
    obtain ⟨l, hl, hul⟩ := hx.2.2
    exact ⟨l, r, by simpa only [dist_comm] using hl,
      by simpa only [Pi.neg_apply, neg_sub_neg] using hul, hr, hur⟩
  have hinterior : MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
      (OTSelector.Geometry.calibratedInterior u) := by
    intro x hx
    obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners x hx
    exact ⟨⟨l, dist_pos.mp (hl.symm ▸ hΔ), hul.trans hl.symm⟩,
      ⟨r, dist_pos.mp (hr.symm ▸ hΔ), hur.trans hr.symm⟩⟩
  refine ⟨hC, hpartners, ?_⟩
  intro ν hν
  exact hF.ae_levelPositionComparison_of_calibrated_C11_core hcomplete old hν hC hU
    (fun x hx ↦ hKU hx.1) hUt hu hinterior hG hLip (hval.mono inter_subset_left)
    (fun x hx ↦ hactual x hx.1) hEL hinit hp hΔ hpartners

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
