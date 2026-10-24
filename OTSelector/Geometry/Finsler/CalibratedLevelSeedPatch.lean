import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CalibratedLevelSeedPatch.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CalibratedLevelSeedPatch`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.CalibratedLevelSeedPatch

* **Conditions:** An actual calibrated seed stores a covector kernel, rational level, complete unit curves and an original C1,1 presentation with explicit compact-core/gradient data.
* **Objects:** Structured seed/presentation objects retaining the true original clock, Borel labels, normalization and countable local coordinate cover.
* **Proof detail:** Package the supplied geometric witnesses and read the level/interior consequences directly from their actual clock and unit-curve identities.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).

Source relation (adapter): The records are project interfaces implementing the ray-cluster construction; their full fields are retained in the bound source excerpt.
-/

/-!
# Actual calibrated level seeds with their local coordinate cover

This record retains the actual complete curves, their original potential clock,
measurable seed labels and constructed local coordinate estimates. The covector
kernel remains the label space; a linear normalization is retained for volume.
The geometric producer constructs these data from the original Finsler structure.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original C1,1 presentation retained by an actual level-seed producer.
The section and ambient curves are the ones used to define the patch itself. -/
structure C11LevelSeedPresentation (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (p : E →L[ℝ] ℝ) (level : ℚ) (V S : Set p.ker) (curve : p.ker → ℝ → M) where
  initialChart : M
  core : Set E
  domain : Set E
  potential : E → ℝ
  gradientConstant : ℝ≥0
  position : p.ker → E
  ambient : E → ℝ → M
  core_compact : IsCompact core
  domain_open : IsOpen domain
  core_subset : core ⊆ domain
  domain_target : domain ⊆ (extChartAt 𝓘(ℝ, E) initialChart).target
  potential_contDiff : ContDiff ℝ 1 potential
  gradient_lipschitz : LipschitzWith gradientConstant (fderiv ℝ potential)
  potential_eq : EqOn potential (u ∘ (extChartAt 𝓘(ℝ, E) initialChart).symm) core
  potential_derivative : ∀ y ∈ core,
    HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) initialChart).symm)
      (fderiv ℝ potential y) y
  position_contDiff : ContDiffOn ℝ 1 position V
  position_domain : MapsTo position V domain
  position_injective : InjOn position V
  position_immersion : ∀ w ∈ V, Function.Injective (fderiv ℝ position w)
  labels_eq : S = V ∩ position ⁻¹' core
  curve_eq : curve = fun w ↦ ambient (position w)
  ambient_complete : ∀ y ∈ domain, F.IsEulerLagrangeOn (ambient y) univ
  ambient_initial : ∀ y ∈ domain,
    ambient y 0 = (extChartAt 𝓘(ℝ, E) initialChart).symm y
  ambient_momentum : ∀ y ∈ domain,
    F.chartMomentumFamily initialChart ambient (y, 0) = (y, fderiv ℝ potential y)
  level_eq : ∀ w ∈ V, potential (position w) = (level : ℝ)
  zero_mem : (0 : p.ker) ∈ V
  center_mem : position 0 ∈ core
  covector_eq : p = fderiv ℝ potential (position 0)
  position_derivative : HasFDerivAt position p.ker.subtypeL 0

/-- A constructed original level seed, including its genuine curves and local
readouts. Labels may have zero reference measure and no saturation is required. -/
structure CalibratedLevelSeedPatch (F : ContinuousFinslerNorm E M) (u : M → ℝ) where
  covector : E →L[ℝ] ℝ
  level : ℚ
  openLabels : Set covector.ker
  openLabels_open : IsOpen openLabels
  labels : Set covector.ker
  labels_measurable : MeasurableSet labels
  labels_subset : labels ⊆ openLabels
  normalization : (ℝ × covector.ker) ≃L[ℝ] E
  curve : covector.ker → ℝ → M
  c11_presentation : Nonempty
    (C11LevelSeedPresentation F u covector level openLabels labels curve)
  continuous_at_time : ∀ t : ℝ, ContinuousOn (fun w ↦ curve w t) openLabels
  complete : ∀ w ∈ labels, F.IsEulerLagrangeOn (curve w) univ
  unit : ∀ w ∈ labels, ∀ t : ℝ,
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve w) ⟨t, (1 : ℝ)⟩) = 1
  initial_injective : InjOn (fun w ↦ curve w 0) labels
  reach : ℝ
  reach_pos : 0 < reach
  clock : ∀ w ∈ labels, ∀ t ∈ Icc (-reach) reach, u (curve w t) = (level : ℝ) + t
  centers : Set (ℝ × covector.ker)
  centers_countable : centers.Countable
  centers_subset : centers ⊆ univ ×ˢ openLabels
  radius : ℝ × covector.ker → ℝ
  constant : ℝ × covector.ker → ℝ≥0
  local_data : ∀ q ∈ centers, 0 < radius q ∧
    closedBall q (radius q) ⊆ univ ×ˢ openLabels ∧
    MapsTo (fun z : ℝ × covector.ker ↦ curve z.2 z.1) (closedBall q (radius q))
      (extChartAt 𝓘(ℝ, E) (curve q.2 q.1)).source ∧
    LipschitzOnWith (constant q)
      (fun z : ℝ × covector.ker ↦ extChartAt 𝓘(ℝ, E) (curve q.2 q.1) (curve z.2 z.1))
      (closedBall q (radius q))
  local_cover : (⋃ q ∈ centers, ball q (radius q)) = univ ×ˢ openLabels

namespace CalibratedLevelSeedPatch

variable {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- Every retained initial seed lies on its original rational potential level. -/
theorem potential_initial (A : CalibratedLevelSeedPatch F u)
    {w : A.covector.ker} (hw : w ∈ A.labels) : u (A.curve w 0) = (A.level : ℝ) := by
  simpa only [add_zero] using A.clock w hw 0 ⟨neg_nonpos.mpr A.reach_pos.le, A.reach_pos.le⟩

omit [BorelSpace E] in
/-- The two-sided original clock places each retained seed in the calibrated interior. -/
theorem mapsTo_initial_calibratedInterior [T2Space M] [PreconnectedSpace M]
    (A : CalibratedLevelSeedPatch F u) (hF : F.IsSmoothStronglyConvex)
    (hu : let _instSeedPatchLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instSeedPatchMetric : MetricSpace M := F.metricSpace
    MapsTo (fun w ↦ A.curve w 0) A.labels (OTSelector.Geometry.calibratedInterior u) := by
  let _instSeedPatchMetric : MetricSpace M := F.metricSpace
  dsimp only
  intro w hw
  have horder : -A.reach ≤ A.reach := by linarith [A.reach_pos]
  exact (hF.calibrated_window_of_complete_unit_endpoints hu (A.complete w hw) (A.unit w hw)
    (A.clock w hw (-A.reach) (left_mem_Icc.mpr horder))
    (A.clock w hw A.reach (right_mem_Icc.mpr horder))).2.2 0
      ⟨neg_neg_of_pos A.reach_pos, A.reach_pos⟩

end CalibratedLevelSeedPatch

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
