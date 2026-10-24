import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationSupportBound.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationSupportBound`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationSupportBound

* **Conditions:** The original continuous Finsler distance, a 1-Lipschitz potential and compact endpoint carriers.
* **Objects:** Continuous/Borel nonnegative distance slack and a finite common upper bound on every original endpoint pair.
* **Proof detail:** Use metric continuity and the Lipschitz inequality, then bound the continuous slack on the compact product.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=32): Sections 4A3B(a)–(c), p. 32; 4A3C(a)–(f), pp. 32–33.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): A generic compact distance-slack bound independent of geometric seed/type assignments.
-/

/-!
# Global original-distance slack bounds on compact endpoint supports

The original Lipschitz potential gives nonnegative slack. Its continuity and
compactness of the actual source and target carriers give a finite common bound
for every endpoint pair, including pairs assigned to different geometric types.
-/

open Set Metric Manifold
open scoped Topology ContDiff
noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]

/-- Original distance slack is continuous in both physical endpoints. -/
theorem continuous_distance_slack (F : ContinuousFinslerNorm E M) {u : M → ℝ}
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    Continuous (fun p : M × M ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) := by
  let : MetricSpace M := F.metricSpace
  exact (continuous_fst.dist continuous_snd).sub (hu.continuous.comp continuous_snd) |>.add
    (hu.continuous.comp continuous_fst)

/-- The same actual slack is Borel measurable, with no selected charts or inverses. -/
theorem measurable_distance_slack [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M]
    (F : ContinuousFinslerNorm E M) {u : M → ℝ}
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    Measurable (fun p : M × M ↦ (F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1) :=
  (F.continuous_distance_slack hu).measurable

/-- Original compact carriers supply the global nonnegative finite cost bound
needed for unmatched-type repairs of actual empirical plans. -/
theorem exists_uniform_compact_distance_slack_bound (F : ContinuousFinslerNorm E M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) {u : M → ℝ}
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    ∃ D > 0, ∀ x ∈ A, ∀ y ∈ B,
      0 ≤ (F.lengthEDist x y).toReal - u y + u x ∧
      (F.lengthEDist x y).toReal - u y + u x ≤ D := by
  let : MetricSpace M := F.metricSpace
  obtain ⟨D, hD⟩ := (hA.prod hB).exists_bound_of_continuousOn
    (F.continuous_distance_slack hu).continuousOn
  refine ⟨|D| + 1, by positivity, ?_⟩
  intro x hx y hy
  have hl := hu.le_add_mul y x
  simp only [NNReal.coe_one, one_mul, dist_comm y x] at hl
  refine ⟨by change 0 ≤ dist x y - u y + u x; linarith, ?_⟩
  have hb := hD (x, y) ⟨hx, hy⟩
  exact (le_abs_self _).trans (hb.trans ((le_abs_self D).trans (by linarith)))

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
