import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric

/-!
## Lemma skeleton

* **Conditions:** A finite-dimensional C1 Hausdorff preconnected manifold with a continuous reversible Finsler norm; 0 ≤ r ≤ d(x,y), epsilon > 0.
* **Objects:** The genuine Finsler length metric, an exact first-radius split and approximate second-radius control, then approximate midpoints.
* **Proof detail:** Choose a C1 competitor within epsilon of the length infimum. Apply the intermediate value theorem to distance from its starting point, then use additivity of path length.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Anton Petrunin, *Lectures on metric geometry (author lecture notes, course Spring 2020)*, Lecture 1, Section L, pp. 16–17: length spaces, induced length metric and approximate midpoints.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=16
* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html

**Relationship to the sources:** Derived length-space lemma. The source describes length metrics and epsilon-midpoints; the arbitrary-radius split with exact first distance is proved here.
-/

/-!
# Approximate splitting for the original Finsler length metric

The genuine infimum over C1 Finsler path lengths has approximate splitting points.
Choose a C1 path with length within epsilon of the original distance. The continuous
distance from its starting point attains every radius up to the endpoint distance.
Additivity of the actual path length controls the remaining distance from that point.
Thus the first radius can be attained exactly, while only the remaining distance
incurs the prescribed error. Approximate splitting and midpoint statements follow.

The metric in every statement is the already constructed original Finsler length
metric. No minimizing path, completeness, strong convexity, or inner product is assumed.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff ENNReal

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M] [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

/-- A near-minimizing actual Finsler path contains an exact prescribed-radius point
whose remaining distance exceeds the complementary radius by less than epsilon. -/
theorem exists_lengthMetric_split (F : ContinuousFinslerNorm E M) (x y : M) {r ε : ℝ} :
    letI : MetricSpace M := F.metricSpace
    0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : M, dist x z = r ∧ dist z y < dist x y - r + ε := by
  let : MetricSpace M := F.metricSpace
  intro hr hrd hε
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let : ∀ y : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) y) := F.enormSMulClass
  have happrox : F.lengthEDist x y < ENNReal.ofReal (dist x y + ε) := by
    change edist x y < ENNReal.ofReal (dist x y + ε)
    rw [edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)
  obtain ⟨γ, hγ₀, hγ₁, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt happrox
  have hcont : ContinuousOn (fun t ↦ dist x (γ t)) (Icc (0 : ℝ) 1) := by
    intro t ht
    exact Filter.Tendsto.dist continuousWithinAt_const (hγ.continuousOn t ht)
  have hbetween : r ∈ Icc (dist x (γ 0)) (dist x (γ 1)) := by
    simpa only [hγ₀, hγ₁, dist_self] using (show r ∈ Icc 0 (dist x y) from ⟨hr, hrd⟩)
  obtain ⟨t, ht, htr⟩ := intermediate_value_Icc zero_le_one hcont hbetween
  change dist x (γ t) = r at htr
  have hfirst : edist x (γ t) ≤ Manifold.pathELength 𝓘(ℝ, E) γ 0 t := by
    change F.lengthEDist x (γ t) ≤ _
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc le_rfl ht.2)) hγ₀ rfl ht.1
  have hsecond : edist (γ t) y ≤ Manifold.pathELength 𝓘(ℝ, E) γ t 1 := by
    change F.lengthEDist (γ t) y ≤ _
    exact Manifold.riemannianEDist_le_pathELength
      (hγ.mono (Icc_subset_Icc ht.1 le_rfl)) rfl hγ₁ ht.2
  have hsum : edist x (γ t) + edist (γ t) y < ENNReal.ofReal (dist x y + ε) := by
    apply (add_le_add hfirst hsecond).trans_lt
    rw [Manifold.pathELength_add ht.1 ht.2]
    exact hlen
  rw [edist_dist, edist_dist, ← ENNReal.ofReal_add dist_nonneg dist_nonneg] at hsum
  have hreal : dist x (γ t) + dist (γ t) y < dist x y + ε :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hsum
  refine ⟨γ t, htr, ?_⟩
  rw [htr] at hreal
  linarith

/-- The original Finsler length metric has approximate splitting at every intermediate radius. -/
theorem exists_lengthMetric_approximate_split (F : ContinuousFinslerNorm E M)
    (x y : M) {r ε : ℝ} :
    letI : MetricSpace M := F.metricSpace
    0 ≤ r → r ≤ dist x y → 0 < ε →
      ∃ z : M, dist x z < r + ε ∧ dist z y < dist x y - r + ε := by
  let : MetricSpace M := F.metricSpace
  intro hr hrd hε
  obtain ⟨z, hz, hzy⟩ := F.exists_lengthMetric_split x y hr hrd hε
  exact ⟨z, by rw [hz]; linarith, hzy⟩

/-- The original Finsler length metric has approximate midpoints with arbitrarily small error. -/
theorem exists_lengthMetric_approximate_midpoint (F : ContinuousFinslerNorm E M)
    (x y : M) {ε : ℝ} :
    letI : MetricSpace M := F.metricSpace
    0 < ε → ∃ z : M, dist x z < dist x y / 2 + ε ∧ dist z y < dist x y / 2 + ε := by
  let : MetricSpace M := F.metricSpace
  intro hε
  obtain ⟨z, hxz, hzy⟩ := F.exists_lengthMetric_approximate_split x y
    (r := dist x y / 2) (by positivity) (by linarith [dist_nonneg (x := x) (y := y)]) hε
  refine ⟨z, hxz, ?_⟩
  convert hzy using 1
  ring

end OTSelector.Geometry.ContinuousFinslerNorm
