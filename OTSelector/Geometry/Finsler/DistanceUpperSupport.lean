import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.EndpointLengthSupport
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.DistanceUpperSupport

* **Conditions:** Two distinct points in complete original Finsler geometry and any legal chart of the endpoint.
* **Objects:** A genuine smooth touching upper support for the original distance-to-point in that chart.
* **Proof detail:** Construct a smooth minimizing extension, vary only a short terminal chart tail and add the unchanged prefix distance.

Mathematical sources:
- [Anton Petrunin, Lectures on metric geometry](https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=18): Lecture 1, Section L, Theorem 1.30 (Hopf–Rinow), Exercise 1.31 and proof, pp. 18–19.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceUpperSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceUpperSupport`; the selected original proof blocks follow. -/
section

/-!
# Smooth upper supports for the original distance to any distinct point

A complete original metric supplies a globally smooth extension of a minimizing
segment. Its short terminal tail stays in any chosen chart of the endpoint. Varying
that tail gives a smooth length support, and adding the fixed prefix distance gives
a touching upper support of the original distance. No distance regularity,
nonconjugacy, or chosen minimizing curve is assumed.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

private theorem exists_smooth_minimizer_chart_tail (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {p q : M} (hpq : p ≠ q) (hq : q ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    let _instMinimizerTailMetric : MetricSpace M := F.metricSpace
    ∃ (g : ℝ → M) (a : ℝ) (I : Set ℝ),
      g 0 = p ∧ g (dist p q) = q ∧ 0 < a ∧ a < dist p q ∧ IsOpen I ∧
      Icc a (dist p q) ⊆ I ∧ MapsTo g I (extChartAt 𝓘(ℝ, E) old).source ∧
      ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) old ∘ g) I ∧
      (∀ t ∈ I, ((extChartAt 𝓘(ℝ, E) old ∘ g) t,
        deriv (extChartAt 𝓘(ℝ, E) old ∘ g) t) ∈ chartEnergyDomain old) ∧
      Isometry (fun t : Icc (0 : ℝ) (dist p q) ↦ g t) := by
  let _instMinimizerTailMetric : MetricSpace M := F.metricSpace
  let _instMinimizerTailENorm : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hd : 0 < dist p q := dist_pos.mpr hpq
  obtain ⟨g, hg0, hgq, hEL, _, _, hiso, _⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hpq
  obtain ⟨I, hI, hdI, hmap, hx, hphase, _⟩ :=
    hF.exists_chartEulerLagrangeOn_of_isEulerLagrangeAt
      (hEL (dist p q) (mem_univ _)) old (by rwa [hgq])
  obtain ⟨δ, hδ, hδI⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hI.mem_nhds hdI)
  let ε := min (δ / 2) (dist p q / 2)
  have hε : 0 < ε := lt_min (half_pos hδ) (half_pos hd)
  have hεδ : ε ≤ δ := (min_le_left _ _).trans (half_le_self hδ.le)
  have hεd : ε ≤ dist p q / 2 := min_le_right _ _
  let a := dist p q - ε
  have ha : 0 < a := by dsimp [a]; linarith
  have had : a < dist p q := by dsimp [a]; linarith
  have hseg : Icc a (dist p q) ⊆ I := by
    intro t ht
    apply hδI
    rw [Real.closedBall_eq_Icc]
    dsimp [a] at ht
    constructor <;> linarith [ht.1, ht.2]
  exact ⟨g, a, I, hg0, hgq, ha, had, hI, hseg, hmap, hx, hphase, hiso⟩

/-- The original distance to any distinct point has a smooth touching upper support
in every chart containing the endpoint. The actual minimizing curve and its smooth
extension across the endpoint are constructed from original metric completeness. -/
theorem exists_smooth_distance_upperSupport_in_chart (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {p q : M} (hpq : p ≠ q) (hq : q ∈ (extChartAt 𝓘(ℝ, E) old).source) :
    let _instDistanceUpperSupportMetric : MetricSpace M := F.metricSpace
    ∃ (U : Set E) (H : E → ℝ), IsOpen U ∧ extChartAt 𝓘(ℝ, E) old q ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧ ContDiffOn ℝ ∞ H U ∧
      (∀ z ∈ U, dist p ((extChartAt 𝓘(ℝ, E) old).symm z) ≤ H z) ∧
      H (extChartAt 𝓘(ℝ, E) old q) = dist p q := by
  let _instDistanceUpperSupportMetric : MetricSpace M := F.metricSpace
  obtain ⟨g, a, I, hg0, hgq, ha, had, hI, hseg, hmap, hx, hphase, hiso⟩ :=
    exists_smooth_minimizer_chart_tail hF hcomplete old hpq hq
  let x : ℝ → E := extChartAt 𝓘(ℝ, E) old ∘ g
  have hrec (t : ℝ) (ht : t ∈ I) :
      (extChartAt 𝓘(ℝ, E) old).symm (x t) = g t :=
    (extChartAt 𝓘(ℝ, E) old).left_inv (hmap ht)
  have hxq : x (dist p q) = extChartAt 𝓘(ℝ, E) old q := by
    change extChartAt 𝓘(ℝ, E) old (g (dist p q)) = _
    rw [hgq]
  have hisotail : Isometry (fun t : Icc a (dist p q) ↦
      (extChartAt 𝓘(ℝ, E) old).symm (x t)) := by
    intro s t
    change edist ((extChartAt 𝓘(ℝ, E) old).symm (x s))
      ((extChartAt 𝓘(ℝ, E) old).symm (x t)) = edist s t
    rw [hrec s (hseg s.property), hrec t (hseg t.property)]
    exact hiso.edist_eq
      ⟨s, ha.le.trans s.property.1, s.property.2⟩
      ⟨t, ha.le.trans t.property.1, t.property.2⟩
  obtain ⟨U, hU, hqU, hUtarget, hS, hbound, htouch⟩ :=
    hF.exists_smooth_endpointLengthSupport_of_isometry old hI hx had hseg
      (fun t ht ↦ hphase t (hseg ht)) hisotail
  have hpa : dist p (g a) = a := by
    calc
      dist p (g a) = dist (g 0) (g a) := by rw [hg0]
      _ = dist (0 : ℝ) a := hiso.dist_eq ⟨0, le_rfl, dist_nonneg⟩ ⟨a, ha.le, had.le⟩
      _ = a := by rw [Real.dist_eq, zero_sub, abs_neg, abs_of_pos ha]
  have haq : dist (g a) q = dist p q - a := by
    calc
      dist (g a) q = dist (g a) (g (dist p q)) := by rw [hgq]
      _ = dist a (dist p q) :=
        hiso.dist_eq ⟨a, ha.le, had.le⟩ ⟨dist p q, dist_nonneg, le_rfl⟩
      _ = dist p q - a := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_pos (sub_pos.mpr had)]
  let H : E → ℝ := fun z ↦ dist p (g a) + F.chartEndpointLengthSupport old x a (dist p q) z
  refine ⟨U, H, hU, ?_, hUtarget, contDiffOn_const.add hS, ?_, ?_⟩
  · rwa [← hxq]
  · intro z hz
    have hb := hbound z hz
    rw [hrec a (hseg (left_mem_Icc.mpr had.le))] at hb
    exact (dist_triangle p (g a) ((extChartAt 𝓘(ℝ, E) old).symm z)).trans
      (add_le_add le_rfl hb)
  · change dist p (g a) + F.chartEndpointLengthSupport old x a (dist p q)
      (extChartAt 𝓘(ℝ, E) old q) = dist p q
    rw [← hxq, htouch, hrec a (hseg (left_mem_Icc.mpr had.le)),
      hrec (dist p q) (hseg (right_mem_Icc.mpr had.le)), hgq, hpa, haq]
    ring

/-- The original distance to a distinct point admits a smooth touching upper support
in the endpoint's own chart, with no distance differentiability premise. -/
theorem exists_smooth_distance_upperSupport (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {p q : M} (hpq : p ≠ q) :
    let _instDistanceUpperSupportMetric : MetricSpace M := F.metricSpace
    ∃ (U : Set E) (H : E → ℝ), IsOpen U ∧ extChartAt 𝓘(ℝ, E) q q ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, E) q).target ∧ ContDiffOn ℝ ∞ H U ∧
      (∀ z ∈ U, dist p ((extChartAt 𝓘(ℝ, E) q).symm z) ≤ H z) ∧
      H (extChartAt 𝓘(ℝ, E) q q) = dist p q :=
  hF.exists_smooth_distance_upperSupport_in_chart hcomplete q hpq (mem_extChartAt_source q)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
