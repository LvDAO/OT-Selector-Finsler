import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Analysis.Calculus.CompactUniformFirstJet

Conditions: A C1 map near a compact parameter set, or two maps with matching first jets there and the stated displacement control.

Objects: A common first-order remainder radius and a uniform comparison for the two label differences.

Proof detail: Use uniform continuity of the derivative on a compact neighborhood, integrate/mean-value bound the derivative deviation along short segments, and cancel the matching first jets.

## Mathematical sources

- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=46): Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
- [Jiří Lebl, Basic Analysis II](https://www.jirka.org/ra/realanal2.pdf#page=37): Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61.
- [Terence Tao, An Epsilon of Room, I](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation: Uniform compact Taylor corollary, proved from derivative continuity; no independent jet remainder assumption is inserted.
-/

/-!
# Uniform first-order remainders near compact families

Continuity of the actual derivative gives a common first-order remainder near every
center of a compact set. The perturbed point need not belong to that compact set.
Matching values and partial derivatives then compare two parameterized maps uniformly.
-/

open Set Filter Metric
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A C1 map has a uniform first-order Taylor remainder near compact centers. -/
theorem exists_uniform_firstOrder_remainder_of_contDiffOn
    {f : E → V} {U K : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ 1 f U)
    (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ K, ∀ h : E, ‖h‖ < r →
      x + h ∈ U ∧ ‖f (x + h) - f x - (fderiv ℝ f x) h‖ ≤ ε * ‖h‖ := by
  have hDf : ∀ x ∈ K, ContinuousAt (fderiv ℝ f) x := fun x hx ↦
    (hf.continuousOn_fderiv_of_isOpen hU (by rfl)).continuousAt (hU.mem_nhds (hKU hx))
  have huni := hK.uniformContinuousAt_of_continuousAt (fderiv ℝ f) hDf
    (Metric.dist_mem_uniformity hε)
  obtain ⟨δ, hδ, hclose⟩ := Metric.mem_uniformity_dist.mp huni
  obtain ⟨η, hη, hηU⟩ := hK.exists_thickening_subset_open hU hKU
  let r := min δ η
  have hr : 0 < r := lt_min hδ hη
  refine ⟨r, hr, ?_⟩
  intro x hx h hh
  have hballU : ball x r ⊆ U := by
    intro y hy
    apply hηU
    exact mem_thickening_iff.mpr ⟨x, hx, lt_of_lt_of_le hy (min_le_right δ η)⟩
  have hxh : x + h ∈ ball x r := by simpa [mem_ball, dist_eq_norm] using hh
  refine ⟨hballU hxh, ?_⟩
  have hd : ∀ y ∈ ball x r, DifferentiableAt ℝ f y := fun y hy ↦
    (hf.contDiffAt (hU.mem_nhds (hballU hy))).differentiableAt (by simp)
  have hbound : ∀ y ∈ ball x r, ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ ε := by
    intro y hy
    have hxy : dist x y < δ :=
      lt_of_lt_of_le (by simpa only [mem_ball, dist_comm] using hy) (min_le_left δ η)
    have hnear := hclose hxy hx
    change dist (fderiv ℝ f x) (fderiv ℝ f y) < ε at hnear
    rw [dist_comm, dist_eq_norm] at hnear
    exact hnear.le
  have hmv := (convex_ball x r).norm_image_sub_le_of_norm_fderiv_le'
    hd hbound (mem_ball_self hr) hxh
  simpa only [add_sub_cancel_left] using hmv

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Maps with matching values and actual label derivatives on a compact family have
uniformly small differences when only the label is perturbed. -/
theorem exists_uniform_label_difference_of_same_firstJet
    {f g : P × E → V} {U K : Set (P × E)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) (hg : ContDiffOn ℝ 1 g U)
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hvalue : ∀ z ∈ K, f z = g z)
    (hderiv : ∀ z ∈ K, ∀ h : E, (fderiv ℝ f z) (0, h) = (fderiv ℝ g z) (0, h))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ z ∈ K, ∀ h : E, ‖h‖ < r →
      (z.1, z.2 + h) ∈ U ∧ ‖f (z.1, z.2 + h) - g (z.1, z.2 + h)‖ ≤ ε * ‖h‖ := by
  obtain ⟨r, hr, hrem⟩ := exists_uniform_firstOrder_remainder_of_contDiffOn hU
    (hf.sub hg) hK hKU hε
  refine ⟨r, hr, ?_⟩
  intro z hz h hh
  have hnorm : ‖((0 : P), h)‖ = ‖h‖ := by simp
  have hstep := hrem z hz (0, h) (by simpa only [hnorm] using hh)
  have hfD := (hf.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp)
  have hgD := (hg.contDiffAt (hU.mem_nhds (hKU hz))).differentiableAt (by simp)
  have hD : fderiv ℝ (fun q ↦ f q - g q) z = fderiv ℝ f z - fderiv ℝ g z :=
    (hfD.hasFDerivAt.sub hgD.hasFDerivAt).fderiv
  have hzadd : z + (0, h) = (z.1, z.2 + h) := by ext <;> simp
  simpa only [hzadd, hnorm, hD, sub_apply,
    hvalue z hz, hderiv z hz h, sub_self, sub_zero] using hstep

end OTSelector.Geometry
