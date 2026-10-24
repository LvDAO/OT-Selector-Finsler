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
import OTSelector.Geometry.Finsler.Basic
/-
Portions copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under the Apache License, Version 2.0.
https://www.apache.org/licenses/LICENSE-2.0
Adapted from Mathlib.Geometry.Manifold.Riemannian.Basic.
-/

/-!
## Lemma skeleton

* **Conditions:** A continuous reversible finite tangent norm on a C1 manifold; finite-dimensional charts for local comparisons, Hausdorff separation for point separation, and preconnectedness for finite distance.
* **Objects:** The derivative-integral path infimum as an extended distance, extended metric and finite metric, all compatible with the original topology.
* **Proof detail:** Use straight chart segments for an upper comparison and a short-path exit argument for the lower comparison. Build the topology-compatible metric and use clopen finite-distance components for finiteness.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Anton Petrunin, *Lectures on metric geometry (author lecture notes, course Spring 2020)*, Lecture 1, Section L, pp. 16–17: length spaces, induced length metric and approximate midpoints.
  https://anton-petrunin.github.io/metric-geometry/tex/lectures.pdf#page=16
* Sébastien Gouëzel and mathlib contributors, *Mathlib.Geometry.Manifold.Riemannian.Basic*, Lemmas eventually_riemannianEDist_le_edist_extChartAt, eventually_riemannianEDist_lt, and setOfPred_riemannianEDist_lt_subset_nhds.
  https://github.com/leanprover-community/mathlib4/blob/d77ef0741c6da1ff12df68fb4145ea0ae0850c54/Mathlib/Geometry/Manifold/Riemannian/Basic.lean

**Relationship to the sources:** Weaker-regularity reversible extension of the smooth Finsler length construction in Shen. The detailed norm-only proof templates are explicitly adapted from the pinned mathlib source; no inner product is introduced.
-/

/-!
# The genuine metric induced by continuous reversible Finsler lengths

For finite-dimensional manifolds without boundary, `ContinuousFinslerNorm` supplies the original
finite tangent lengths. `lengthEDist` is the actual infimum of their integrals along C¹ paths.
The coordinate bounds proved from continuity and positivity in `FinslerNorm` give both a chart
segment upper bound and a short-path exit lower bound. These prove compatibility with the original
topology. Finite-dimensional local compactness upgrades Hausdorff separation to T₃, yielding an
extended metric. Connectedness then gives a finite metric with exactly the original topology.

The segment and exit arguments adapt Sébastien Gouëzel's norm-only proof steps in mathlib's
`Geometry.Manifold.Riemannian.Basic`. The only use of that module outside these proof templates
is its normed-vector-space line-length formula; no Riemannian bundle or inner product is assumed.
No local comparison, finite-distance, pre-existing metric-compatibility, or path-existence
hypothesis is included. Completeness and Finsler geodesic/Jacobi identifications are separate.
-/

open Bundle Set MeasureTheory Manifold Filter Metric
open scoped NNReal ENNReal ContDiff Topology

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  (F : ContinuousFinslerNorm E M)

/-- The infimum of actual lengths of C¹ paths measured by the given fiber lengths. -/
def lengthEDist (x y : M) : ℝ≥0∞ :=
  letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  riemannianEDist 𝓘(ℝ, E) x y

/-- Constant paths have zero length. -/
@[simp] theorem lengthEDist_self (x : M) : F.lengthEDist x x = 0 := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let : ∀ y : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) y) := F.enormSMulClass
  exact riemannianEDist_self

/-- Reversibility of fiber length gives symmetry of the induced extended distance. -/
theorem lengthEDist_comm (x y : M) : F.lengthEDist x y = F.lengthEDist y x := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let : ∀ y : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) y) := F.enormSMulClass
  exact riemannianEDist_comm

/-- Reparametrization and concatenation of admissible paths give the triangle inequality. -/
theorem lengthEDist_triangle (x y z : M) :
    F.lengthEDist x z ≤ F.lengthEDist x y + F.lengthEDist y z := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let : ∀ y : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) y) := F.enormSMulClass
  exact riemannianEDist_triangle

variable [FiniteDimensional ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- Near a chart center, length distance is bounded by model-space distance. -/
lemma eventually_edist_le_edist_extChartAt (x : M) :
    ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝 x,
    F.lengthEDist x y ≤ C * edist (extChartAt 𝓘(ℝ, E) x x) (extChartAt 𝓘(ℝ, E) x y) := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let : ∀ y : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) y) := F.enormSMulClass
  change ∃ C > (0 : ℝ≥0), ∀ᶠ y in 𝓝 x,
    riemannianEDist 𝓘(ℝ, E) x y ≤ C * edist (extChartAt 𝓘(ℝ, E) x x)
      (extChartAt 𝓘(ℝ, E) x y)
  /- To construct a path with controlled distance from `x` to `y`, we consider the segment from
  `extChartAt x x` to `extChartAt x y` in the chart, and we push it by `(extChartAt x).symm`. As
  the derivative of the latter is locally bounded, this only multiplies the length by a bounded
  amount. -/
  -- first start from a bound on the derivative
  rcases F.eventually_inverse_chart_bound x with ⟨C, C_pos, hC⟩
  refine ⟨C, C_pos, ?_⟩
  -- consider a small convex set around `extChartAt x x` where everything is controlled.
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      ball (extChartAt 𝓘(ℝ, E) x x) r ∩ range 𝓘(ℝ, E) ⊆ (extChartAt 𝓘(ℝ, E) x).target ∩
        {y | ∀ v : E,
          (F.toFun ⟨(extChartAt 𝓘(ℝ, E) x).symm y,
            mfderiv[range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) x).symm y v⟩ : ℝ≥0∞) ≤ C * ‖v‖ₑ} :=
    mem_nhdsWithin_iff.1 (inter_mem (extChartAt_target_mem_nhdsWithin x) hC)
  -- pull this set inside `M`: this is the set where we will get the estimate.
  have A : (extChartAt 𝓘(ℝ, E) x) ⁻¹' (ball (extChartAt 𝓘(ℝ, E) x x) r ∩ range 𝓘(ℝ, E)) ∈ 𝓝 x := by
    apply extChartAt_preimage_mem_nhds_of_mem_nhdsWithin (by simp)
    rw [inter_comm]
    exact inter_mem_nhdsWithin _ (ball_mem_nhds _ r_pos)
  -- consider `y` in this good set. Let `η` be the segment in the extended chart, and
  -- `γ` its composition with `(extChartAt x).symm`.
  filter_upwards [A, chart_source_mem_nhds E x] with y hy h'y
  let η := ContinuousAffineMap.lineMap (R := ℝ) (extChartAt 𝓘(ℝ, E) x x) (extChartAt 𝓘(ℝ, E) x y)
  set γ := (extChartAt 𝓘(ℝ, E) x).symm ∘ η
  -- by convexity, the whole segment between `extChartAt x x` and `extChartAt x y` is in the
  -- controlled set.
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' ((extChartAt 𝓘(ℝ, E) x).target ∩
        {y | ∀ v : E,
          (F.toFun ⟨(extChartAt 𝓘(ℝ, E) x).symm y,
            mfderiv[range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) x).symm y v⟩ : ℝ≥0∞) ≤ C * ‖v‖ₑ}) := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
     ← segment_eq_image_lineMap, η]
    apply Subset.trans _ hr
    exact ((convex_ball _ _).inter 𝓘(ℝ, E).convex_range).segment_subset (by simp [r_pos]) hy
  simp only [preimage_inter, subset_inter_iff] at hη
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  -- we can bound the length distance using the specific path `γ`.
  have : riemannianEDist 𝓘(ℝ, E) x y ≤ pathELength 𝓘(ℝ, E) γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth hη.1
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq, h'y]
  apply this.trans
  -- Finally, we control the length of `γ` thanks to the boundedness of the derivative of
  -- `(extChartAt x).symm` on the whole controlled set.
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have : mfderiv[Icc 0 1] γ t =
      (mfderiv[range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (hη.1 ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact hη.1.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range 𝓘(ℝ, E)] (extChartAt 𝓘(ℝ, E) x).symm (η t))
        (mfderiv[Icc 0 1] η t 1) := congr($this 1)
  rw [this]
  convert! hη.2 ht (mfderiv[Icc 0 1] η t 1) using 1
  simp only [mfderivWithin_eq_fderivWithin]
  rfl

/-- If points are close for the topology, then their length distance is small. -/
lemma eventually_lengthEDist_lt (x : M) {c : ℝ≥0∞} (hc : 0 < c) :
    ∀ᶠ y in 𝓝 x, F.lengthEDist x y < c := by
  rcases F.eventually_edist_le_edist_extChartAt x with ⟨C, C_pos, hC⟩
  have : (extChartAt 𝓘(ℝ, E) x) ⁻¹' (Metric.eball (extChartAt 𝓘(ℝ, E) x x) (c / C)) ∈ 𝓝 x := by
    apply (continuousAt_extChartAt x).preimage_mem_nhds
    exact Metric.eball_mem_nhds _ (ENNReal.div_pos hc.ne' (by simp))
  filter_upwards [this, hC] with y hy h'y
  apply h'y.trans_lt
  have : edist (extChartAt 𝓘(ℝ, E) x x) (extChartAt 𝓘(ℝ, E) x y) < c / C := by
    simpa only [mem_preimage, Metric.mem_eball'] using hy
  rwa [ENNReal.lt_div_iff_mul_lt, mul_comm] at this
  · exact Or.inl (mod_cast C_pos.ne')
  · simp

set_option backward.isDefEq.respectTransparency false in
/-- Any neighborhood of `x` contains all the points which are close enough to `x` for the
length distance, `ℝ≥0` version. -/
lemma lengthEDist_ball_subset_nhds [RegularSpace M] {x : M} {s : Set M} (hs : s ∈ 𝓝 x) :
    ∃ c > (0 : ℝ≥0), {y | F.lengthEDist x y < c} ⊆ s := by
  let : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let : ∀ y : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) y) := F.enormSMulClass
  /- Consider a closed neighborhood `u` of `x` on which the derivative of the extended chart is
  bounded by some `C`, contained in `s`, then an open neighborhood `v` of `x` inside `u`,
  and finally `r` small enough that the ball of radius `r` in the extended chart is contained in
  the image of `v`.

  We claim that points at length distance at most `r / C` of `x` are inside `u` (and therefore
  inside `s`). To prove this, consider a path of length at most `r / C` starting from `x`. While
  it stays inside `u`, then by the derivative control its image in the extended chart has length
  at most `r`, so it cannot exit the ball of radius `r`, which means that in the manifold it is
  inside `v` (which is strictly inside `u`). This means that the path will stay inside `u` for
  a little bit longer, by openness of `v`. Iterating this argument, it follows that the path will
  remain inside `u` for the whole time interval `[0, 1]`. In particular, its right endpoint is
  inside `u`, as desired.

  The formalization of this argument goes through the lemma
  `IsClosed.Icc_subset_of_forall_mem_nhdsGT_of_mem` which gives an induction-like principle over
  real intervals.
  -/
  -- first introduce a neighborhood where the derivative of the extended chart is bounded by `C`
  rcases F.eventually_chart_bound x with ⟨C, C_pos, hC⟩
  -- let `u` be a closed neighborhood, inside `s`, with the derivative control
  obtain ⟨u, u_mem, u_closed, us, hu, uc⟩ : ∃ u ∈ 𝓝 x, IsClosed u ∧ u ⊆ s
      ∧ u ⊆ {y | ∀ w : TangentSpace 𝓘(ℝ, E) y,
        ‖mfderiv% (extChartAt 𝓘(ℝ, E) x) y w‖ₑ ≤ C * (F.toFun ⟨y, w⟩ : ℝ≥0∞)}
      ∧ u ⊆ (extChartAt 𝓘(ℝ, E) x).source := by
    have := Filter.inter_mem (Filter.inter_mem hs hC) (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) x)
    rcases exists_mem_nhds_isClosed_subset this with ⟨u, u_mem, u_closed, hu⟩
    simp only [subset_inter_iff] at hu
    exact ⟨u, u_mem, u_closed, hu.1.1, hu.1.2, hu.2⟩
  have uc' : u ⊆ (chartAt E x).source := by simpa [extChartAt_source 𝓘(ℝ, E) x] using uc
  -- let `v` be a smaller open neighborhood, inside `u`.
  obtain ⟨v, ⟨v_mem, v_open⟩, hv⟩ : ∃ v, (v ∈ 𝓝 x ∧ IsOpen v) ∧ v ⊆ u :=
    (nhds_basis_opens' x).mem_iff.1 u_mem
  -- let `r > 0` be small enough that, in the extended chart, the ball of radius `r` is contained
  -- in the image of `v`.
  obtain ⟨r, r_pos, hr⟩ : ∃ r > 0,
      ball (extChartAt 𝓘(ℝ, E) x x) r ⊆ (extChartAt 𝓘(ℝ, E) x).symm ⁻¹' v :=
    Metric.mem_nhds_iff.1 (extChartAt_preimage_mem_nhds v_mem)
  lift r to ℝ≥0 using r_pos.le
  simp only [gt_iff_lt, NNReal.coe_pos] at r_pos
  -- the desired constant will be `c := r / C`
  refine ⟨r / C, by positivity, ?_⟩
  intro y hy
  change riemannianEDist 𝓘(ℝ, E) x y < (r / C : ℝ≥0) at hy
  -- consider a path `γ` of length `< r / C` from `x` to a point `y`. We will show that `y` belongs
  -- to `u`.
  rcases exists_lt_locally_constant_of_riemannianEDist_lt hy zero_lt_one
    with ⟨γ, hγx, hγy, γ_smooth, hγ, -⟩
  let A := γ ⁻¹' u
  have zero_mem : 0 ∈ A := by simpa  [hγx, A] using mem_of_mem_nhds u_mem
  have A_closed : IsClosed (A ∩ Icc 0 1) :=
    (u_closed.preimage γ_smooth.continuous).inter isClosed_Icc
  suffices Icc 0 1 ⊆ A by
    apply us
    have : 1 ∈ A := this ⟨zero_le_one, le_rfl⟩
    simpa [A, hγy, us]
  apply A_closed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset zero_mem
  rintro t₁ ⟨ht₁0, ht₁1⟩ t₁_mem
  suffices γ t₁ ∈ v from
    γ_smooth.continuous.continuousWithinAt <| mem_of_superset (v_open.mem_nhds this) hv
  let γ' := extChartAt 𝓘(ℝ, E) x ∘ γ
  have hC : CMDiff[Icc 0 t₁] 1 γ' :=
    contMDiffOn_extChartAt.comp (I' := 𝓘(ℝ, E)) (t := (chartAt E x).source)
      γ_smooth.contMDiffOn (fun t' ht' ↦ uc' <| t₁_mem ht')
  have : ‖γ' t₁ - γ' 0‖ₑ < r := by
    rcases ht₁0.eq_or_lt with rfl | h't'
    · simp [r_pos]
    calc
      ‖γ' t₁ - γ' 0‖ₑ
    _ ≤ ∫⁻ t' in Icc 0 t₁, ‖derivWithin γ' (Icc 0 t₁) t'‖ₑ := by
      apply enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc _ ht₁0
      rwa [← contMDiffOn_iff_contDiffOn]
    _ = ∫⁻ t' in Icc 0 t₁, ‖mfderiv[Icc 0 t₁] γ' t' 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t' in Icc 0 t₁, C * ‖mfderiv[Icc 0 t₁] γ t' 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc (fun t' ht' ↦ ?_)
      have : mfderiv[Icc 0 t₁] γ' t' =
          (mfderiv% (extChartAt 𝓘(ℝ, E) x) (γ t')) ∘L (mfderiv[Icc 0 t₁] γ t') := by
        apply mfderiv_comp_mfderivWithin
        · refine mdifferentiableAt_extChartAt (uc' ?_)
          apply t₁_mem ht'
        · exact (γ_smooth.mdifferentiable one_ne_zero).mdifferentiableOn _ ht'
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc h't' _ ht'
      have : mfderiv[Icc 0 t₁] γ' t' 1 =
          (mfderiv% (extChartAt 𝓘(ℝ, E) x) (γ t')) (mfderiv[Icc 0 t₁] γ t' 1) :=
        congr($this 1)
      rw [this]
      exact hu (t₁_mem ht') _
    _ = C * pathELength 𝓘(ℝ, E) γ 0 t₁ := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          pathELength_eq_lintegral_mfderivWithin_Icc]
    _ ≤ C * pathELength 𝓘(ℝ, E) γ 0 1 := by
      gcongr
    _ < C * (r / C) := by
      gcongr
      · exact ENNReal.coe_ne_top
      · exact hγ.trans_eq (ENNReal.coe_div C_pos.ne')
    _ = r := (ENNReal.eq_div_iff (by simpa using C_pos.ne') ENNReal.coe_ne_top).mp rfl
  have : γ' t₁ ∈ (extChartAt 𝓘(ℝ, E) x).symm ⁻¹' v := by
    apply hr
    rw [← Metric.eball_coe, Metric.mem_eball, edist_eq_enorm_sub]
    convert! this
    simp [γ', hγx]
  convert! mem_preimage.1 this
  simp only [Function.comp_apply, γ', (extChartAt 𝓘(ℝ, E) x).left_inv <| uc <| t₁_mem
    (right_mem_Icc.mpr ht₁0)]

/-- The actual length infimum equips the manifold with its original topology. -/
@[reducible] def pseudoEMetricSpace [RegularSpace M] : PseudoEMetricSpace M :=
  PseudoEMetricSpace.ofEDistOfTopology F.lengthEDist
    F.lengthEDist_self F.lengthEDist_comm F.lengthEDist_triangle
    (fun x ↦ (basis_sets (𝓝 x)).to_hasBasis'
      (fun _ hs ↦ by
        obtain ⟨c, hc, hsub⟩ := F.lengthEDist_ball_subset_nhds hs
        exact ⟨(c : ℝ≥0∞), by exact_mod_cast hc, hsub⟩)
      (fun _ hc ↦ F.eventually_lengthEDist_lt x hc))

/-- On a Hausdorff manifold the length infimum separates points, with unchanged topology. -/
@[reducible] def emetricSpace [T2Space M] : EMetricSpace M :=
  letI : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  letI : PseudoEMetricSpace M := F.pseudoEMetricSpace
  EMetricSpace.ofT0PseudoEMetricSpace M

/-- Distinct points have positive genuine length distance. -/
@[simp] theorem lengthEDist_eq_zero_iff [T2Space M] (x y : M) :
    F.lengthEDist x y = 0 ↔ x = y := by
  let : EMetricSpace M := F.emetricSpace
  change edist x y = 0 ↔ x = y
  exact edist_eq_zero

/-- Connectedness makes every actual length distance finite; no path existence is assumed. -/
theorem lengthEDist_lt_top [T2Space M] [PreconnectedSpace M] (x y : M) :
    F.lengthEDist x y < ⊤ := by
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace E M
  let : PseudoEMetricSpace M := F.pseudoEMetricSpace
  change edist x y < ⊤
  have hc : IsClopen (Metric.eball x ⊤) :=
    ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩
  have hall : Metric.eball x ⊤ = univ := hc.eq_univ ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hall]; trivial
  simpa only [Metric.mem_eball, edist_comm] using hy

/-- The genuine length metric on a connected Hausdorff manifold preserves its given topology. -/
@[reducible] def metricSpace [T2Space M] [PreconnectedSpace M] : MetricSpace M :=
  letI : EMetricSpace M := F.emetricSpace
  EMetricSpace.toMetricSpace (fun x y ↦ (F.lengthEDist_lt_top x y).ne)

/-- The constructed metric's extended distance is exactly the original path-length infimum. -/
theorem metricSpace_edist [T2Space M] [PreconnectedSpace M] (x y : M) :
    @edist M F.metricSpace.toEDist x y = F.lengthEDist x y := rfl

/-- The real distance is the finite real value of the same genuine length infimum. -/
theorem metricSpace_dist [T2Space M] [PreconnectedSpace M] (x y : M) :
    @dist M F.metricSpace.toDist x y = (F.lengthEDist x y).toReal := rfl

/-- The constructed metric preserves the original manifold topology definitionally. -/
theorem metricSpace_topology [T2Space M] [PreconnectedSpace M] :
    F.metricSpace.toUniformSpace.toTopologicalSpace = ‹TopologicalSpace M› := rfl

end OTSelector.Geometry.ContinuousFinslerNorm
