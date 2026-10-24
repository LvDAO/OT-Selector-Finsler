import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.ShortPath
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerChartLipschitz.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerChartLipschitz`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Coordinates.ChartLipschitz

* **Conditions:** A continuous Finsler fiber norm on a C1 manifold; the length-metric constructions supply their stated topological hypotheses.
* **Objects:** A chart displacement estimate for C1 paths and a local Lipschitz bound from the original Finsler distance to coordinates.
* **Proof detail:** Bound the chart differential by the fiber norm, integrate along near-minimizing paths, and use short-path confinement before taking the length infimum.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A weaker-regularity extension of the usual smooth Finsler local metric comparison; the all-near-minimizer confinement is a local proof ingredient.
-/

/-!
# Local chart Lipschitz bounds for the original Finsler length metric

The actual chart differential bound controls the displacement of C1 paths in a
small neighborhood. Near-minimizing paths for the original distance remain in
that neighborhood, giving a uniform Lipschitz constant for the chart itself.
No smoothness or strong convexity of the Finsler norm is needed.
-/

open Bundle Set MeasureTheory Manifold Filter Metric
open scoped NNReal ENNReal ContDiff Topology

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  (F : ContinuousFinslerNorm E M)

set_option backward.isDefEq.respectTransparency false in
private theorem chart_edist_le_pathELength_mul (x₀ : M) {U : Set M} {C : ℝ≥0}
    (hsource : U ⊆ (extChartAt 𝓘(ℝ, E) x₀).source)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v‖ₑ ≤
        C * (F.toFun ⟨x, v⟩ : ℝ≥0∞))
    {γ : ℝ → M} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 γ (Icc 0 1))
    (hmap : MapsTo γ (Icc 0 1) U) :
    let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    edist (extChartAt 𝓘(ℝ, E) x₀ (γ 0)) (extChartAt 𝓘(ℝ, E) x₀ (γ 1)) ≤
      C * Manifold.pathELength 𝓘(ℝ, E) γ 0 1 := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let η := extChartAt 𝓘(ℝ, E) x₀ ∘ γ
  have hη : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 η (Icc 0 1) :=
    contMDiffOn_extChartAt.comp (I' := 𝓘(ℝ, E)) (t := (chartAt E x₀).source) hγ (fun t ht ↦ by
      simpa only [extChartAt_source, mem_preimage] using hsource (hmap ht))
  calc
    edist (extChartAt 𝓘(ℝ, E) x₀ (γ 0)) (extChartAt 𝓘(ℝ, E) x₀ (γ 1))
        = ‖η 1 - η 0‖ₑ := by rw [edist_comm, edist_eq_enorm_sub]; rfl
    _ ≤ ∫⁻ t in Icc 0 1, ‖derivWithin η (Icc 0 1) t‖ₑ :=
      enorm_sub_le_lintegral_derivWithin_Icc_of_contDiffOn_Icc
        (by rwa [← contMDiffOn_iff_contDiffOn]) zero_le_one
    _ = ∫⁻ t in Icc 0 1, ‖mfderiv[Icc 0 1] η t 1‖ₑ := by
      simp_rw [← fderivWithin_derivWithin, mfderivWithin_eq_fderivWithin]
      rfl
    _ ≤ ∫⁻ t in Icc 0 1, C * ‖mfderiv[Icc 0 1] γ t 1‖ₑ := by
      apply setLIntegral_mono' measurableSet_Icc
      intro t ht
      have hd : mfderiv[Icc 0 1] η t =
          (mfderiv% (extChartAt 𝓘(ℝ, E) x₀) (γ t)) ∘L (mfderiv[Icc 0 1] γ t) := by
        apply mfderiv_comp_mfderivWithin
        · exact mdifferentiableAt_extChartAt (by
            simpa only [extChartAt_source, mem_preimage] using hsource (hmap ht))
        · exact hγ.mdifferentiableOn one_ne_zero t ht
        · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
          exact uniqueDiffOn_Icc zero_lt_one t ht
      rw [hd]
      exact hbound _ (hmap ht) _
    _ = C * Manifold.pathELength 𝓘(ℝ, E) γ 0 1 := by
      rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
        pathELength_eq_lintegral_mfderivWithin_Icc]

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

set_option backward.isDefEq.respectTransparency false in
/-- Every extended chart is Lipschitz on some open neighborhood of its center for the
original Finsler length metric. The neighborhood and constant are constructed from F. -/
theorem exists_lipschitzOnWith_extChartAt (x₀ : M) :
    let : MetricSpace M := F.metricSpace
    ∃ (U : Set M) (K : ℝ≥0), IsOpen U ∧ x₀ ∈ U ∧
      U ⊆ (extChartAt 𝓘(ℝ, E) x₀).source ∧
      LipschitzOnWith K (extChartAt 𝓘(ℝ, E) x₀) U := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  obtain ⟨C, hCpos, hC⟩ := F.eventually_chart_bound x₀
  let V : Set M := (extChartAt 𝓘(ℝ, E) x₀).source ∩
    {x | ∀ v : TangentSpace 𝓘(ℝ, E) x,
      ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀) x v‖ₑ ≤
        C * (F.toFun ⟨x, v⟩ : ℝ≥0∞)}
  have hV : V ∈ 𝓝 x₀ := inter_mem (extChartAt_source_mem_nhds (I := 𝓘(ℝ, E)) x₀) hC
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hV
  have hr : 0 < R / 4 := by positivity
  refine ⟨ball x₀ (R / 4), C, isOpen_ball, mem_ball_self hr,
    fun y hy ↦ (hball (ball_subset_ball (by linarith) hy)).1, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro y hy z hz
  have hy' : dist y x₀ < R / 4 := hy
  have hz' : dist z x₀ < R / 4 := hz
  have hyz : dist y z < R / 2 := by
    have := dist_triangle y x₀ z
    rw [dist_comm x₀ z] at this
    linarith
  by_contra hn
  have hbad : (C : ℝ) * dist y z <
      dist (extChartAt 𝓘(ℝ, E) x₀ y) (extChartAt 𝓘(ℝ, E) x₀ z) := lt_of_not_ge hn
  have hCpos' : (0 : ℝ) < C := hCpos
  have hlt : dist y z < min (R / 2)
      (dist (extChartAt 𝓘(ℝ, E) x₀ y) (extChartAt 𝓘(ℝ, E) x₀ z) / C) := by
    refine lt_min hyz ?_
    rw [lt_div_iff₀ hCpos']
    simpa only [mul_comm] using hbad
  obtain ⟨l, hdl, hl⟩ := exists_between hlt
  have hlR : l < R / 2 := hl.trans_le (min_le_left _ _)
  have hcl : (C : ℝ) * l <
      dist (extChartAt 𝓘(ℝ, E) x₀ y) (extChartAt 𝓘(ℝ, E) x₀ z) := by
    have h := hl.trans_le (min_le_right _ _)
    rw [lt_div_iff₀ hCpos'] at h
    simpa only [mul_comm] using h
  have hdist : F.lengthEDist y z < ENNReal.ofReal l := by
    change edist y z < ENNReal.ofReal l
    rw [edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := y) (y := z)]) |>.2 hdl
  obtain ⟨γ, hγ0, hγ1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hdist
  have hmap : MapsTo γ (Icc 0 1) V := by
    intro t ht
    apply hball
    have hp : edist y (γ t) < ENNReal.ofReal l := by
      rw [← hγ0]
      exact (F.lengthEDist_le_pathELength_of_mem_Icc hγ ht).trans_lt hlen
    have hpt : dist y (γ t) < l := by
      rw [edist_dist] at hp
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [dist_nonneg (x := y) (y := z)])).1 hp
    change dist (γ t) x₀ < R
    have := dist_triangle (γ t) y x₀
    rw [dist_comm (γ t) y] at this
    linarith
  have hbound := F.chart_edist_le_pathELength_mul x₀ (fun _ hv ↦ hv.1)
    (fun _ hv ↦ hv.2) hγ hmap
  rw [hγ0, hγ1] at hbound
  have hmul : (C : ℝ≥0∞) * Manifold.pathELength 𝓘(ℝ, E) γ 0 1 <
      C * ENNReal.ofReal l :=
    by
      simpa only [mul_comm] using
        ENNReal.mul_lt_mul_left (by exact_mod_cast hCpos.ne') ENNReal.coe_ne_top hlen
  have hsmall : (C : ℝ≥0∞) * ENNReal.ofReal l <
      edist (extChartAt 𝓘(ℝ, E) x₀ y) (extChartAt 𝓘(ℝ, E) x₀ z) := by
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg, edist_dist]
    exact ENNReal.ofReal_lt_ofReal_iff (by linarith [mul_nonneg C.coe_nonneg (le_of_lt (lt_of_le_of_lt dist_nonneg hdl))]) |>.2 hcl
  exact (lt_irrefl _ (hbound.trans_lt (hmul.trans hsmall)))

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
