import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteTimeLipschitz
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Coordinates.InverseChartLipschitz
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationC11Map.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationC11Map`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationC11Map

* **Conditions:** An actual complete C1,1 seed family with original momentum identity and compact state–time parameter sets, optionally composed with a Lipschitz level seed.
* **Objects:** Uniform actual-metric Lipschitz bounds for the same complete family, including label–time restrictions.
* **Proof detail:** Transfer local C1,1 chart estimates through the actual inverse chart, combine them over the compact set and compose the level seed.

Mathematical sources:
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=56): Section 2.4, pp. 45–47, equations (2.46)–(2.50), Theorem 2.10.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): The result remains valid with position folds and does not replace the original family by a local flow witness.
-/

/-!
# Actual-metric Lipschitz bounds for complete C1,1 seed families

The existing local chart estimates are transferred through the actual inverse
chart and combined on compact seed-time sets. This applies to the original
complete family even when its position map has folds.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- A compact part of the original complete C1,1 family is jointly Lipschitz
in the actual distance, without assuming a common output chart or injectivity. -/
theorem exists_lipschitzOnWith_C11_family_on_compact
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {U : Set E} (hU : IsOpen U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M}
    (hΓ : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x ∧
      F.IsEulerLagrangeOn (Γ x) univ ∧
      F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {P : Set (E × ℝ)} (hP : IsCompact P) (hPU : P ⊆ U ×ˢ univ) :
    let _inst : MetricSpace M := F.metricSpace
    ∃ C : ℝ≥0, LipschitzOnWith C (fun q : E × ℝ ↦ Γ q.1 q.2) P := by
  let : MetricSpace M := F.metricSpace
  apply LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hP
  intro q hq
  let terminal := Γ q.1 q.2
  let χ := extChartAt 𝓘(ℝ, E) terminal
  let read := fun z : E × ℝ ↦ χ (Γ z.1 z.2)
  obtain ⟨r, C, hr, _, hmap, hread⟩ :=
    hF.exists_joint_lipschitz_chart_readout_of_C11_initial_momentum hcomplete initial
      hG hLip hU hUt (fun x hx ↦ (hΓ x hx).2.1) (fun x hx ↦ (hΓ x hx).1)
      (fun x hx ↦ (hΓ x hx).2.2) (hPU hq).1 terminal q.2
      (mem_extChartAt_source terminal)
  obtain ⟨s, D, hs, _, hχ⟩ := F.exists_lipschitzOnWith_extChartAt_symm terminal
  have hc : ContinuousAt read q :=
    (hread.continuousOn q (mem_closedBall_self hr.le)).continuousAt (closedBall_mem_nhds q hr)
  let T := closedBall q r ∩ read ⁻¹' ball (χ terminal) s
  have hT : T ∈ 𝓝 q := inter_mem (closedBall_mem_nhds q hr)
    (hc.preimage_mem_nhds (ball_mem_nhds _ hs))
  have hcomp := hχ.comp (hread.mono (show T ⊆ closedBall q r from inter_subset_left))
    (show MapsTo read T (ball (χ terminal) s) from fun z hz ↦ hz.2)
  refine ⟨D * C, T, nhdsWithin_le_nhds hT, ?_⟩
  intro z hz w hw
  have hh := hcomp hz hw
  change edist (χ.symm (χ (Γ z.1 z.2))) (χ.symm (χ (Γ w.1 w.2))) ≤ _ at hh
  simpa only [χ.left_inv (hmap hz.1), χ.left_inv (hmap hw.1)] using hh

omit [NormedSpace ℝ W] in
/-- Every actual compact level section supplies a whole-time Lipschitz physical
parameter map for the original family; this is the map used by volume estimates. -/
theorem exists_lipschitzOnWith_C11_level_family
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (initial : M)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    {U : Set E} (hU : IsOpen U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
    {Γ : E → ℝ → M}
    (hΓ : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x ∧
      F.IsEulerLagrangeOn (Γ x) univ ∧
      F.chartMomentumFamily initial Γ (x, 0) = (x, fderiv ℝ G x))
    {K : Set W} (hK : IsCompact K) {σ : W → E} {B : ℝ≥0}
    (hσ : LipschitzOnWith B σ K) (hσU : MapsTo σ K U) (lo hi : ℝ) :
    let _inst : MetricSpace M := F.metricSpace
    ∃ C : ℝ≥0, LipschitzOnWith C (fun q : W × ℝ ↦ Γ (σ q.1) q.2) (K ×ˢ Icc lo hi) := by
  let : MetricSpace M := F.metricSpace
  have hP : IsCompact ((σ '' K) ×ˢ Icc lo hi) :=
    (hK.image_of_continuousOn hσ.continuousOn).prod isCompact_Icc
  have hPU : (σ '' K) ×ˢ Icc lo hi ⊆ U ×ˢ univ := by
    intro q hq
    obtain ⟨w, hw, heq⟩ := hq.1
    exact ⟨heq ▸ hσU hw, mem_univ _⟩
  obtain ⟨C, hC⟩ := hF.exists_lipschitzOnWith_C11_family_on_compact hcomplete initial
    hG hLip hU hUt hΓ hP hPU
  have hparam : LipschitzOnWith (max (B * 1) 1) (fun q : W × ℝ ↦ (σ q.1, q.2))
      (K ×ˢ Icc lo hi) :=
    (hσ.comp LipschitzWith.prod_fst.lipschitzOnWith (fun q hq ↦ hq.1)).prodMk
      LipschitzWith.prod_snd.lipschitzOnWith
  exact ⟨C * max (B * 1) 1, hC.comp hparam
    (fun q hq ↦ ⟨mem_image_of_mem σ hq.1, hq.2⟩)⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
