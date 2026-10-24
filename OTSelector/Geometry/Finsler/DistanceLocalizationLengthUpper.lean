import OTSelector.Analysis.Calculus.MetricPotentialContact
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.LengthHessian
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationLengthUpper.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationLengthUpper`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationLengthUpper

* **Conditions:** A compact subset of the actual slit chart phase and smooth strong convexity.
* **Objects:** One uniform radius/Hessian constant giving a quadratic upper Taylor bound, and its unit normal-direction specialization.
* **Proof detail:** Bound the actual length Hessian on a compact legal neighborhood, apply the one-dimensional Taylor bound on velocity segments and remove the linear term by momentum normality.

Mathematical sources:
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_taylor.html): Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=2): Section 2, pp. 304–305: positive homogeneity, slit smoothness, positive fundamental tensor gy=½∂²F² and F(y)²=gy(y,y).

Source relation (derived): A uniform compact Taylor consequence; the original length Hessian and actual normal pairing determine the bound.
-/

/-!
# Uniform upper bounds for actual Finsler length in normal directions

Compactness inside the original slit chart produces a legal neighborhood and a
bound for the actual length Hessian. Its Taylor remainder controls every small
velocity perturbation, including along Lipschitz competitor paths.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- A compact set of actual nonzero chart velocities has one quadratic Taylor
upper bound for the original length, uniformly over its base points. -/
theorem exists_uniform_chartLength_quadratic_upper
    (hF : F.IsSmoothStronglyConvex) (old : M) {P : Set (E × E)}
    (hP : IsCompact P) (hPD : P ⊆ chartEnergyDomain old) :
    ∃ r > 0, ∃ C : ℝ≥0, ∀ q ∈ P, ∀ ξ : E, ‖ξ‖ ≤ r →
      (F.chartLength old (q.1, q.2 + ξ) : ℝ) ≤ (F.chartLength old q : ℝ) +
        fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) q ξ + (C : ℝ) * ‖ξ‖ ^ 2 := by
  let L := fun z ↦ (F.chartLength old z : ℝ)
  have hD := isOpen_chartEnergyDomain (E := E) old
  have hL := hF.contDiffOn_chartLength old
  obtain ⟨r, hr, hsub⟩ := hP.exists_cthickening_subset_open hD hPD
  have hQ : IsCompact (cthickening r P) := hP.cthickening
  have hH : ContinuousOn (fderiv ℝ (fderiv ℝ L)) (chartEnergyDomain old) :=
    (hL.fderiv_of_isOpen hD (m := 1) (by simp)).continuousOn_fderiv_of_isOpen hD le_rfl
  let _instHessianNorm : NormedAddCommGroup ((E × E) →L[ℝ] (E × E) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let _instHessianSpace : NormedSpace ℝ ((E × E) →L[ℝ] (E × E) →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedSpace
  obtain ⟨C₀, hC₀⟩ := hQ.exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ L)) (hH.mono hsub)
  let C : ℝ≥0 := ⟨max C₀ 0, le_max_right _ _⟩
  refine ⟨r, hr, C, ?_⟩
  intro q hq ξ hξ
  have hball : closedBall q r ⊆ chartEnergyDomain old := by
    intro z hz
    exact hsub (mem_cthickening_of_dist_le z q r P hq (mem_closedBall.mp hz))
  have hz : (q.1, q.2 + ξ) ∈ closedBall q r := by
    simpa [mem_closedBall, dist_eq_norm, Prod.norm_def] using hξ
  have hrem := norm_linear_remainder_le_of_hessian_bound (f := L)
    (convex_closedBall q r)
    (fun z hz ↦ (hL.contDiffAt (hD.mem_nhds (hball hz))).differentiableAt (by simp))
    (fun z hz ↦ ((hL.fderiv_of_isOpen hD (m := 1) (by simp)).contDiffAt
      (hD.mem_nhds (hball hz))).differentiableAt one_ne_zero)
    C.coe_nonneg (fun z hz ↦ (hC₀ z
      (mem_cthickening_of_dist_le z q r P hq (mem_closedBall.mp hz))).trans
        (le_max_left _ _)) (mem_closedBall_self hr.le) hz
  have hd : DifferentiableAt ℝ L q := (hL.contDiffAt (hD.mem_nhds (hPD hq))).differentiableAt
    (by simp)
  have hi : HasFDerivAt (fun v : E ↦ (q.1, v))
      ((0 : E →L[ℝ] E).prod (ContinuousLinearMap.id ℝ E)) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have hpart := congrArg (fun A : E →L[ℝ] ℝ ↦ A ξ) (hd.hasFDerivAt.comp q.2 hi).fderiv
  have hstep : (q.1, q.2 + ξ) - q = (0, ξ) := by ext <;> simp
  rw [hstep] at hrem
  have hlin : fderiv ℝ L q (0, ξ) = fiberLegendre L q ξ := hpart.symm
  rw [hlin] at hrem
  have hb := (abs_le.mp hrem).2
  simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at hb
  change L (q.1, q.2 + ξ) ≤ L q + fiberLegendre L q ξ + (C : ℝ) * ‖ξ‖ ^ 2
  linarith

/-- The same produced constants control all unit velocities and their actual
conormal perturbations. No differentiability of a selected family is assumed. -/
theorem exists_uniform_normal_chartLength_upper
    (hF : F.IsSmoothStronglyConvex) (old : M) {P : Set (E × E)}
    (hP : IsCompact P) (hPD : P ⊆ chartEnergyDomain old) :
    ∃ r > 0, ∃ C : ℝ≥0, ∀ q ∈ P, (F.chartLength old q : ℝ) = 1 →
      ∀ ξ : E, ‖ξ‖ ≤ r →
        fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) q ξ = 0 →
        (F.chartLength old (q.1, q.2 + ξ) : ℝ) ≤ 1 + (C : ℝ) * ‖ξ‖ ^ 2 := by
  obtain ⟨r, hr, C, hb⟩ := hF.exists_uniform_chartLength_quadratic_upper old hP hPD
  refine ⟨r, hr, C, fun q hq hunit ξ hξ hnormal ↦ ?_⟩
  simpa only [hunit, hnormal, add_zero] using hb q hq ξ hξ

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
