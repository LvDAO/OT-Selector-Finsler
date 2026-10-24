import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Riemannian.PathELength
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Compact
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Calibration.LocalMinimality
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.TangentChartCurve

/-!
## Lemma skeleton

* **Conditions:** A C1 chart curve with image in a chart target, a C1 coordinate potential with du(v) ≤ F(v), and equality along the curve; finite dimension and regularity only for local minimality.
* **Objects:** The actual manifold curve reconstructed by the inverse chart, its genuine tangent velocity, the pulled-back potential and locally minimizing subsegments.
* **Proof detail:** Apply inverse-chart differentiation and the chain rule to identify velocity and speed. Transfer the differential bound and saturation, then apply the short calibrated-curve comparison.

## Mathematical sources

* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II*, Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
  https://www.jirka.org/ra/realanal2.pdf
* J. C. Álvarez Paiva; A. C. Thompson, *Volumes on Normed and Finsler Spaces, MSRI Publications 50 (2004)*, Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
  https://library.slmath.org/books/Book50/files/02AT.pdf#page=22
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** Chart implementation of the one-dimensional exact-form calibration principle. No calibration is assumed to exist without being supplied.
-/

/-!
# Calibrated coordinate curves as actual manifold curves

An actual C1 coordinate curve in a chart reconstructs an actual C1 manifold curve. Its
coordinate tangent is its genuine ordinary derivative, and its Finsler speed is exactly
the original length in that tangent chart. Consequently a supplied coordinate calibration
and its saturation produce a genuine manifold calibration and saturated curve.

In finite dimension, the existing short-path argument then constructs a time neighborhood
on which every ordered subsegment realizes the original Finsler length distance. This module
supplies the chart conversion; the coordinate calibration itself remains an explicit input.
-/

open Bundle Set Manifold Filter
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

set_option backward.isDefEq.respectTransparency false in
/-- The actual chart differential of the reconstructed curve's tangent is its coordinate
velocity. Both derivatives are genuine derivatives, derived by inverse-chart calculus. -/
theorem mfderiv_extChartAt_chartCurve (x₀ : M) {γ : ℝ → E} {t : ℝ} {v : E}
    (hγ : γ t ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (hdγ : HasDerivAt γ v t) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀)
      ((extChartAt 𝓘(ℝ, E) x₀).symm (γ t))
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ) t 1) = v := by
  have hi : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E)
      (extChartAt 𝓘(ℝ, E) x₀).symm (γ t) := by
    simpa only [modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      mdifferentiableWithinAt_extChartAt_symm hγ
  rw [mfderiv_comp t hi hdγ.differentiableAt.mdifferentiableAt]
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀)
    ((extChartAt 𝓘(ℝ, E) x₀).symm (γ t))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (γ t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)) = v
  have hvel : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 = v := by
    rw [mfderiv_eq_fderiv]
    exact (fderiv_apply_one_eq_deriv (𝕜 := ℝ) (f := γ) (x := t)).trans hdγ.deriv
  have hinv := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hγ
  simp only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] at hinv
  exact (congrArg (fun w : E ↦
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀)
      ((extChartAt 𝓘(ℝ, E) x₀).symm (γ t))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀).symm (γ t) w)) hvel).trans
    (congrArg (fun A : E →L[ℝ] E ↦ A v) hinv)

/-- The actual speed of the reconstructed manifold curve is its original chart length. -/
theorem toFun_chartCurve_velocity (F : ContinuousFinslerNorm E M) (x₀ : M)
    {γ : ℝ → E} {t : ℝ} {v : E}
    (hγ : γ t ∈ (extChartAt 𝓘(ℝ, E) x₀).target) (hdγ : HasDerivAt γ v t) :
    F.toFun ⟨((extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ) t,
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ) t 1⟩ =
        F.chartLength x₀ (γ t, v) := by
  change F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E)
    ((extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ) ⟨t, (1 : ℝ)⟩) = _
  rw [tangentMap_chart_symm_curve x₀ hγ hdγ]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A coordinate calibration and its saturated coordinate curve give an actual manifold
calibration and saturated C1 curve on the explicit pullback domain. -/
theorem chartCurve_calibrated (F : ContinuousFinslerNorm E M) (x₀ : M)
    {V : Set E} {u : E → ℝ} (hV : IsOpen V)
    (hsub : V ⊆ (extChartAt 𝓘(ℝ, E) x₀).target) (hu : ContDiffOn ℝ 1 u V)
    (hbound : ∀ y ∈ V, ∀ w : E, fderiv ℝ u y w ≤ (F.chartLength x₀ (y, w) : ℝ))
    {γ : ℝ → E} {S : Set ℝ} (hS : IsOpen S) (hγ : ContDiffOn ℝ 1 γ S)
    (hmap : MapsTo γ S V)
    (hsat : ∀ t ∈ S, fderiv ℝ u (γ t) (deriv γ t) =
      (F.chartLength x₀ (γ t, deriv γ t) : ℝ)) :
    let U := chartCalibrationDomain x₀ V
    let c := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ
    let uM := u ∘ extChartAt 𝓘(ℝ, E) x₀
    IsOpen U ∧ ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) 1 uM U ∧
      (∀ x ∈ U, ∀ v : TangentSpace 𝓘(ℝ, E) x,
        @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) uM x v) (F.toFun ⟨x, v⟩ : ℝ)) ∧
      ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c S ∧ MapsTo c S U ∧
      ∀ t ∈ S, mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) uM (c t)
          (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1) =
        (F.toFun ⟨c t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1⟩ : ℝ) := by
  let c := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ
  have hct : MapsTo c S (chartCalibrationDomain x₀ V) := fun t ht ↦
    chart_symm_mem_chartCalibrationDomain x₀ (hsub (hmap ht)) (hmap ht)
  refine ⟨isOpen_chartCalibrationDomain x₀ hV, contMDiffOn_chartPullback x₀ hu,
    fun x hx v ↦ F.mfderiv_chartPullback_le x₀ hV hu hbound hx v,
    (contMDiffOn_extChartAt_symm x₀).comp hγ.contMDiffOn (fun t ht ↦ hsub (hmap ht)),
    hct, ?_⟩
  intro t ht
  have hdγ := (hγ.contDiffAt (hS.mem_nhds ht)).differentiableAt one_ne_zero |>.hasDerivAt
  rw [mfderiv_chartPullback_apply x₀ hV hu (hct ht)]
  change fderiv ℝ u (extChartAt 𝓘(ℝ, E) x₀ ((extChartAt 𝓘(ℝ, E) x₀).symm (γ t)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) x₀)
        ((extChartAt 𝓘(ℝ, E) x₀).symm (γ t))
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c t 1)) = _
  dsimp only [c]
  rw [mfderiv_extChartAt_chartCurve x₀ (hsub (hmap ht)) hdγ,
    (extChartAt 𝓘(ℝ, E) x₀).right_inv (hsub (hmap ht)), hsat t ht]
  exact congrArg (fun s : ℝ≥0 ↦ (s : ℝ))
    (F.toFun_chartCurve_velocity x₀ (hsub (hmap ht)) hdγ).symm

/-- A coordinate-calibrated curve realizes original Finsler distance between every ordered
pair of times in a constructed positive time neighborhood. -/
theorem exists_local_minimality_chartCurve_of_calibrated
    [FiniteDimensional ℝ E] [RegularSpace M] (F : ContinuousFinslerNorm E M) (x₀ : M)
    {V : Set E} {u : E → ℝ} (hV : IsOpen V)
    (hsub : V ⊆ (extChartAt 𝓘(ℝ, E) x₀).target) (hu : ContDiffOn ℝ 1 u V)
    (hbound : ∀ y ∈ V, ∀ w : E, fderiv ℝ u y w ≤ (F.chartLength x₀ (y, w) : ℝ))
    {γ : ℝ → E} {S : Set ℝ} {t₀ : ℝ} (hS : IsOpen S) (ht₀ : t₀ ∈ S)
    (hγ : ContDiffOn ℝ 1 γ S) (hmap : MapsTo γ S V)
    (hsat : ∀ t ∈ S, fderiv ℝ u (γ t) (deriv γ t) =
      (F.chartLength x₀ (γ t, deriv γ t) : ℝ)) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    let c := (extChartAt 𝓘(ℝ, E) x₀).symm ∘ γ
    ∃ δ : ℝ, 0 < δ ∧ Icc (t₀ - δ) (t₀ + δ) ⊆ S ∧
      ∀ s ∈ Icc (t₀ - δ) (t₀ + δ), ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), s ≤ t →
        F.lengthEDist (c s) (c t) = Manifold.pathELength 𝓘(ℝ, E) c s t := by
  obtain ⟨hU, huM, hboundM, hc, hmapM, hsatM⟩ :=
    F.chartCurve_calibrated x₀ hV hsub hu hbound hS hγ hmap hsat
  exact F.exists_local_minimality_of_calibrated hU huM hboundM hS ht₀ hc hmapM hsatM

end OTSelector.Geometry.ContinuousFinslerNorm
