import OTSelector.Analysis.Calculus.AffineEndpointVariation
import OTSelector.Analysis.Calculus.Variational.CompactSmoothIntegral
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerEnergy
import OTSelector.Geometry.Finsler.LengthAction
import OTSelector.Geometry.Finsler.LengthHessian
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.EndpointLengthSupport

* **Conditions:** An actual C1 chart path; smooth slit regularity for endpoint perturbations and a minimizing or isometric central segment for touching.
* **Objects:** Smooth upper supports of actual endpoint distance obtained from true perturbed path lengths.
* **Proof detail:** Perturb the endpoint affinely inside the actual slit chart, integrate smooth length and compare with the original distance infimum.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=249): Section 8.3, pp. 238–240, equations (8.33)–(8.47): first variation, Euler–Lagrange, Legendre transformation, Hamilton equations and energy conservation.

Source relation (derived): No endpoint nonconjugacy or prior distance smoothness is assumed.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerEndpointLengthSupport.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerEndpointLengthSupport`; the selected original proof blocks follow. -/
section

/-!
# Smooth upper supports from actual endpoint-variable original lengths

An actual chart path gives an upper bound for the original length distance. A smooth
endpoint perturbation inside the original slit tangent domain makes that path length
smooth in its endpoint. At a central minimizing segment it touches the actual distance.
No original-distance regularity or endpoint nonconjugacy is assumed.
-/

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]

/-- A legal C1 chart path bounds original distance by its actual original length integral. -/
theorem dist_chart_le_integral_chartLength (F : ContinuousFinslerNorm E M) (old : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ 1 x I)
    {a b : ℝ} (hab : a ≤ b) (hseg : Icc a b ⊆ I)
    (hbase : ∀ t ∈ Icc a b, x t ∈ (extChartAt 𝓘(ℝ, E) old).target) :
    let _instEndpointLengthBoundMetric : MetricSpace M := F.metricSpace
    dist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
      ((extChartAt 𝓘(ℝ, E) old).symm (x b)) ≤
        ∫ t in a..b, (F.chartLength old (x t, deriv x t) : ℝ) := by
  let _instEndpointLengthBoundMetric : MetricSpace M := F.metricSpace
  let _instEndpointLengthBoundENorm : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  let _instEndpointLengthBoundSMul : ∀ y : M, ENormSMulClass ℝ
      (TangentSpace 𝓘(ℝ, E) y) := F.enormSMulClass
  have hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1
      ((extChartAt 𝓘(ℝ, E) old).symm ∘ x) (Icc a b) :=
    (contMDiffOn_extChartAt_symm old).comp (hx.contMDiffOn.mono hseg) hbase
  have hb := Manifold.riemannianEDist_le_pathELength hc rfl rfl hab
  rw [F.pathELength_chart_eq old hI hx hab hseg hbase] at hb
  change edist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
    ((extChartAt 𝓘(ℝ, E) old).symm (x b)) ≤ _ at hb
  rw [edist_dist] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (intervalIntegral.integral_nonneg hab
    (fun t _ ↦ NNReal.coe_nonneg _))).mp hb


/-- Original length of the actual affine endpoint perturbation, written in its genuine chart. -/
def chartEndpointLengthSupport (F : ContinuousFinslerNorm E M) (old : M)
    (x : ℝ → E) (a b : ℝ) (z : E) : ℝ :=
  ∫ t in a..b, (F.chartLength old (affineEndpointPhase x a b (z, t)) : ℝ)

namespace IsSmoothStronglyConvex

variable {F : ContinuousFinslerNorm E M}

/-- A smooth legal slit chart path that actually minimizes original length constructs a
smooth upper support of the original endpoint distance. The support is the length of the
actual affine endpoint perturbation; original-distance smoothness is not assumed. -/
theorem exists_smooth_endpointLengthSupport (hF : F.IsSmoothStronglyConvex) (old : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I)
    {a b : ℝ} (hab : a < b) (hseg : Icc a b ⊆ I)
    (htrace : ∀ t ∈ Icc a b, (x t, deriv x t) ∈ chartEnergyDomain old)
    (hmin : let _instCentralLengthSupportENorm :
        ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
      F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
        ((extChartAt 𝓘(ℝ, E) old).symm (x b)) =
      pathELength 𝓘(ℝ, E) ((extChartAt 𝓘(ℝ, E) old).symm ∘ x) a b) :
    let _instSmoothLengthSupportMetric : MetricSpace M := F.metricSpace
    ∃ U : Set E, IsOpen U ∧ x b ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ContDiffOn ℝ ∞ (F.chartEndpointLengthSupport old x a b) U ∧
      (∀ z ∈ U, dist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
        ((extChartAt 𝓘(ℝ, E) old).symm z) ≤ F.chartEndpointLengthSupport old x a b z) ∧
      F.chartEndpointLengthSupport old x a b (x b) =
        dist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
          ((extChartAt 𝓘(ℝ, E) old).symm (x b)) := by
  let _instSmoothLengthSupportMetric : MetricSpace M := F.metricSpace
  let _instSmoothLengthSupportENorm : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  obtain ⟨U, V, hU, hxb, hV, hIV, hVI, hphase⟩ :=
    exists_affineEndpointVariation_strip hI hx hseg (isOpen_chartEnergyDomain old) htrace
  have hpath (z : E) : ContDiffOn ℝ 1
      (fun t ↦ affineEndpointVariation x a b (z, t)) V :=
    ((contDiffOn_affineEndpointVariation hx a b).comp
      (contDiffOn_const.prodMk contDiffOn_id) (fun t ht ↦ ⟨mem_univ _, hVI ht⟩)).of_le
        (by simp)
  have hderiv (z : E) (t : ℝ) (ht : t ∈ V) :
      deriv (fun s ↦ affineEndpointVariation x a b (z, s)) t =
        (affineEndpointPhase x a b (z, t)).2 :=
    (hasDerivAt_affineEndpointVariation
      ((hx.contDiffAt (hI.mem_nhds (hVI ht))).differentiableAt (by simp)) z).deriv
  have hbase (z : E) (hz : z ∈ U) (t : ℝ) (ht : t ∈ Icc a b) :
      affineEndpointVariation x a b (z, t) ∈ (extChartAt 𝓘(ℝ, E) old).target :=
    (hphase ⟨hz, hIV ht⟩).1
  have hsmooth : ContDiffOn ℝ ∞
      (fun q : E × ℝ ↦ (F.chartLength old (affineEndpointPhase x a b q) : ℝ))
      (U ×ˢ V) :=
    (hF.contDiffOn_chartLength old).comp
      ((contDiffOn_affineEndpointPhase hI hx a b).mono
        (fun q hq ↦ ⟨mem_univ _, hVI hq.2⟩)) hphase
  have hS (z : E) : F.chartEndpointLengthSupport old x a b z =
      ∫ t in a..b, (F.chartLength old (affineEndpointVariation x a b (z, t),
        deriv (fun s ↦ affineEndpointVariation x a b (z, s)) t) : ℝ) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab.le] at ht
    dsimp only
    rw [hderiv z t (hIV ht)]
    rfl
  refine ⟨U, hU, hxb, ?_, ?_, ?_, ?_⟩
  · intro z hz
    have hh := hbase z hz b (right_mem_Icc.mpr hab.le)
    rwa [(affineEndpointVariation_endpoints x hab z).2] at hh
  · exact contDiffOn_infty_intervalIntegral_of_contDiffOn hU (hU.prod hV) hsmooth hab.le
      (fun z hz t ht ↦ ⟨hz, hIV ht⟩)
  · intro z hz
    have hb := F.dist_chart_le_integral_chartLength old hV (hpath z) hab.le hIV (hbase z hz)
    simpa only [(affineEndpointVariation_endpoints x hab z).1,
      (affineEndpointVariation_endpoints x hab z).2, ← hS z] using hb
  · have hp := F.pathELength_chart_eq old hI (hx.of_le (by simp)) hab.le hseg
      (fun t ht ↦ (htrace t ht).1)
    have hnonneg : 0 ≤ ∫ t in a..b, (F.chartLength old (x t, deriv x t) : ℝ) :=
      intervalIntegral.integral_nonneg hab.le (fun t _ ↦ NNReal.coe_nonneg _)
    change F.chartEndpointLengthSupport old x a b (x b) = (F.lengthEDist _ _).toReal
    rw [hmin, hp, ENNReal.toReal_ofReal hnonneg]
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [affineEndpointPhase_center]

/-- For an actual original-distance isometric central segment, the same smooth support
is constructed without supplying any distance/action identity. Original minimality is derived. -/
theorem exists_smooth_endpointLengthSupport_of_isometry
    (hF : F.IsSmoothStronglyConvex) (old : M)
    {x : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hx : ContDiffOn ℝ ∞ x I)
    {a b : ℝ} (hab : a < b) (hseg : Icc a b ⊆ I)
    (htrace : ∀ t ∈ Icc a b, (x t, deriv x t) ∈ chartEnergyDomain old)
    (hiso : let _instIsometricLengthSupportMetric : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ (extChartAt 𝓘(ℝ, E) old).symm (x t))) :
    let _instIsometricLengthSupportMetric : MetricSpace M := F.metricSpace
    ∃ U : Set E, IsOpen U ∧ x b ∈ U ∧ U ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ContDiffOn ℝ ∞ (F.chartEndpointLengthSupport old x a b) U ∧
      (∀ z ∈ U, dist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
        ((extChartAt 𝓘(ℝ, E) old).symm z) ≤ F.chartEndpointLengthSupport old x a b z) ∧
      F.chartEndpointLengthSupport old x a b (x b) =
        dist ((extChartAt 𝓘(ℝ, E) old).symm (x a))
          ((extChartAt 𝓘(ℝ, E) old).symm (x b)) := by
  apply hF.exists_smooth_endpointLengthSupport old hI hx hab hseg htrace
  let _instIsometricSupportENorm : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  exact hF.lengthEDist_eq_pathELength_of_isometric_interval
    (c := (extChartAt 𝓘(ℝ, E) old).symm ∘ x) hab.le hiso

end IsSmoothStronglyConvex
end OTSelector.Geometry.ContinuousFinslerNorm

end
end
