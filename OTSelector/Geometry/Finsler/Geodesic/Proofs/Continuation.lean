import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Extend
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
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.ExtendFrom
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.UniformSpace.Cauchy
import OTSelector.Analysis.CompactODEContinuation
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Energy.Compact
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeEnergy
import OTSelector.Geometry.Finsler.Hamiltonian.EulerLagrangeVectorField
import OTSelector.Geometry.Finsler.Hamiltonian.IntegralCurve
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Continuation of an intrinsic Finsler geodesic across finite endpoints

Main declarations: exists_eulerLagrange_extension_right; exists_eulerLagrange_extension_left.

This file contains the original declarations and their proofs. The source-unit
sections below preserve each unit's conditions, objects, proof details and
book or paper locations.
-/

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.FiniteTimeEndpoint`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A uniformly continuous curve into a complete metric space, or a C1 Finsler curve whose actual speed is bounded; completeness is for that same Finsler length metric.
* **Objects:** A speed-integral bound, Lipschitz control in the induced distance, and a continuous position extension from (a,b) to [a,b].
* **Proof detail:** Integrate the constant speed bound; compare distance with subsegment length; obtain uniform continuity and extend Cauchy limits to the interval endpoints.

## Mathematical sources

* Kenneth R. Davidson; Allan P. Donsig, *Real Analysis and Applications: Theory in Practice — Supplementary Material*, Section 9.B, Extension Theorem 9.B.4, p. 63.
  https://www.math.uwaterloo.ca/~krdavids/RAA/RAAsupp.pdf#page=65
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** Exact interval specialization of the uniform extension theorem, combined with the Finsler length formula. It does not claim convergence of velocity or momentum.
-/

/-!
# Finite-time endpoints from the actual Finsler speed

A bound on the actual tangent-vector Finsler norm bounds the integral path length.
Every C1 curve with this speed bound is therefore Lipschitz for the original Finsler
length metric. If this very metric is complete, the curve extends continuously to
both finite endpoints of its open time interval.

The extension agrees with the original interior curve. This is an endpoint theorem
for position; it does not assert convergence or continuation of velocity or momentum.
No inner product, strong convexity, or separately assumed Lipschitz property is used.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Geometry

/-- A uniformly continuous curve into a complete metric space extends to finite endpoints. -/
theorem exists_continuousOn_Icc_extension_of_uniformContinuousOn_metric
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    {c : ℝ → X} {a b : ℝ} (hab : a < b) (hc : UniformContinuousOn c (Ioo a b)) :
    ∃ cbar : ℝ → X, ContinuousOn cbar (Icc a b) ∧ EqOn cbar c (Ioo a b) := by
  refine ⟨extendFrom (Ioo a b) c, continuousOn_extendFrom ?_ ?_,
    extendFrom_extends hc.continuousOn⟩
  · rw [closure_Ioo hab.ne]
  · intro t ht
    have hcl : t ∈ closure (Ioo a b) := by rwa [closure_Ioo hab.ne]
    have : NeBot (𝓝[Ioo a b] t) := mem_closure_iff_nhdsWithin_neBot.mp hcl
    apply cauchy_map_iff_exists_tendsto.mp
    have hn : Cauchy (𝓝[Ioo a b] t) := cauchy_nhds.mono nhdsWithin_le_nhds
    exact hn.map_of_le hc inf_le_right

namespace ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]

/-- The actual tangent speed bound controls the original derivative-integral path length. -/
theorem pathELength_le_of_speed_le (F : ContinuousFinslerNorm E M)
    {c : ℝ → M} {a b : ℝ} {C : ℝ≥0}
    (hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤ C) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    Manifold.pathELength 𝓘(ℝ, E) c a b ≤ (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ ≤ ∫⁻ _ in Ioo a b, (C : ℝ≥0∞) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t ht
      exact ENNReal.coe_le_coe.mpr (hspeed t ht)
    _ = (C : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
      rw [setLIntegral_const, Real.volume_Ioo]

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

/-- A C1 curve with bounded actual Finsler speed is Lipschitz in the original length metric. -/
theorem lipschitzOnWith_lengthMetric_of_speed_le (F : ContinuousFinslerNorm E M)
    {c : ℝ → M} {a b : ℝ} {C : ℝ≥0}
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Ioo a b))
    (hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤ C) :
    letI : MetricSpace M := F.metricSpace
    LipschitzOnWith C c (Ioo a b) := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let : ∀ x : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) := F.enormSMulClass
  have hordered : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s ≤ t →
      edist (c s) (c t) ≤ (C : ℝ≥0∞) * edist s t := by
    intro s hs t ht hst
    have hsegment : Icc s t ⊆ Ioo a b := by
      intro u hu
      exact ⟨hs.1.trans_le hu.1, hu.2.trans_lt ht.2⟩
    calc
      edist (c s) (c t) ≤ Manifold.pathELength 𝓘(ℝ, E) c s t :=
        Manifold.riemannianEDist_le_pathELength (hc.mono hsegment) rfl rfl hst
      _ ≤ (C : ℝ≥0∞) * ENNReal.ofReal (t - s) :=
        F.pathELength_le_of_speed_le (fun u hu ↦ hspeed u (hsegment ⟨hu.1.le, hu.2.le⟩))
      _ = (C : ℝ≥0∞) * edist s t := by
        rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
  intro s hs t ht
  rcases le_total s t with hst | hts
  · exact hordered s hs t ht hst
  · rw [edist_comm (c s) (c t), edist_comm s t]
    exact hordered t ht s hs hts

/-- Completeness of the original Finsler length metric supplies finite continuous position
endpoints for every C1 curve with uniformly bounded actual Finsler speed. -/
theorem exists_continuousOn_Icc_extension_of_speed_le (F : ContinuousFinslerNorm E M)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c : ℝ → M} {a b : ℝ} {C : ℝ≥0} (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Ioo a b))
    (hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤ C) :
    ∃ cbar : ℝ → M, ContinuousOn cbar (Icc a b) ∧ EqOn cbar c (Ioo a b) := by
  let : MetricSpace M := F.metricSpace
  let : CompleteSpace M := hcomplete
  exact exists_continuousOn_Icc_extension_of_uniformContinuousOn_metric hab
    (F.lipschitzOnWith_lengthMetric_of_speed_le hc hspeed).uniformContinuousOn

end ContinuousFinslerNorm
end OTSelector.Geometry

end
end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.EndpointChart`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A continuous manifold curve on a nondegenerate closed interval. The speed-bound corollary additionally uses C1 Finsler regularity and completeness of the original length metric.
* **Objects:** A terminal closed time interval and its compact coordinate image inside the actual chart centered at the endpoint.
* **Proof detail:** Continuity places a terminal interval in the endpoint chart; take its continuous coordinate image as the compact set. For bounded speed, first construct the endpoint by uniform extension.

## Mathematical sources

* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html
* Kenneth R. Davidson; Allan P. Donsig, *Real Analysis and Applications: Theory in Practice — Supplementary Material*, Section 9.B, Extension Theorem 9.B.4, p. 63.
  https://www.math.uwaterloo.ca/~krdavids/RAA/RAAsupp.pdf#page=65
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)*, Section 4, p. 313: the length integral, induced distance and minimizing curves.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11

**Relationship to the sources:** Topological compact-image adapter used by the continuation proof, combined with the metric extension theorem in the Finsler corollary.
-/

/-!
# A fixed compact chart near a finite Finsler endpoint

A continuous curve on a closed time interval eventually lies in the chart centered at
its right endpoint. The coordinate image of a sufficiently short closed terminal interval
is compact and lies inside that same chart target. Thus compact coordinate confinement is
constructed from the endpoint, rather than assumed of the original trajectory.

For an actual C1 Finsler curve, completeness of the original length metric and bounded
original speed supply the endpoint. No Euler--Lagrange equation or strong convexity is
needed for this position-level conclusion. The compact set is the continuous coordinate
image of the terminal interval, so its compactness uses no extra finite-dimensional step.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Near its right endpoint, a continuous curve has a compact coordinate trace inside the
single chart centered at that endpoint. Both the chart confinement and compact set are derived. -/
theorem exists_right_endpoint_chart_compact {cbar : ℝ → M} {a b : ℝ}
    (hab : a < b) (hcbar : ContinuousOn cbar (Icc a b)) :
    ∃ b₀ ∈ Ioo a b, ∃ K : Set E,
      IsCompact K ∧ K ⊆ (extChartAt 𝓘(ℝ, E) (cbar b)).target ∧
      MapsTo cbar (Icc b₀ b) (extChartAt 𝓘(ℝ, E) (cbar b)).source ∧
      ContinuousOn ((extChartAt 𝓘(ℝ, E) (cbar b)) ∘ cbar) (Icc b₀ b) ∧
      MapsTo ((extChartAt 𝓘(ℝ, E) (cbar b)) ∘ cbar) (Icc b₀ b) K := by
  have hsource : cbar ⁻¹' (extChartAt 𝓘(ℝ, E) (cbar b)).source ∈ 𝓝[≤] b := by
    rw [← nhdsWithin_Icc_eq_nhdsLE hab]
    exact hcbar b ⟨hab.le, le_rfl⟩ (extChartAt_source_mem_nhds (cbar b))
  have hnear : cbar ⁻¹' (extChartAt 𝓘(ℝ, E) (cbar b)).source ∩ Ioi a ∈ 𝓝[≤] b :=
    inter_mem hsource (nhdsWithin_le_nhds (Ioi_mem_nhds hab))
  obtain ⟨b₀, hb₀, hsub⟩ := mem_nhdsLE_iff_exists_Icc_subset.mp hnear
  have hab₀ : a < b₀ := (hsub ⟨le_rfl, hb₀.le⟩).2
  have hsourceMap : MapsTo cbar (Icc b₀ b) (extChartAt 𝓘(ℝ, E) (cbar b)).source :=
    fun t ht ↦ (hsub ht).1
  have htime : Icc b₀ b ⊆ Icc a b := Icc_subset_Icc hab₀.le le_rfl
  have hcoord : ContinuousOn ((extChartAt 𝓘(ℝ, E) (cbar b)) ∘ cbar) (Icc b₀ b) :=
    (continuousOn_extChartAt (cbar b)).comp (hcbar.mono htime) hsourceMap
  let K := ((extChartAt 𝓘(ℝ, E) (cbar b)) ∘ cbar) '' Icc b₀ b
  refine ⟨b₀, ⟨hab₀, hb₀⟩, K, isCompact_Icc.image_of_continuousOn hcoord,
    ?_, hsourceMap, hcoord, mapsTo_image _ _⟩
  rintro u ⟨t, ht, rfl⟩
  exact (extChartAt 𝓘(ℝ, E) (cbar b)).map_source (hsourceMap ht)

namespace ContinuousFinslerNorm

variable [IsManifold 𝓘(ℝ, E) 1 M] [FiniteDimensional ℝ E]
  [T2Space M] [PreconnectedSpace M]

/-- Completeness and bounded original speed yield a finite position endpoint and a compact
coordinate trace near it, in the actual chart centered at that endpoint. -/
theorem exists_endpoint_chart_compact_of_speed_le (F : ContinuousFinslerNorm E M)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c : ℝ → M} {a b : ℝ} {C : ℝ≥0} (hab : a < b)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c (Ioo a b))
    (hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤ C) :
    ∃ cbar : ℝ → M, ContinuousOn cbar (Icc a b) ∧ EqOn cbar c (Ioo a b) ∧
      ∃ b₀ ∈ Ioo a b, ∃ K : Set E,
        IsCompact K ∧ K ⊆ (extChartAt 𝓘(ℝ, E) (cbar b)).target ∧
        MapsTo cbar (Icc b₀ b) (extChartAt 𝓘(ℝ, E) (cbar b)).source ∧
        ContinuousOn ((extChartAt 𝓘(ℝ, E) (cbar b)) ∘ cbar) (Icc b₀ b) ∧
        MapsTo ((extChartAt 𝓘(ℝ, E) (cbar b)) ∘ cbar) (Icc b₀ b) K := by
  obtain ⟨cbar, hcbar, heq⟩ :=
    F.exists_continuousOn_Icc_extension_of_speed_le hcomplete hab hc hspeed
  exact ⟨cbar, hcbar, heq, exists_right_endpoint_chart_compact hab hcbar⟩

end ContinuousFinslerNorm
end OTSelector.Geometry

end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.ChartContinuation`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** Smooth strongly convex Finsler energy on a finite-dimensional smooth manifold; a nonzero-velocity C2 Euler–Lagrange solution above a compact coordinate base inside a true chart.
* **Objects:** A compact fixed-positive-speed phase set and a smooth extension past the finite right endpoint, agreeing on the whole original interval.
* **Proof detail:** Use conserved speed to confine position and velocity to a compact subset of the slit domain. Continue the smooth phase ODE there and project to the actual position curve and its derivative.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, including the explicit left-endpoint version.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49

**Relationship to the sources:** Combination of the spray formulation and compact-range ODE continuation; compact phase confinement is established before applying continuation.
-/

/-!
# Continuation of actual Finsler equations over compact coordinate bases

The original Euler--Lagrange equation conserves Finsler speed. Over a compact base
inside a true chart, the fixed positive speed confines the actual position-velocity
state to a compact subset of the slit energy domain. The actual smooth phase field
therefore continues the curve past a finite endpoint. Projection recovers a smooth
position curve, its true velocity and its genuine Euler--Lagrange equation.

Compact base confinement is the local input here; the endpoint chart construction
derives such confinement when the original length metric is complete.
-/

open Set Metric Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] {F : ContinuousFinslerNorm E M}

/-- Every actual C2 slit Euler--Lagrange curve confined above a compact coordinate base
extends smoothly past its finite right endpoint, preserving the whole original curve. -/
theorem exists_chartEulerLagrange_extension_right (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt 𝓘(ℝ, E) x₀).target)
    {x : ℝ → E} {a b : ℝ} (hab : a < b) (hx : ContDiffOn ℝ 2 x (Ioo a b))
    (hbase : MapsTo x (Ioo a b) K)
    (hphase : ∀ t ∈ Ioo a b, (x t, deriv x t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ Ioo a b, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
      (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) :
    ∃ δ > (0 : ℝ), ∃ xbar : ℝ → E,
      EqOn xbar x (Ioo a b) ∧ ContDiffOn ℝ ∞ xbar (Ioo a (b + δ)) ∧
      (∀ t ∈ Ioo a (b + δ), (xbar t, deriv xbar t) ∈ chartEnergyDomain x₀) ∧
      ∀ t ∈ Ioo a (b + δ), HasDerivAt
        (fun s ↦ fiberLegendre (F.chartEnergy x₀) (xbar s, deriv xbar s))
        (baseEnergyDifferential (F.chartEnergy x₀) (xbar t, deriv xbar t)) t := by
  obtain ⟨t₀, ht₀⟩ := exists_between hab
  let c : ℝ := F.chartLength x₀ (x t₀, deriv x t₀)
  have hc : 0 < c := NNReal.coe_pos.mpr (F.chartLength_pos x₀ (hphase t₀ ht₀))
  let S : Set (E × E) := {z | z.1 ∈ K ∧ (F.chartLength x₀ z : ℝ) ∈ Icc c c}
  have hS : IsCompact S := F.isCompact_chartSpeed_range x₀ hK hKU c c
  have hSU : S ⊆ chartEnergyDomain x₀ := F.chartSpeed_range_subset_domain x₀ hKU hc
  have hmap : MapsTo (fun t ↦ (x t, deriv x t)) (Ioo a b) S := by
    intro t ht
    refine ⟨hbase ht, ?_⟩
    have heq := hF.chartLength_eq_of_eulerLagrange x₀ isOpen_Ioo
      (convex_Ioo a b).isPreconnected hx hphase hEL ht ht₀
    change (F.chartLength x₀ (x t, deriv x t) : ℝ) ∈ Icc c c
    rw [heq]
    exact ⟨le_rfl, le_rfl⟩
  have hfield := hF.contDiffOn_chartEulerLagrangeVectorField x₀
  have hODE := hF.hasDerivAt_chartEulerLagrange_positionVelocity x₀
    isOpen_Ioo hx hphase hEL
  obtain ⟨δ, hδ, y, heq, hstay, hy⟩ := exists_integralCurve_extension_right_of_compact
    (isOpen_chartEnergyDomain x₀) (hfield.of_le (by simp)) hS hSU hab hmap hODE
  have hysmooth := contDiffOn_integralCurve_of_isOpen hfield isOpen_Ioo hstay hy
  have hactual : ∀ t ∈ Ioo a (b + δ), ((y t).1, deriv (fun s ↦ (y s).1) t) = y t := by
    intro t ht
    have hd : HasDerivAt (fun s ↦ (y s).1)
        (eulerLagrangeVectorField (F.chartEnergy x₀) (y t)).1 t := (hy t ht).fst
    rw [hd.deriv, hF.chartEulerLagrangeVectorField_fst x₀ (hstay ht)]
  refine ⟨δ, hδ, fun t ↦ (y t).1, ?_, hysmooth.fst, ?_, ?_⟩
  · intro t ht
    exact congrArg Prod.fst (heq ht)
  · intro t ht
    rw [hactual t ht]
    exact hstay ht
  · intro t ht
    exact hF.hasDerivAt_chartEulerLagrange_of_positionVelocity x₀ isOpen_Ioo hstay hy ht

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.Continuation`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A smooth strongly convex Finsler structure on a finite-dimensional Hausdorff preconnected smooth manifold, complete for the original length metric; an intrinsic nonzero-velocity solution on (a,b).
* **Objects:** An actual intrinsic extension to (a,b+delta), agreeing with the entire original manifold curve.
* **Proof detail:** Derive one constant speed, obtain a position endpoint and compact terminal chart trace, express the original equation in that chart, continue its compact phase ODE, and glue.

## Mathematical sources

* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Kenneth R. Davidson; Allan P. Donsig, *Real Analysis and Applications: Theory in Practice — Supplementary Material*, Section 9.B, Extension Theorem 9.B.4, p. 63.
  https://www.math.uwaterloo.ca/~krdavids/RAA/RAAsupp.pdf#page=65
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, including the explicit left-endpoint version.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61

**Relationship to the sources:** Intrinsic synthesis of bounded-speed metric extension and compact-range ODE continuation. The source provides the ODE criterion, while the required Finsler compact confinement is proved locally.
-/

/-!
# Finite continuation of intrinsic Finsler Euler--Lagrange curves

The original curve may pass through arbitrarily many atlas charts. Its local actual
Euler--Lagrange equation gives one constant original speed on the connected interval.
Completeness therefore supplies a position endpoint and a compact terminal coordinate
image. Coordinate covariance makes the entire terminal curve solve the true equation
in that endpoint chart. Compact phase continuation and local gluing extend the intrinsic
equation through the finite endpoint, preserving the whole original manifold curve.
-/

open Set Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original metric completeness extends every intrinsic nonzero-velocity Euler--Lagrange
curve through its finite right endpoint. No fixed chart, speed bound or compact orbit
is required as an input. -/
theorem exists_eulerLagrange_extension_right (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : F.IsEulerLagrangeOn c (Ioo a b)) :
    ∃ δ > (0 : ℝ), ∃ cext : ℝ → M,
      EqOn cext c (Ioo a b) ∧ F.IsEulerLagrangeOn cext (Ioo a (b + δ)) := by
  obtain ⟨t₀, ht₀⟩ := exists_between hab
  have hsmooth := hF.contMDiffOn_of_isEulerLagrangeOn hc
  have hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) :=
    fun t ht ↦ (hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_Ioo ht ht₀).le
  obtain ⟨cbar, hcbar, hcbar_eq, b₀, hb₀, K, hK, hKsub, hsource, _, hKmap⟩ :=
    F.exists_endpoint_chart_compact_of_speed_le hcomplete hab
      (hsmooth.of_le (by simp)) hspeed
  let new := cbar b
  let η := extChartAt 𝓘(ℝ, E) new ∘ c
  have hsmall : Ioo b₀ b ⊆ Ioo a b := Ioo_subset_Ioo hb₀.1.le le_rfl
  have hmap : MapsTo c (Ioo b₀ b) (extChartAt 𝓘(ℝ, E) new).source := by
    intro t ht
    rw [← hcbar_eq (hsmall ht)]
    exact hsource ⟨ht.1.le, ht.2.le⟩
  obtain ⟨hη, hηphase, hηEL⟩ :=
    hF.chartEulerLagrange_of_isEulerLagrangeOn (hc.mono hsmall) new hmap
  have hηmap : MapsTo η (Ioo b₀ b) K := by
    intro t ht
    change extChartAt 𝓘(ℝ, E) new (c t) ∈ K
    rw [← hcbar_eq (hsmall ht)]
    exact hKmap ⟨ht.1.le, ht.2.le⟩
  obtain ⟨δ, hδ, ηbar, hηbar_eq, hηbar, hηbar_phase, hηbar_EL⟩ :=
    hF.exists_chartEulerLagrange_extension_right new hK hKsub hb₀.2
      (hη.of_le (by simp)) hηmap hηphase hηEL
  let cnew := (extChartAt 𝓘(ℝ, E) new).symm ∘ ηbar
  let cext : ℝ → M := fun t ↦ if t < b then c t else cnew t
  have hoverlap : EqOn cnew c (Ioo b₀ b) := by
    intro t ht
    change (extChartAt 𝓘(ℝ, E) new).symm (ηbar t) = c t
    rw [hηbar_eq ht]
    exact (extChartAt 𝓘(ℝ, E) new).left_inv (hmap ht)
  have hold : EqOn cext c (Ioo a b) := by
    intro t ht
    simp only [cext, ite_eq_left ht.2]
  have hnew : EqOn cext cnew (Ioo b₀ (b + δ)) := by
    intro t ht
    by_cases htb : t < b
    · simpa only [cext, ite_eq_left htb] using (hoverlap ⟨ht.1, htb⟩).symm
    · simp only [cext, ite_eq_right htb]
  have hcnew : F.IsEulerLagrangeOn cnew (Ioo b₀ (b + δ)) :=
    F.isEulerLagrangeOn_chart_symm new isOpen_Ioo
      (hηbar.of_le (by simp)) hηbar_phase hηbar_EL
  have holdEL := hc.congr isOpen_Ioo hold.symm
  have hnewEL := hcnew.congr isOpen_Ioo hnew.symm
  refine ⟨δ, hδ, cext, hold, ?_⟩
  intro t ht
  by_cases htb : t < b
  · exact holdEL t ⟨ht.1, htb⟩
  · exact hnewEL t ⟨lt_of_lt_of_le hb₀.2 (le_of_not_gt htb), ht.2⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end

/-! Source unit: `OTSelector.Geometry.Finsler.Geodesic.LeftContinuation`. Its original mathematical documentation follows. -/
section

/-!
## Lemma skeleton

* **Conditions:** A continuous closed-interval curve for the compact left endpoint trace; for differential continuation, smooth strongly convex finite-dimensional Finsler data and compact coordinate confinement; original metric completeness for intrinsic continuation.
* **Objects:** A compact initial chart trace, a left chartwise ODE extension and an intrinsic extension to (a-delta,b).
* **Proof detail:** Construct the left endpoint chart trace; confine fixed positive speed phase; use the left-endpoint ODE continuation result; transfer back and glue.

## Mathematical sources

* Jiří Lebl, *Basic Analysis I: Introduction to Real Analysis, Volume I*, Section 7.5, Lemma 7.5.5 (compact continuous images), Theorem 7.5.6 (extreme values), and Exercise 7.5.6 (intermediate value theorem).
  https://www.jirka.org/ra/html/sec_metcont.html
* Zhongmin Shen, *Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)*, Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
  https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, Lemma 2.14 and Corollary 2.15, pp. 52–53, including the explicit left-endpoint version.
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=63
* Gerald Teschl, *Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)*, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).
  https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61

**Relationship to the sources:** Left-endpoint version of the same continuation synthesis. Teschl explicitly includes the left endpoint; the manifold chart and nonzero phase control are local formal developments.
-/

/-!
# Left finite continuation for intrinsic Finsler Euler--Lagrange curves

Completeness of the original length metric gives a position endpoint at the left end
of a finite time interval. The actual equation in the chart centered there confines the
phase to a compact positive-speed set. Left continuation of that actual phase field and
overlap gluing extend the original intrinsic solution through the endpoint.
-/

open Set Filter Metric Manifold
open scoped Topology ContDiff

namespace OTSelector.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- A continuous closed-interval curve has a compact coordinate trace near its left
endpoint, contained in the actual chart centered at that endpoint. -/
theorem exists_left_endpoint_chart_compact {cbar : ℝ → M} {a b : ℝ}
    (hab : a < b) (hcbar : ContinuousOn cbar (Icc a b)) :
    ∃ a₀ ∈ Ioo a b, ∃ K : Set E,
      IsCompact K ∧ K ⊆ (extChartAt 𝓘(ℝ, E) (cbar a)).target ∧
      MapsTo cbar (Icc a a₀) (extChartAt 𝓘(ℝ, E) (cbar a)).source ∧
      ContinuousOn ((extChartAt 𝓘(ℝ, E) (cbar a)) ∘ cbar) (Icc a a₀) ∧
      MapsTo ((extChartAt 𝓘(ℝ, E) (cbar a)) ∘ cbar) (Icc a a₀) K := by
  have hsource : cbar ⁻¹' (extChartAt 𝓘(ℝ, E) (cbar a)).source ∈ 𝓝[≥] a := by
    rw [← nhdsWithin_Icc_eq_nhdsGE hab]
    exact hcbar a ⟨le_rfl, hab.le⟩ (extChartAt_source_mem_nhds (cbar a))
  have hnear : cbar ⁻¹' (extChartAt 𝓘(ℝ, E) (cbar a)).source ∩ Iio b ∈ 𝓝[≥] a :=
    inter_mem hsource (nhdsWithin_le_nhds (Iio_mem_nhds hab))
  obtain ⟨a₀, ha₀, hsub⟩ := mem_nhdsGE_iff_exists_Icc_subset.mp hnear
  have ha₀b : a₀ < b := (hsub ⟨ha₀.le, le_rfl⟩).2
  have hsourceMap : MapsTo cbar (Icc a a₀) (extChartAt 𝓘(ℝ, E) (cbar a)).source :=
    fun t ht ↦ (hsub ht).1
  have htime : Icc a a₀ ⊆ Icc a b := Icc_subset_Icc le_rfl ha₀b.le
  have hcoord : ContinuousOn ((extChartAt 𝓘(ℝ, E) (cbar a)) ∘ cbar) (Icc a a₀) :=
    (continuousOn_extChartAt (cbar a)).comp (hcbar.mono htime) hsourceMap
  let K := ((extChartAt 𝓘(ℝ, E) (cbar a)) ∘ cbar) '' Icc a a₀
  refine ⟨a₀, ⟨ha₀, ha₀b⟩, K, isCompact_Icc.image_of_continuousOn hcoord,
    ?_, hsourceMap, hcoord, mapsTo_image _ _⟩
  rintro u ⟨t, ht, rfl⟩
  exact (extChartAt 𝓘(ℝ, E) (cbar a)).map_source (hsourceMap ht)

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

/-- Every actual C2 slit Euler--Lagrange curve confined above a compact coordinate base
extends smoothly past its finite left endpoint, preserving the whole original curve. -/
theorem exists_chartEulerLagrange_extension_left (hF : F.IsSmoothStronglyConvex)
    (x₀ : M) {K : Set E} (hK : IsCompact K)
    (hKU : K ⊆ (extChartAt 𝓘(ℝ, E) x₀).target)
    {x : ℝ → E} {a b : ℝ} (hab : a < b) (hx : ContDiffOn ℝ 2 x (Ioo a b))
    (hbase : MapsTo x (Ioo a b) K)
    (hphase : ∀ t ∈ Ioo a b, (x t, deriv x t) ∈ chartEnergyDomain x₀)
    (hEL : ∀ t ∈ Ioo a b, HasDerivAt
      (fun s ↦ fiberLegendre (F.chartEnergy x₀) (x s, deriv x s))
      (baseEnergyDifferential (F.chartEnergy x₀) (x t, deriv x t)) t) :
    ∃ δ > (0 : ℝ), ∃ xbar : ℝ → E,
      EqOn xbar x (Ioo a b) ∧ ContDiffOn ℝ ∞ xbar (Ioo (a - δ) b) ∧
      (∀ t ∈ Ioo (a - δ) b, (xbar t, deriv xbar t) ∈ chartEnergyDomain x₀) ∧
      ∀ t ∈ Ioo (a - δ) b, HasDerivAt
        (fun s ↦ fiberLegendre (F.chartEnergy x₀) (xbar s, deriv xbar s))
        (baseEnergyDifferential (F.chartEnergy x₀) (xbar t, deriv xbar t)) t := by
  obtain ⟨t₀, ht₀⟩ := exists_between hab
  let c : ℝ := F.chartLength x₀ (x t₀, deriv x t₀)
  have hc : 0 < c := NNReal.coe_pos.mpr (F.chartLength_pos x₀ (hphase t₀ ht₀))
  let S : Set (E × E) := {z | z.1 ∈ K ∧ (F.chartLength x₀ z : ℝ) ∈ Icc c c}
  have hS : IsCompact S := F.isCompact_chartSpeed_range x₀ hK hKU c c
  have hSU : S ⊆ chartEnergyDomain x₀ := F.chartSpeed_range_subset_domain x₀ hKU hc
  have hmap : MapsTo (fun t ↦ (x t, deriv x t)) (Ioo a b) S := by
    intro t ht
    refine ⟨hbase ht, ?_⟩
    have heq := hF.chartLength_eq_of_eulerLagrange x₀ isOpen_Ioo
      (convex_Ioo a b).isPreconnected hx hphase hEL ht ht₀
    change (F.chartLength x₀ (x t, deriv x t) : ℝ) ∈ Icc c c
    rw [heq]
    exact ⟨le_rfl, le_rfl⟩
  have hfield := hF.contDiffOn_chartEulerLagrangeVectorField x₀
  have hODE := hF.hasDerivAt_chartEulerLagrange_positionVelocity x₀
    isOpen_Ioo hx hphase hEL
  obtain ⟨δ, hδ, y, heq, hstay, hy⟩ := exists_integralCurve_extension_left_of_compact
    (isOpen_chartEnergyDomain x₀) (hfield.of_le (by simp)) hS hSU hab hmap hODE
  have hysmooth := contDiffOn_integralCurve_of_isOpen hfield isOpen_Ioo hstay hy
  have hactual : ∀ t ∈ Ioo (a - δ) b, ((y t).1, deriv (fun s ↦ (y s).1) t) = y t := by
    intro t ht
    have hd : HasDerivAt (fun s ↦ (y s).1)
        (eulerLagrangeVectorField (F.chartEnergy x₀) (y t)).1 t := (hy t ht).fst
    rw [hd.deriv, hF.chartEulerLagrangeVectorField_fst x₀ (hstay ht)]
  refine ⟨δ, hδ, fun t ↦ (y t).1, ?_, hysmooth.fst, ?_, ?_⟩
  · intro t ht
    exact congrArg Prod.fst (heq ht)
  · intro t ht
    rw [hactual t ht]
    exact hstay ht
  · intro t ht
    exact hF.hasDerivAt_chartEulerLagrange_of_positionVelocity x₀ isOpen_Ioo hstay hy ht


variable [T2Space M] [PreconnectedSpace M]

/-- Original metric completeness extends an intrinsic nonzero-velocity Euler--Lagrange
curve through its finite left endpoint, preserving its whole original time interval.
The speed bound, endpoint chart and compact confinement are derived from the equation. -/
theorem exists_eulerLagrange_extension_left (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : F.IsEulerLagrangeOn c (Ioo a b)) :
    ∃ δ > (0 : ℝ), ∃ cext : ℝ → M,
      EqOn cext c (Ioo a b) ∧ F.IsEulerLagrangeOn cext (Ioo (a - δ) b) := by
  obtain ⟨t₀, ht₀⟩ := exists_between hab
  have hsmooth := hF.contMDiffOn_of_isEulerLagrangeOn hc
  have hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) ≤
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t₀, (1 : ℝ)⟩) :=
    fun t ht ↦ (hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_Ioo ht ht₀).le
  obtain ⟨cbar, hcbar, hcbar_eq⟩ :=
    F.exists_continuousOn_Icc_extension_of_speed_le hcomplete hab
      (hsmooth.of_le (by simp)) hspeed
  obtain ⟨a₀, ha₀, K, hK, hKsub, hsource, _, hKmap⟩ :=
    exists_left_endpoint_chart_compact (E := E) hab hcbar
  let new := cbar a
  let η := extChartAt 𝓘(ℝ, E) new ∘ c
  have hsmall : Ioo a a₀ ⊆ Ioo a b := Ioo_subset_Ioo le_rfl ha₀.2.le
  have hmap : MapsTo c (Ioo a a₀) (extChartAt 𝓘(ℝ, E) new).source := by
    intro t ht
    rw [← hcbar_eq (hsmall ht)]
    exact hsource ⟨ht.1.le, ht.2.le⟩
  obtain ⟨hη, hηphase, hηEL⟩ :=
    hF.chartEulerLagrange_of_isEulerLagrangeOn (hc.mono hsmall) new hmap
  have hηmap : MapsTo η (Ioo a a₀) K := by
    intro t ht
    change extChartAt 𝓘(ℝ, E) new (c t) ∈ K
    rw [← hcbar_eq (hsmall ht)]
    exact hKmap ⟨ht.1.le, ht.2.le⟩
  obtain ⟨δ, hδ, ηbar, hηbar_eq, hηbar, hηbar_phase, hηbar_EL⟩ :=
    hF.exists_chartEulerLagrange_extension_left new hK hKsub ha₀.1
      (hη.of_le (by simp)) hηmap hηphase hηEL
  let cnew := (extChartAt 𝓘(ℝ, E) new).symm ∘ ηbar
  let cext : ℝ → M := fun t ↦ if a < t then c t else cnew t
  have hoverlap : EqOn cnew c (Ioo a a₀) := by
    intro t ht
    change (extChartAt 𝓘(ℝ, E) new).symm (ηbar t) = c t
    rw [hηbar_eq ht]
    exact (extChartAt 𝓘(ℝ, E) new).left_inv (hmap ht)
  have hold : EqOn cext c (Ioo a b) := by
    intro t ht
    simp only [cext, ite_eq_left ht.1]
  have hnew : EqOn cext cnew (Ioo (a - δ) a₀) := by
    intro t ht
    by_cases hat : a < t
    · simpa only [cext, ite_eq_left hat] using (hoverlap ⟨hat, ht.2⟩).symm
    · simp only [cext, ite_eq_right hat]
  have hcnew : F.IsEulerLagrangeOn cnew (Ioo (a - δ) a₀) :=
    F.isEulerLagrangeOn_chart_symm new isOpen_Ioo
      (hηbar.of_le (by simp)) hηbar_phase hηbar_EL
  have holdEL := hc.congr isOpen_Ioo hold.symm
  have hnewEL := hcnew.congr isOpen_Ioo hnew.symm
  refine ⟨δ, hδ, cext, hold, ?_⟩
  intro t ht
  by_cases hat : a < t
  · exact holdEL t ⟨hat, ht.2⟩
  · exact hnewEL t ⟨ht.1, lt_of_le_of_lt (le_of_not_gt hat) ha₀.1⟩

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
