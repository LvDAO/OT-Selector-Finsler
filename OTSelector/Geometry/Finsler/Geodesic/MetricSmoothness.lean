import OTSelector.Analysis.ContinuousDerivativeRepresentative
import OTSelector.Analysis.Convex.Legendre.Parametric
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.MetricContinuousVelocity
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerRegularity
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Hamiltonian.Basic
import OTSelector.Geometry.Finsler.Hamiltonian.IntegralCurve
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerMetricSmoothness.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerMetricSmoothness`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.MetricSmoothness

* **Conditions:** An original-distance isometric interval in a smooth strongly convex finite-dimensional Finsler manifold.
* **Objects:** Intrinsic Euler–Lagrange germs at each interior time and a globally smooth interior curve.
* **Proof detail:** Absolute continuity identifies the actual derivative with the continuous velocity representative; the momentum primitive gives classical Euler–Lagrange and the smooth Hamiltonian ODE bootstraps regularity.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=49): Section 2.2, Theorem 2.2 (Picard–Lindelöf) and Lemma 2.3 (regularity), p. 38.

Source relation (derived): A complete local regularity derivation from an initially nonsmooth metric minimizer; no C2 minimizer hypothesis is imported.
-/

/-!
# Smooth actual Euler--Lagrange identity of metric minimizing intervals

An original-distance isometric interval satisfies the intrinsic nonzero-velocity
Euler--Lagrange equation near every interior time. Absolute continuity recovers the
actual derivative from the continuous velocity representative; the original momentum
primitive yields the classical equation. The smooth Hamiltonian vector field then
upgrades the actual solution to smoothness without a C2 premise on the minimizer.
-/

open Set Filter Metric Manifold MeasureTheory
open scoped Topology ContDiff NNReal

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

set_option backward.isDefEq.respectTransparency false in
/-- Every interior point of an original-distance isometric interval is an intrinsic
actual slit Euler--Lagrange germ. No coordinate differentiability is assumed. -/
theorem isEulerLagrangeAt_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b)
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) : F.IsEulerLagrangeAt c t₀ := by
  let : MetricSpace M := F.metricSpace
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let χ := extChartAt 𝓘(ℝ, E) (c t₀)
  let x : ℝ → E := χ ∘ c
  let L := F.chartEnergy (c t₀)
  let q : ℝ → E →L[ℝ] ℝ := fun t ↦ baseEnergyDifferential L (x t, deriv x t)
  obtain ⟨δ, hδ, C, v, hsub, hsource, hx, hv, hP, hphase, hmomentum, hq, hveq, _⟩ :=
    hF.exists_continuous_chartVelocity_of_isometric_interval ht₀ hiso
  let P : ℝ → E →L[ℝ] ℝ := fun t ↦ C + ∫ s in (t₀ - δ)..t, q s
  let Q : ℝ → E →L[ℝ] ℝ := fun t ↦ baseEnergyDifferential L (x t, v t)
  have habδ : t₀ - δ ≤ t₀ + δ := by linarith
  have hQ : ContinuousOn Q (Icc (t₀ - δ) (t₀ + δ)) := by
    have hbase : ContinuousOn (baseEnergyDifferential L) (chartEnergyDomain (c t₀)) := by
      intro w hw
      exact (contDiffAt_baseEnergyDifferential ((hF.contDiffOn_chartEnergy (c t₀)).contDiffAt
        ((isOpen_chartEnergyDomain (c t₀)).mem_nhds hw))).continuousAt.continuousWithinAt
    exact hbase.comp (hx.prodMk hv) hphase
  have hqeq : q =ᵐ[volume.restrict (Ioo (t₀ - δ) (t₀ + δ))] Q := by
    filter_upwards [hveq] with t ht
    change baseEnergyDifferential L (x t, deriv x t) = baseEnergyDifferential L (x t, v t)
    rw [ht]
  have hPd (t : ℝ) (ht : t ∈ Ioo (t₀ - δ) (t₀ + δ)) : HasDerivAt P (Q t) t :=
    (hasDerivAt_integral_of_continuous_ae_representative habδ hq hQ hqeq ht).const_add C
  have hab : a ≤ b := le_of_lt (ht₀.1.trans ht₀.2)
  let d : ℝ → M := (fun t : Icc a b ↦ c t) ∘ projIcc a b hab
  have hd : LipschitzWith 1 d := by
    simpa only [mul_one] using hiso.lipschitzWith.comp (LipschitzWith.projIcc hab)
  have heq : EqOn d c (Icc a b) := by
    intro t ht
    simp only [d, Function.comp_apply, projIcc_of_mem _ ht]
  have hd₀ : d t₀ = c t₀ := heq (Ioo_subset_Icc_self ht₀)
  obtain ⟨ε, hε, Kx, _, hxLip, _, _, _⟩ :=
    F.exists_regular_chartInterval_of_lipschitzWith hd t₀
  rw [hd₀] at hxLip
  change LipschitzOnWith Kx (χ ∘ d) (Icc (t₀ - ε) (t₀ + ε)) at hxLip
  let r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  have hrδ : r ≤ δ := min_le_left _ _
  have hrε : r ≤ ε := min_le_right _ _
  have hsmall : Icc (t₀ - r) (t₀ + r) ⊆ Icc (t₀ - δ) (t₀ + δ) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hsmallε : Icc (t₀ - r) (t₀ + r) ⊆ Icc (t₀ - ε) (t₀ + ε) :=
    Icc_subset_Icc (by linarith) (by linarith)
  have hopenSmall : Ioo (t₀ - r) (t₀ + r) ⊆ Ioo (t₀ - δ) (t₀ + δ) :=
    Ioo_subset_Ioo (by linarith) (by linarith)
  have hxEq : EqOn (χ ∘ d) x (Icc (t₀ - r) (t₀ + r)) := by
    intro t ht
    exact congrArg χ (heq (Ioo_subset_Icc_self (hsub (hsmall ht))))
  have hxLip' : LipschitzOnWith Kx x (Icc (t₀ - r) (t₀ + r)) := by
    intro u hu w hw
    rw [← hxEq hu, ← hxEq hw]
    exact hxLip (hsmallε hu) (hsmallε hw)
  have hac : AbsolutelyContinuousOnInterval x (t₀ - r) (t₀ + r) := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le (by linarith : t₀ - r ≤ t₀ + r)] using hxLip'
  have hxdAE : ∀ᵐ t ∂volume.restrict (Ioo (t₀ - r) (t₀ + r)), HasDerivAt x (v t) t := by
    have hdiff := (hxLip'.mono Ioo_subset_Icc_self).ae_differentiableWithinAt
      (μ := volume) measurableSet_Ioo
    filter_upwards [hdiff, ae_restrict_of_ae_restrict_of_subset hopenSmall hveq,
      ae_restrict_mem measurableSet_Ioo] with t ht hvt htin
    rw [hvt]
    exact (ht.differentiableAt (isOpen_Ioo.mem_nhds htin)).hasDerivAt
  have hxd := hasDerivAt_of_absolutelyContinuous_of_continuous_ae_derivative
    (by linarith : t₀ - r ≤ t₀ + r) hac (hv.mono hsmall) hxdAE
  have hEL (t : ℝ) (ht : t ∈ Ioo (t₀ - r) (t₀ + r)) :
      HasDerivAt (fun s ↦ fiberLegendre L (x s, deriv x s))
        (baseEnergyDifferential L (x t, deriv x t)) t := by
    have heqP : (fun s ↦ fiberLegendre L (x s, deriv x s)) =ᶠ[𝓝 t] P := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      rw [(hxd s hs).deriv]
      exact (hmomentum s (hsmall (Ioo_subset_Icc_self hs))).symm
    rw [(hxd t ht).deriv]
    exact (hPd t (hopenSmall ht)).congr_of_eventuallyEq heqP
  have ht₀r : t₀ ∈ Ioo (t₀ - r) (t₀ + r) := ⟨by linarith, by linarith⟩
  have ht₀δ : t₀ ∈ Icc (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  obtain ⟨e, he, hes, _, _, _, _, hX, _⟩ :=
    hF.exists_smooth_chartHamiltonian (c t₀) (hphase t₀ ht₀δ)
  have hstay : ∀ᶠ u in 𝓝 t₀, (x u, v u) ∈ e.source :=
    ((hx.prodMk hv).continuousAt (Icc_mem_nhds (by linarith) (by linarith)))
      |>.preimage_mem_nhds (e.open_source.mem_nhds hes)
  obtain ⟨J, hJsub, hJ, ht₀J⟩ := _root_.mem_nhds_iff.mp
    (inter_mem (isOpen_Ioo.mem_nhds ht₀r) hstay)
  have hJs (t : ℝ) (ht : t ∈ J) : (x t, deriv x t) ∈ e.source := by
    rw [(hxd t (hJsub ht).1).deriv]
    exact (hJsub ht).2
  have hxsmooth : ContDiffOn ℝ ∞ x J := by
    have hlift : ContDiffOn ℝ ∞ (eulerLagrangePhaseLift L x) J := by
      apply contDiffOn_integralCurve_of_isOpen hX hJ
      · intro t ht
        change parametricLegendre L (x t, deriv x t) ∈ e.target
        rw [← he]
        exact e.map_source (hJs t ht)
      · intro t ht
        exact hasDerivAt_eulerLagrangePhaseLift he (hxd t (hJsub ht).1).differentiableAt
          (hJs t ht) (hEL t (hJsub ht).1)
    exact hlift.fst
  refine ⟨c t₀, J, hJ, ht₀J, ?_, hxsmooth.of_le (by simp), ?_, ?_⟩
  · intro t ht
    exact hsource (hsmall (Ioo_subset_Icc_self (hJsub ht).1))
  · intro t ht
    change (x t, deriv x t) ∈ chartEnergyDomain (c t₀)
    rw [(hxd t (hJsub ht).1).deriv]
    exact hphase t (hsmall (Ioo_subset_Icc_self (hJsub ht).1))
  · intro t ht
    exact hEL t (hJsub ht).1

/-- An original-distance isometric interval satisfies the intrinsic actual equation
at every interior time. -/
theorem isEulerLagrangeOn_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) : F.IsEulerLagrangeOn c (Ioo a b) :=
  fun _ ht ↦ hF.isEulerLagrangeAt_of_isometric_interval ht hiso

/-- Metric minimizing isometric intervals are smooth on their open time interval. -/
theorem contMDiffOn_of_isometric_interval (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc a b ↦ c t)) :
    ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c (Ioo a b) :=
  hF.contMDiffOn_of_isEulerLagrangeOn (hF.isEulerLagrangeOn_of_isometric_interval hiso)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
