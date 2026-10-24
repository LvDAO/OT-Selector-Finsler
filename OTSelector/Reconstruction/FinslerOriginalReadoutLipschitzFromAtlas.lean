import OTSelector.Reconstruction.FinslerOriginalAmplitudeReadoutBookkeeping
import OTSelector.Reconstruction.FinslerOriginalParentChartProducer
import OTSelector.Geometry.Finsler.Coordinates.InverseChartLipschitz

/-!
# Readout Lipschitz constant from atlas derivative data

This file closes the remaining gap of
FinslerOriginalAmplitudeReadoutBookkeeping.lean: the inverse-chart Lipschitz
constant is no longer a hypothesis but is extracted from the actual atlas
derivative data.

The underlying geometry is the inverse-chart bound of
OTSelector.Geometry.FinslerInverseChartLipschitz: on a chart ball around the chart
centre, the actual inverse chart is Lipschitz for the original Finsler distance,
with a constant obtained from the uniform inverse-chart differential bound (the
mean value inequality along coordinate segments).  This supplies the hread input
of the ball containment unconditionally.

Contents:

1. exists_readout_inverse_lipschitz: the constructed chart ball and its
   Lipschitz inverse-chart constant.
2. frozenCoreEntry_ballContainment_of_chartBall: on that chart ball, source and
   target points with a common chart amplitude bound Drad lie in one manifold
   ball of radius K * Drad.  This is the hX/hY input of the frozen core entry
   bound, with the readout constant now explicit from the atlas data.
3. calibratedWindow_ballContainment: the same containment stated for the retained
   points of a calibrated seed window, where the chart readout is the window
   readout P.readout and the retained domain is P.domain.
4. windowChartData_toManifold_eq_chart_curve: the node-position/path identity in
   the window chart data context, expressing every retained window point as a
   curve point through the chart section.
5. windowChartData_ballContainment: the containment in the window-chart-data
   context, together with the chart-section expression of both endpoints.
-/
open Set Function Filter MeasureTheory Matrix Module Manifold Metric
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator Classical Topology BigOperators

noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The inverse-chart Lipschitz constant from the atlas derivative data -/

/-- **Constructed chart ball with Lipschitz inverse chart.**  From the uniform
inverse-chart differential bound (atlas derivative data, mean value inequality
along coordinate segments), there is a chart ball around the chart centre on
which the actual inverse chart is Lipschitz for the original Finsler distance.
This is the unconditional source of the readout constant K. -/
theorem exists_readout_inverse_lipschitz (x₀ : M) :
    letI : MetricSpace M := F.metricSpace
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧
      ball (extChartAt 𝓘(ℝ, E) x₀ x₀) r ⊆ (extChartAt 𝓘(ℝ, E) x₀).target ∧
      LipschitzOnWith K (extChartAt 𝓘(ℝ, E) x₀).symm
        (ball (extChartAt 𝓘(ℝ, E) x₀ x₀) r) :=
  F.exists_lipschitzOnWith_extChartAt_symm x₀

/-- **Chart ball amplitude containment (generic).**  If the inverse chart readout
Psi is Lipschitz on a chart closed ball and fixes the readout on the retained
points, then a common chart amplitude bound Drad yields one manifold ball of
radius K * Drad.  This is the hX/hY input of the frozen core entry bound. -/
theorem dist_le_of_chartBall_amplitude {M G : Type*} [PseudoMetricSpace M]
    [NormedAddCommGroup G] {Φ : M → G} {Ψ : G → M} {y₀ : G} {r : ℝ} {K : ℝ≥0}
    (hK : LipschitzOnWith K Ψ (ball y₀ r)) {ι : Type*}
    {X : ι → M} {c : M} {Drad : ℝ}
    (hXball : ∀ i, Φ (X i) ∈ ball y₀ r)
    (hcball : Φ c ∈ ball y₀ r)
    (hXleft : ∀ i, Ψ (Φ (X i)) = X i) (hcleft : Ψ (Φ c) = c)
    (hamp : ∀ i, ‖Φ (X i) - Φ c‖ ≤ Drad) :
    ∀ i, dist (X i) c ≤ (K : ℝ) * Drad := by
  intro i
  have h := hK.dist_le_mul (Φ (X i)) (hXball i) (Φ c) (hcball)
  rw [hXleft i, hcleft, dist_eq_norm] at h
  exact h.trans (mul_le_mul_of_nonneg_left (hamp i) (NNReal.coe_nonneg K))

/-! ## The retained calibrated window -/

/-- **Retained window ball containment.**  For a calibrated seed window, every
retained pair of window points (in the window domain, with readout deviations
from the window centre bounded by half the constructed chart radius, and readout
amplitude separated by at most Drad) lies in one manifold ball of radius
K * Drad.  This is the frozen core entry ball containment in the actual window
readout, with the constant K coming from the atlas derivative data. -/
theorem calibratedWindow_ballContainment (P : CalibratedSeedWindow F u) :
    letI : MetricSpace M := F.metricSpace
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧
      ∀ (z zc : ℝ × P.seed.covector.ker) {Drad : ℝ},
        z ∈ P.domain → zc ∈ P.domain →
        ‖P.readout z - P.readout P.center‖ < r / 2 →
        ‖P.readout zc - P.readout P.center‖ < r / 2 →
        ‖P.readout z - P.readout zc‖ ≤ Drad →
        dist (P.toManifold z) (P.toManifold zc) ≤ (K : ℝ) * Drad := by
  letI : MetricSpace M := F.metricSpace
  obtain ⟨r, K, hr, -, hK⟩ := F.exists_lipschitzOnWith_extChartAt_symm
    (P.toManifold P.center)
  refine ⟨r, K, hr, ?_⟩
  intro z zc Drad hz hzc hzball hzcball hamp
  have hzball' : z ∈ ball P.center (P.seed.radius P.center) := inter_subset_left hz
  have hzcball' : zc ∈ ball P.center (P.seed.radius P.center) := inter_subset_left hzc
  have hzsrc : P.toManifold z ∈ (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source :=
    P.mapsTo_chart hzball'
  have hzcsrc : P.toManifold zc ∈ (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).source :=
    P.mapsTo_chart hzcball'
  have hzmem : extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.toManifold z) ∈
      ball (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
        (P.toManifold P.center)) r := by
    rw [mem_ball, dist_eq_norm]
    have hznorm : ‖P.readout z - P.readout P.center‖ < r := by linarith
    simpa only [CalibratedSeedWindow.readout, Function.comp_apply] using hznorm
  have hzcmem : extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.toManifold zc) ∈
      ball (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)
        (P.toManifold P.center)) r := by
    rw [mem_ball, dist_eq_norm]
    have hzcnorm : ‖P.readout zc - P.readout P.center‖ < r := by linarith
    simpa only [CalibratedSeedWindow.readout, Function.comp_apply] using hzcnorm
  have hXleft : ∀ _ : Unit,
      (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).symm
        (extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.toManifold z)) = P.toManifold z :=
    fun _ => (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).left_inv hzsrc
  have hcleft : (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).symm
      (extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.toManifold zc)) = P.toManifold zc :=
    (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).left_inv hzcsrc
  have hamp' : ∀ _ : Unit, ‖extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.toManifold z) -
      extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.toManifold zc)‖ ≤ Drad := by
    intro _
    simpa only [CalibratedSeedWindow.readout, Function.comp_apply] using hamp
  exact dist_le_of_chartBall_amplitude
    (Φ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center))
    (Ψ := (extChartAt 𝓘(ℝ, E) (P.toManifold P.center)).symm)
    (y₀ := extChartAt 𝓘(ℝ, E) (P.toManifold P.center) (P.toManifold P.center))
    (r := r) (K := K) (X := fun _ : Unit => P.toManifold z)
    (c := P.toManifold zc) (Drad := Drad) hK
    (fun _ => hzmem) hzcmem hXleft hcleft hamp' ()

/-! ## Window chart data: the node-position identity and the containment -/

variable {P : ℕ → CalibratedSeedWindow F u}

/-- **Window chart data node-position identity.**  The actual manifold point of a
retained window parameter is the chart-datum curve through the chart section
point of its transported label.  This is the node-position/path identity chain of
the amplitude lane, now in the window chart data context. -/
theorem windowChartData_toManifold_eq_chart_curve (W : WindowChartData P) (j : ℕ)
    (z : ℝ × (P j).seed.covector.ker) :
    (P j).toManifold z =
      (W.chartData j).Γ ((W.chartData j).σ ((W.parentEquiv j) z.2)) z.1 :=
  W.parent_curves j z.2 z.1

/-- **Window chart data ball containment.**  In the window chart data context, the
retained pairs of the j-th window satisfy the frozen core entry ball containment
of explicit radius K * Drad, and both endpoints are realized as chart-datum curves
through the transported chart section.  This is the composed hX input of the
frozen core entry bound with atlas-sourced constants. -/
theorem windowChartData_ballContainment (W : WindowChartData P) (j : ℕ) :
    letI : MetricSpace M := F.metricSpace
    ∃ (r : ℝ) (K : ℝ≥0), 0 < r ∧
      ∀ (z zc : ℝ × (P j).seed.covector.ker) {Drad : ℝ},
        z ∈ (P j).domain → zc ∈ (P j).domain →
        ‖(P j).readout z - (P j).readout (P j).center‖ < r / 2 →
        ‖(P j).readout zc - (P j).readout (P j).center‖ < r / 2 →
        ‖(P j).readout z - (P j).readout zc‖ ≤ Drad →
        dist ((P j).toManifold z) ((P j).toManifold zc) ≤ (K : ℝ) * Drad ∧
          (P j).toManifold z =
            (W.chartData j).Γ ((W.chartData j).σ ((W.parentEquiv j) z.2)) z.1 ∧
          (P j).toManifold zc =
            (W.chartData j).Γ ((W.chartData j).σ ((W.parentEquiv j) zc.2)) zc.1 := by
  letI : MetricSpace M := F.metricSpace
  obtain ⟨r, K, hr, hcont⟩ := calibratedWindow_ballContainment (P := P j)
  exact ⟨r, K, hr, fun z zc Drad hz hzc hzr hzcr hamp =>
    ⟨hcont z zc hz hzc hzr hzcr hamp,
      windowChartData_toManifold_eq_chart_curve W j z,
      windowChartData_toManifold_eq_chart_curve W j zc⟩⟩

end OTSelector.Reconstruction
