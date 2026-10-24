import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedBackwardIdentity
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.Geodesic.SmoothMinimizer
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Topology.MetricSpace.SaturatedCalibration
import OTSelector.Transport.Kantorovich.CalibratedEndpoints
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.InitialEndpointCover

* **Conditions:** A genuine regular initial endpoint and the actual contact cores/families covering the calibrated interior.
* **Objects:** Containment in countably many rational backward-time images of those actual core sections.
* **Proof detail:** Construct its forward minimizing segment, choose an intermediate rational time, locate its interior point in a core and use actual backward curve identity.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=29): Sections 4–4.1, Definition 4.2 and Proposition 4.3, p. 29; Lemma 4.5, pp. 30–31; Definition 4.6 and Lemma 4.8, pp. 31–32.
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/realanal.pdf#page=31): Section 1.2.2, Theorem 1.2.4, p. 31.
- [Gerald Teschl, Ordinary Differential Equations and Dynamical Systems (AMS 2012 author preliminary version)](https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61): Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerInitialEndpointCover.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerInitialEndpointCover`; the selected original proof blocks follow. -/
section

/-!
# Rational backward slices covering actual regular initial endpoints

Every genuine regular initial endpoint has a forward calibrated minimizing segment.
A strictly intermediate rational time lies in the actual calibrated interior and hence
in one of the supplied coordinate cores. The actual initial momentum of that core's
complete family identifies its backward value with the original endpoint. No separate
backward identity, chosen curve, countability or measure hypothesis is supplied.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Actual coordinate families covering the calibrated interior cover every regular
initial endpoint by rational backward slices. Each slice retains the genuine endpoint
condition and exact original potential and distance clocks. The supplied families need
only their actual complete EL equations, initial points and actual potential momenta. -/
theorem calibratedInitialEndpoints_regular_subset_iUnion_backward
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instInitialCoverLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    (old : ι → M) (K : ι → Set E) (Γ : ι → E → ℝ → M)
    (hK : ∀ i, K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target)
    (hcover : let _instInitialCoverUnion : MetricSpace M := F.metricSpace
      calibratedInterior u ⊆ ⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i)
    (hfamily : ∀ i x, x ∈ K i →
      F.IsEulerLagrangeOn (Γ i x) univ ∧
      Γ i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
      F.chartMomentumFamily (old i) (Γ i) (x, 0) =
        (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) x)) :
    let _instInitialCoverMetric : MetricSpace M := F.metricSpace
    calibratedInitialEndpoints u ∩ F.potentialRegularDomain u ⊆
      ⋃ i, ⋃ q : ℚ, (fun x ↦ Γ i x (-(q : ℝ))) ''
        (K i ∩ {x | Γ i x (-(q : ℝ)) ∈
            calibratedInitialEndpoints u ∩ F.potentialRegularDomain u ∧
          u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - u (Γ i x (-(q : ℝ))) = q ∧
          dist (Γ i x (-(q : ℝ))) ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = q}) := by
  let _instInitialCoverMetric : MetricSpace M := F.metricSpace
  let _instInitialCoverENorm : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  dsimp only
  intro x hx
  obtain ⟨y, hxy, hsat⟩ := hx.1.1
  obtain ⟨c, hc0, hcy, hcEL, _, hcunit, hciso, _⟩ :=
    hF.exists_smooth_lengthMetric_minimizer hcomplete hxy
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨q, hq0, hqd⟩ := exists_rat_btwn hdist
  have hqt : (q : ℝ) ∈ Ioo (0 : ℝ) (dist x y) := ⟨hq0, hqd⟩
  have hqt' : (q : ℝ) ∈ Icc (0 : ℝ) (dist x y) := ⟨hq0.le, hqd.le⟩
  have hsatc : u (c (dist x y)) - u (c 0) = dist x y := by
    simpa only [hcy, hc0] using hsat
  obtain ⟨hqinterior, hqdist⟩ :=
    calibratedInterior_of_calibrated_isometry hu hciso hsatc hqt
  obtain ⟨i, z, hz, hzc⟩ := mem_iUnion.mp (hcover hqinterior)
  obtain ⟨hΓEL, hΓ0, hΓp⟩ := hfamily i z hz
  have hsource : c (q : ℝ) ∈ (extChartAt 𝓘(ℝ, E) (old i)).source := by
    rw [← hzc]
    exact (extChartAt 𝓘(ℝ, E) (old i)).map_target (hK i hz)
  have hchart : extChartAt 𝓘(ℝ, E) (old i) (c (q : ℝ)) = z := by
    rw [← hzc]
    exact (extChartAt 𝓘(ℝ, E) (old i)).right_inv (hK i hz)
  have hdu := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu hqinterior
  have hp : eulerLagrangePhaseLift (F.chartEnergy (old i))
      (extChartAt 𝓘(ℝ, E) (old i) ∘ Γ i z) 0 =
        (extChartAt 𝓘(ℝ, E) (old i) (c (q : ℝ)),
          fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (extChartAt 𝓘(ℝ, E) (old i) (c (q : ℝ)))) := by
    rw [hchart]
    exact hΓp
  have hback := (hF.eq_timeShift_of_chartMomentum_at_calibrated_point (old i) hu
    hcEL hΓEL hdist hciso (by simpa only [sub_zero] using hsatc) hqt'
    (hcunit q) hdu hsource (hΓ0.trans hzc) hp).2
  have hbackx : Γ i z (-(q : ℝ)) = x := hback.trans hc0
  refine mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨q, z, ⟨hz, ?_⟩, hbackx⟩⟩
  refine ⟨hbackx.symm ▸ hx, ?_, ?_⟩
  · have hclock := eq_affine_of_lipschitz_saturated_isometry hu hciso
      (by simpa only [sub_zero] using hsatc)
    rw [hzc, hbackx, hclock q hqt', hc0]
    simp only [sub_zero, add_sub_cancel_left]
  · simpa only [hbackx, hzc, hc0] using hqdist

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
