import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Geometry.Finsler.Calibration.Chart
import OTSelector.Geometry.Finsler.EndpointDistanceBranch
import OTSelector.Geometry.Finsler.EndpointInverse
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Chart
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerEnergy
import OTSelector.Geometry.Finsler.Geodesic.Proofs.LocalEquation
import OTSelector.Geometry.Finsler.LengthMetric

/-!
# Geometry.Finsler.AffineCalibrationTube

* **Conditions:** A supplied actual chart tube with affine expression of the original global potential and constant calibrated unit coordinate velocity.
* **Objects:** Derived potential differentiability, affine clock, actual unit length/distance and local endpoint-distance C2.
* **Proof detail:** Differentiate the affine chart expression, integrate the true unit velocity and apply the existing calibrated endpoint-branch theorem.

Mathematical sources:
- [J. C. Álvarez Paiva; A. C. Thompson, Volumes on Normed and Finsler Spaces, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/02AT.pdf#page=22): Section 4.2, Definition 4.11 and Proposition 4.12, p. 22.
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): The exact-one-form calibration principle specializes to this tube; the auxiliary affine tube is not constructed from an arbitrary rough potential.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerAffineCalibrationTube.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerAffineCalibrationTube`; the selected original proof blocks follow. -/
section

/-!
# Derived data of an actual affine calibration tube

The original global Lipschitz calibration has a supplied affine expression in an actual
chart tube. The central curve has the supplied constant coordinate velocity, paired to
one by that covector, and that velocity has original Finsler length one in the tube.
These data imply differentiability of the potential, its actual unit rate along the
curve, the original path-length and distance formulas, and calibrated minimality.

The endpoint-distance consumer derives these intermediate properties and feeds the
existing branch theorem. The tube and velocity data remain the same auxiliary geometric
data; this module does not construct them from a rough transport potential.
-/

open Set Filter Manifold Bundle Metric MeasureTheory
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- An actual affine chart expression makes the original manifold function differentiable
at each point of that open chart domain. -/
theorem mdifferentiableAt_of_affine_chart (old : M) {u : M → ℝ} {U : Set E}
    (hU : IsOpen U) (p : E →L[ℝ] ℝ) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    {x : M} (hx : x ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hUx : extChartAt 𝓘(ℝ, E) old x ∈ U) :
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u x := by
  have hχ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, E) (extChartAt 𝓘(ℝ, E) old) x :=
    mdifferentiableAt_extChartAt (by simpa only [extChartAt_source] using hx)
  have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
      (fun z ↦ p (extChartAt 𝓘(ℝ, E) old z) + C) x :=
    (p.differentiableAt.mdifferentiableAt.comp x hχ).add mdifferentiableAt_const
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_source old).mem_nhds hx,
    hχ.continuousAt.preimage_mem_nhds (hU.mem_nhds hUx)] with z hz hzU
  simpa only [(extChartAt 𝓘(ℝ, E) old).left_inv hz] using heq _ hzU

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual affine calibration tube implies all central differentiability, minimality,
saturation, and unit-rate data, without assuming any of those conclusions. -/
theorem affine_calibration_tube_data (hF : F.IsSmoothStronglyConvex)
    (old : M) {c : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : F.IsEulerLagrangeOn c univ)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : ∀ t ∈ Icc a b, c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t = v₀) :
    letI : MetricSpace M := F.metricSpace
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a) ∧
      F.lengthEDist (c a) (c b) = Manifold.pathELength 𝓘(ℝ, E) c a b ∧
      u (c b) - u (c a) = dist (c a) (c b) ∧
      (∀ t ∈ Icc a b, HasDerivAt (u ∘ c) 1 t) ∧
      (∀ t ∈ Icc a b, u (c t) = u (c a) + (t - a)) ∧
      Manifold.pathELength 𝓘(ℝ, E) c a b = ENNReal.ofReal (b - a) ∧
      dist (c a) (c b) = b - a := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  have hcsmooth : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ c :=
    contMDiffOn_univ.mp (hF.contMDiffOn_of_isEulerLagrangeOn hc)
  let J := c ⁻¹' (extChartAt 𝓘(ℝ, E) old).source
  have hJ : IsOpen J := (isOpen_extChartAt_source old).preimage hcsmooth.continuous
  have hcoord : ContDiffOn ℝ ∞ (extChartAt 𝓘(ℝ, E) old ∘ c) J :=
    contDiffOn_chart_curve old hcsmooth.contMDiffOn (fun _ ht ↦ ht)
  have hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a) :=
    mdifferentiableAt_of_affine_chart old hU p heq (hx a ⟨le_rfl, hab.le⟩)
      (hspace a ⟨le_rfl, hab.le⟩)
  have hrate (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt (u ∘ c) 1 t := by
    have hxt := (hcoord.contDiffAt (hJ.mem_nhds (hx t ht))).differentiableAt (by simp)
    have he : (u ∘ c) =ᶠ[𝓝 t]
        (fun r ↦ p ((extChartAt 𝓘(ℝ, E) old ∘ c) r) + C) := by
      filter_upwards [hJ.mem_nhds (hx t ht),
        hxt.continuousAt.preimage_mem_nhds (hU.mem_nhds (hspace t ht))] with r hr hrU
      simpa only [Function.comp_apply, (extChartAt 𝓘(ℝ, E) old).left_inv hr] using
        heq _ hrU
    have hd := (p.hasFDerivAt.comp_hasDerivAt t hxt.hasDerivAt).add_const C
    rw [hvelocity t ht, hp] at hd
    exact hd.congr_of_eventuallyEq he
  have haff (t : ℝ) (ht : t ∈ Icc a b) : u (c t) = u (c a) + (t - a) := by
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
      (hu.continuous.comp hcsmooth.continuous).continuousOn
      (fun r hr ↦ hrate r ⟨hr.1.le, hr.2.le.trans ht.2⟩)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume a t)
    simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one, Function.comp_apply] at he
    linarith
  have hspeed (t : ℝ) (ht : t ∈ Icc a b) :
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = 1 := by
    rw [F.speed_eq_chartLength old hJ (hx t ht) (fun _ hr ↦ hr)
      ((hcoord.contDiffAt (hJ.mem_nhds (hx t ht))).differentiableAt (by simp)),
      hvelocity t ht]
    exact hunit _ (hspace t ht)
  have hiso := F.isometry_Icc_of_unitSpeed_calibration hu
    (hcsmooth.contMDiffOn.of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) by simp))
    (fun t ht ↦ hspeed t ⟨ht.1.le, ht.2.le⟩)
    (C := u (c a) - a) (fun t ht ↦ by rw [haff t ht]; ring)
  have hmin := hF.lengthEDist_eq_pathELength_of_isometric_interval hab.le hiso
  have hdist : dist (c a) (c b) = b - a := by
    have hd := hiso.dist_eq ⟨a, le_rfl, hab.le⟩ ⟨b, hab.le, le_rfl⟩
    rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab.le), neg_sub] at hd
    exact hd
  refine ⟨hdu, hmin, ?_, hrate, haff, ?_, hdist⟩
  · rw [haff b ⟨hab.le, le_rfl⟩, hdist]
    ring
  · simpa only [ENNReal.coe_one, one_mul] using
      F.pathELength_eq_of_constant_speed (fun t ht ↦ hspeed t ⟨ht.1.le, ht.2.le⟩)

/-- Original endpoint distance is C2 at an actual affine calibration tube. Central
minimality, saturation, and differentiability are derived from the tube data. -/
theorem contDiffAt_endpointDistance_of_affine_tube_data (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {Γ : (E × E) → ℝ → M} {a b : ℝ} (hab : a < b)
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Γ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ z) ⟨a, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    (hG : ContMDiffOn 𝓘(ℝ, (E × E) × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩)
      (chartEnergyDomain old ×ˢ univ))
    {z₀ : E × E} (hz₀ : z₀ ∈ chartEnergyDomain old)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : ∀ t ∈ Icc a b, Γ z₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1) {C : ℝ}
    (heq : ∀ y ∈ U, u ((extChartAt 𝓘(ℝ, E) old).symm y) = p y + C)
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ Γ z₀) t = v₀) :
    ContDiffAt ℝ 2 (fun q : E × E ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal)
      (chartEndpointMap old Γ b z₀) := by
  obtain ⟨hdu, hmin, hsat, _⟩ := hF.affine_calibration_tube_data old hab
    (hEL z₀ hz₀) hu hx hU p hp hunit heq hspace hvelocity
  exact hF.contDiffAt_endpointDistance_of_affine_calibrated_tube hcomplete old hab
    hEL hinit hG hz₀ hmin hu hsat hdu hx hU hsub p hp hunit heq hspace hvelocity

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
