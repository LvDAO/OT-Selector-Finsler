import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.CalibratedVelocity
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Basic
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.Geodesic.Energy
import OTSelector.Geometry.Finsler.Geodesic.Uniqueness
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.LipschitzDifferential

/-!
# Geometry.Finsler.CalibratedConstantSpeed

* **Conditions:** Actual original energy dynamics, global length minimality on a fixed interval and saturation of a Lipschitz potential.
* **Objects:** The true positive speed determined by endpoints, saturated affine clocks and uniqueness without changing the original time parameterization.
* **Proof detail:** Use energy conservation and constant-speed length, derive scalar saturation on the whole interval, then normalize only the velocity comparison algebraically.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, Definition 4.1 and Lemma 4.2, pp. 313–314; equations (4–1), (4–2) and the canonical-lift spray interpretation.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): The stated result is a derived local construction from the cited principles. The exact original family, branch, coordinate maps and hypotheses remain those in the full source telescope.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerCalibratedConstantSpeed.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerCalibratedConstantSpeed`; the selected original proof blocks follow. -/
section

/-!
# Calibrated minimizing geodesics with their original constant speed

The original energy equation supplies constant positive speed. Global original-length
minimality fixes that speed from the endpoint distance and time interval. Saturation
of a Lipschitz potential then identifies the actual initial covector and tangent,
without changing either the metric or the time parametrization.
-/

open Set Filter Metric Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry

/-- Endpoint saturation of a real Lipschitz function fixes its rate on the whole interval. -/
theorem eq_affine_of_lipschitz_saturated {f : ℝ → ℝ} {K : ℝ≥0} {a b : ℝ}
    (hf : LipschitzWith K f) (hsat : f b - f a = (K : ℝ) * (b - a)) :
    ∀ t ∈ Icc a b, f t = f a + (K : ℝ) * (t - a) := by
  intro t ht
  have hupper := hf.le_add_mul t a
  have hlower := hf.le_add_mul b t
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.1)] at hupper
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hlower
  nlinarith

/-- An existing initial derivative agrees with the saturated constant rate. -/
theorem deriv_eq_of_lipschitz_saturated {f : ℝ → ℝ} {K : ℝ≥0} {a b d : ℝ}
    (hab : a < b) (hf : LipschitzWith K f)
    (hsat : f b - f a = (K : ℝ) * (b - a)) (hd : HasDerivAt f d a) : d = K := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hlin : HasDerivAt (fun t : ℝ ↦ f a + (K : ℝ) * (t - a)) K a := by
    simpa only [Pi.add_apply, id_eq, sub_zero, zero_add, mul_one] using!
      (hasDerivAt_const a (f a)).add
      (((hasDerivAt_id a).sub_const a).const_mul (K : ℝ))
  have heq := eq_affine_of_lipschitz_saturated hf hsat
  have hw : HasDerivWithinAt f K (Icc a b) a :=
    hlin.hasDerivWithinAt.congr_of_mem heq ha
  exact (uniqueDiffOn_Icc hab a ha).eq_deriv (Icc a b) hd.hasDerivWithinAt hw

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M}

namespace ContinuousFinslerNorm.IsSmoothStronglyConvex

/-- At any common positive original speed, one length-bounded saturated covector
selects at most one actual tangent vector. -/
theorem tangent_velocity_eq_of_calibration (hF : F.IsSmoothStronglyConvex) (x : M)
    (p : TangentSpace 𝓘(ℝ, E) x →L[ℝ] ℝ) {v w : TangentSpace 𝓘(ℝ, E) x}
    {s : ℝ≥0} (hs : 0 < s) (hv : F.toFun ⟨x, v⟩ = s) (hw : F.toFun ⟨x, w⟩ = s)
    (hbound : ∀ z : TangentSpace 𝓘(ℝ, E) x, p z ≤ (F.toFun ⟨x, z⟩ : ℝ))
    (hpv : p v = s) (hpw : p w = s) : w = v := by
  have hs0 : (s : ℝ) ≠ 0 := ne_of_gt (NNReal.coe_pos.mpr hs)
  have hunit (z : TangentSpace 𝓘(ℝ, E) x) (hz : F.toFun ⟨x, z⟩ = s) :
      F.toFun ⟨x, (s : ℝ)⁻¹ • z⟩ = 1 := by
    rw [F.map_smul, hz]
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg s.coe_nonneg, NNReal.coe_one]
    exact inv_mul_cancel₀ hs0
  have hnorm (z : TangentSpace 𝓘(ℝ, E) x) (hz : p z = s) :
      p ((s : ℝ)⁻¹ • z) = 1 := by
    rw [_root_.map_smul, hz, smul_eq_mul, inv_mul_cancel₀ hs0]
  have heq := hF.tangent_unit_velocity_eq_of_calibration x p (hunit v hv) (hunit w hw)
    hbound (hnorm v hpv) (hnorm w hpw)
  exact (smul_right_injective _ (inv_ne_zero hs0)) heq

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

/-- A complete original Euler--Lagrange curve is globally Lipschitz with its own
constant speed, derived from the original derivative-integral path length. -/
theorem lipschitzWith_of_isEulerLagrangeOn_univ (hF : F.IsSmoothStronglyConvex)
    {c : ℝ → M} (hc : F.IsEulerLagrangeOn c univ) (a : ℝ) :
    letI : MetricSpace M := F.metricSpace
    LipschitzWith (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩)) c := by
  let : MetricSpace M := F.metricSpace
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  let : ∀ x : M, ENormSMulClass ℝ (TangentSpace 𝓘(ℝ, E) x) := F.enormSMulClass
  let s := F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩)
  have hs (t : ℝ) : F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = s :=
    hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_univ (mem_univ t) (mem_univ a)
  have hreg : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) 1 c := fun t ↦
    (hF.contMDiffAt_of_isEulerLagrangeAt (hc t (mem_univ _))).of_le (by simp)
  have hle (u v : ℝ) (huv : u ≤ v) : edist (c u) (c v) ≤ (s : ℝ≥0∞) * edist u v := by
    have h := riemannianEDist_le_pathELength hreg.contMDiffOn rfl rfl huv
    change F.lengthEDist (c u) (c v) ≤ _ at h
    rw [F.pathELength_eq_of_constant_speed (fun t _ ↦ hs t)] at h
    change F.lengthEDist (c u) (c v) ≤ _
    rw [edist_dist, Real.dist_eq, abs_sub_comm u v, abs_of_nonneg (sub_nonneg.mpr huv)]
    exact h
  intro u v
  rcases le_total u v with huv | hvu
  · exact hle u v huv
  · simpa only [edist_comm] using hle v u hvu


set_option backward.isDefEq.respectTransparency false in
/-- A saturated globally minimizing original EL segment calibrates its actual initial
velocity at its original speed, with no unit-speed or reparametrization premise. -/
theorem mfderiv_initial_eq_speed_of_calibrated_minimizer (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c : ℝ → M} {a b : ℝ} (hab : a < b) (hc : F.IsEulerLagrangeOn c univ)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (c a) (c b) = pathELength 𝓘(ℝ, E) c a b)
    (hsat : letI : MetricSpace M := F.metricSpace; u (c b) - u (c a) = dist (c a) (c b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1) =
        (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩) : ℝ) := by
  let : MetricSpace M := F.metricSpace
  let s := F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩)
  have hdist : dist (c a) (c b) = (s : ℝ) * (b - a) :=
    F.dist_eq_mul_sub_of_constant_speed hab.le (fun t _ ↦
      hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_univ (mem_univ t) (mem_univ a))
      hmin
  have hLip : LipschitzWith s (u ∘ c) := by
    simpa only [one_mul] using hu.comp (hF.lipschitzWith_of_isEulerLagrangeOn_univ hc a)
  have hca := (hF.contMDiffAt_of_isEulerLagrangeAt (hc a (mem_univ _))).mdifferentiableAt
    (by simp)
  have hd : DifferentiableAt ℝ (u ∘ c) a :=
    mdifferentiableAt_iff_differentiableAt.mp (hdu.comp a hca)
  have he : deriv (u ∘ c) a = mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1) := by
    have h := mfderiv_comp_apply a hdu hca (1 : ℝ)
    rw [mfderiv_eq_fderiv] at h
    exact h
  exact he.symm.trans
    (deriv_eq_of_lipschitz_saturated hab hLip (hsat.trans hdist) hd.hasDerivAt)

set_option backward.isDefEq.respectTransparency false in
/-- Original globally minimizing complete EL curves with the same calibrated endpoint
pair agree in their original common time interval and hence at every real time. -/
theorem eq_of_complete_calibrated_minimizers (hF : F.IsSmoothStronglyConvex)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {c d : ℝ → M} {a b : ℝ} (hab : a < b)
    (hc : F.IsEulerLagrangeOn c univ) (hd : F.IsEulerLagrangeOn d univ)
    (hstart : c a = d a) (hend : c b = d b)
    (hcmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (c a) (c b) = pathELength 𝓘(ℝ, E) c a b)
    (hdmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (d a) (d b) = pathELength 𝓘(ℝ, E) d a b)
    (hsat : letI : MetricSpace M := F.metricSpace; u (c b) - u (c a) = dist (c a) (c b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)) : c = d := by
  let : MetricSpace M := F.metricSpace
  let s := F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩)
  let r := F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨a, (1 : ℝ)⟩)
  have hcdis : dist (c a) (c b) = (s : ℝ) * (b - a) :=
    F.dist_eq_mul_sub_of_constant_speed hab.le (fun t _ ↦
      hF.speed_eq_of_isEulerLagrangeOn hc isPreconnected_univ (mem_univ t) (mem_univ a))
      hcmin
  have hddis : dist (d a) (d b) = (r : ℝ) * (b - a) :=
    F.dist_eq_mul_sub_of_constant_speed hab.le (fun t _ ↦
      hF.speed_eq_of_isEulerLagrangeOn hd isPreconnected_univ (mem_univ t) (mem_univ a))
      hdmin
  have hrs : r = s := by
    apply NNReal.coe_injective
    rw [← hstart, ← hend] at hddis
    nlinarith [sub_pos.mpr hab]
  have hdu' : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (d a) := by rwa [← hstart]
  have hdsat : u (d b) - u (d a) = dist (d a) (d b) := by rwa [← hstart, ← hend]
  let p : TangentSpace 𝓘(ℝ, E) (c a) →L[ℝ] ℝ := mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
  let v := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c a 1
  let w := mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d a 1
  have hw : F.toFun ⟨c a, w⟩ = s := by
    rw [hstart]
    exact hrs
  have hpv : p v = s :=
    hF.mfderiv_initial_eq_speed_of_calibrated_minimizer hu hab hc hcmin hsat hdu
  have hpw : p w = s := by
    have h := hF.mfderiv_initial_eq_speed_of_calibrated_minimizer hu hab hd hdmin hdsat hdu'
    change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d a 1) = (s : ℝ)
    rw [hstart]
    exact h.trans (congrArg (fun q : ℝ≥0 ↦ (q : ℝ)) hrs)
  have hbound (z : TangentSpace 𝓘(ℝ, E) (c a)) : p z ≤ (F.toFun ⟨c a, z⟩ : ℝ) := by
    have h := hF.abs_mfderiv_le_finsler_of_lipschitz hu hdu z
    exact (le_abs_self (p z)).trans (by simpa only [p, NNReal.coe_one, one_mul] using! h)
  have hs : 0 < s := F.speed_pos_of_isEulerLagrangeAt (hc a (mem_univ _))
  have hv := hF.tangent_velocity_eq_of_calibration (c a) p hs rfl hw hbound hpv hpw
  have htan : tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨a, (1 : ℝ)⟩ =
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) d ⟨a, (1 : ℝ)⟩ :=
    TotalSpace.ext hstart (heq_of_eq hv.symm)
  funext t
  exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ hc hd
    (mem_univ a) htan (mem_univ t)

end ContinuousFinslerNorm.IsSmoothStronglyConvex
end OTSelector.Geometry

end
end
