import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerConstantSpeedDistance.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerConstantSpeedDistance`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Geodesic.ConstantSpeedDistance

* **Conditions:** A curve with specified constant Finsler speed on an interval; the distance identities additionally assume the stated length-minimality equalities.
* **Objects:** Explicit path length and endpoint distance as speed times duration, including the absolute-time local identity.
* **Proof detail:** Integrate the constant speed, identify distance with the assumed minimizing length, and split the two possible time orders.

Mathematical sources:
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): Elementary integration and distance conversion; constant speed alone does not supply length minimality.
-/

/-!
# Original-distance formulas for constant-speed minimizing curves

An actual constant Finsler speed evaluates the derivative-integral path length.
Whenever a segment realizes the original length distance, that distance is speed
times elapsed time. On an interval where all subsegments minimize, the same
formula around any fixed interior center handles both time orientations.
-/

open Set MeasureTheory Manifold Metric
open scoped NNReal ENNReal ContDiff

noncomputable section

namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) 1 M]
  (F : ContinuousFinslerNorm E M)

/-- Constant actual Finsler speed evaluates the original derivative-integral path length. -/
theorem pathELength_eq_of_constant_speed {c : ℝ → M} {a b : ℝ} {s : ℝ≥0}
    (hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = s) :
    letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    Manifold.pathELength 𝓘(ℝ, E) c a b = (s : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
  let : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Ioo]
  calc
    _ = ∫⁻ _ in Ioo a b, (s : ℝ≥0∞) := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact congrArg (fun r : ℝ≥0 ↦ (r : ℝ≥0∞)) (hspeed t ht)
    _ = (s : ℝ≥0∞) * ENNReal.ofReal (b - a) := by
      rw [setLIntegral_const, Real.volume_Ioo]

variable [FiniteDimensional ℝ E] [T2Space M] [PreconnectedSpace M]

/-- If a constant-speed segment realizes the original length distance, its metric distance
is its actual Finsler speed times the elapsed time. -/
theorem dist_eq_mul_sub_of_constant_speed {c : ℝ → M} {a b : ℝ} {s : ℝ≥0}
    (hab : a ≤ b)
    (hspeed : ∀ t ∈ Ioo a b,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = s)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (c a) (c b) = Manifold.pathELength 𝓘(ℝ, E) c a b) :
    letI : MetricSpace M := F.metricSpace
    dist (c a) (c b) = (s : ℝ) * (b - a) := by
  change (F.lengthEDist (c a) (c b)).toReal = _
  rw [hmin, F.pathELength_eq_of_constant_speed hspeed, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]

/-- A constant-speed curve whose short ordered subsegments realize the original distance
has the exact distance formula in both time directions around the center. -/
theorem dist_eq_mul_abs_sub_of_locally_minimizing {c : ℝ → M} {t₀ δ : ℝ} {s : ℝ≥0}
    (hδ : 0 < δ)
    (hspeed : ∀ t ∈ Ioo (t₀ - δ) (t₀ + δ),
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨t, (1 : ℝ)⟩) = s)
    (hmin : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      ∀ u ∈ Icc (t₀ - δ) (t₀ + δ), ∀ v ∈ Icc (t₀ - δ) (t₀ + δ), u ≤ v →
        F.lengthEDist (c u) (c v) = Manifold.pathELength 𝓘(ℝ, E) c u v) :
    letI : MetricSpace M := F.metricSpace
    ∀ t ∈ Icc (t₀ - δ) (t₀ + δ), dist (c t₀) (c t) = (s : ℝ) * |t - t₀| := by
  let : MetricSpace M := F.metricSpace
  have ht₀ : t₀ ∈ Icc (t₀ - δ) (t₀ + δ) := ⟨by linarith, by linarith⟩
  have hsub : ∀ u ∈ Icc (t₀ - δ) (t₀ + δ), ∀ v ∈ Icc (t₀ - δ) (t₀ + δ),
      ∀ q ∈ Ioo u v,
        F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) c ⟨q, (1 : ℝ)⟩) = s := by
    intro u hu v hv q hq
    exact hspeed q ⟨hu.1.trans_lt hq.1, hq.2.trans_le hv.2⟩
  intro t ht
  rcases le_total t₀ t with hle | hle
  · rw [abs_of_nonneg (sub_nonneg.mpr hle)]
    exact F.dist_eq_mul_sub_of_constant_speed hle (hsub t₀ ht₀ t ht)
      (hmin t₀ ht₀ t ht hle)
  · rw [dist_comm, F.dist_eq_mul_sub_of_constant_speed hle (hsub t ht t₀ ht₀)
      (hmin t ht t₀ ht₀ hle), abs_of_nonpos (sub_nonpos.mpr hle)]
    ring

end OTSelector.Geometry.ContinuousFinslerNorm

end
end
