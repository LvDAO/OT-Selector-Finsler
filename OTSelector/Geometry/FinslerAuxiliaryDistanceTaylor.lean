import OTSelector.Geometry.FinslerAuxiliaryDistanceJet
import OTSelector.Analysis.CubicTaylor

/-!
# Cubic distance expansion with a genuinely local auxiliary calibration

The global rough potential selects the central minimizer. Local auxiliary Finsler
calibration supplies the jet independently, and its C3 regularity gives a common cubic
remainder for both endpoint displacements. The auxiliary potential is never extended
as a globally Lipschitz function and need not agree with the rough potential nearby.
-/

open Set Filter Manifold Bundle Metric
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The original distance has full and kernel quadratic expansions with the same cubic
bound. Its global calibration and auxiliary local dual bound are separate inputs, and
original completeness constructs the smooth variation family internally. -/
theorem endpointDistance_taylor_of_auxiliary_curve (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) {c : ℝ → M} {I : Set ℝ} (hI : IsOpen I) (hconn : IsPreconnected I)
    (hc : F.IsEulerLagrangeOn c I) {a b : ℝ} (hab : a < b) (hseg : Icc a b ⊆ I)
    (hmin₀ : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
      F.lengthEDist (c a) (c b) = Manifold.pathELength 𝓘(ℝ, E) c a b)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hsat : letI : MetricSpace M := F.metricSpace
      u (c b) - u (c a) = dist (c a) (c b))
    (hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (c a))
    (hx : ∀ t ∈ Icc a b, c t ∈ (extChartAt 𝓘(ℝ, E) old).source)
    {U : Set E} (hU : IsOpen U) (hsub : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (p : E →L[ℝ] ℝ) {v₀ : E} (hp : p v₀ = 1)
    (hunit : ∀ x ∈ U, F.chartLength old (x, v₀) = 1)
    (hbound : ∀ x ∈ U, ∀ v : E, p v ≤ (F.chartLength old (x, v) : ℝ))
    (hspace : ∀ t ∈ Icc a b, (extChartAt 𝓘(ℝ, E) old ∘ c) t ∈ U)
    (hvelocity : ∀ t ∈ Icc a b, deriv (extChartAt 𝓘(ℝ, E) old ∘ c) t = v₀) :
    let d : E × E → ℝ := fun q ↦
      (F.lengthEDist ((extChartAt 𝓘(ℝ, E) old).symm q.1)
        ((extChartAt 𝓘(ℝ, E) old).symm q.2)).toReal
    let q₀ := ((extChartAt 𝓘(ℝ, E) old ∘ c) a, (extChartAt 𝓘(ℝ, E) old ∘ c) b)
    ∃ r > 0, ∃ K ≥ 0,
      (∀ α β : E, ‖(α, β)‖ ≤ r →
        |d (q₀ + (α, β)) - (b - a) - p (β - α) -
          (1 / 2 : ℝ) * ((F.chartEndpointCompliance old c a b).inverse
            (β - α) (β - α) - (p (β - α)) ^ 2 / (b - a))| ≤ K * ‖(α, β)‖ ^ 3) ∧
      ∀ α β : p.ker, ‖((α : E), (β : E))‖ ≤ r →
        |d (q₀ + ((α : E), (β : E))) - (b - a) -
          (1 / 2 : ℝ) * (F.chartLengthKernelCompliance old p c a b).inverse
            (β - α) (β - α)| ≤ K * ‖((α : E), (β : E))‖ ^ 3 := by
  obtain ⟨hC3, hzero, hfirst, hsecond, hkernel⟩ :=
    hF.endpointDistance_jet_of_auxiliary_curve hcomplete old hI hconn hc hab hseg
      hmin₀ hu hsat hdu hx hU hsub p hp hunit hbound hspace hvelocity
  obtain ⟨r, hr, K, hK, hrem⟩ := exists_quadratic_taylor_remainder_bound_of_contDiffAt hC3
  refine ⟨r, hr, K, hK, ?_, ?_⟩
  · intro α β hsmall
    have h := hrem (α, β) hsmall
    dsimp only at hzero
    rw [hzero, hfirst, hsecond] at h
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
      _root_.map_sub,
      pow_two, Real.norm_eq_abs] using h
  · intro α β hsmall
    have h := hrem ((α : E), (β : E)) hsmall
    dsimp only at hzero
    rw [hzero, hfirst, hkernel (α, β) (α, β)] at h
    simpa only [sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.fst, Prod.snd,
      show p (α : E) = 0 from α.property, show p (β : E) = 0 from β.property,
      sub_self, sub_zero, Real.norm_eq_abs] using h

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
