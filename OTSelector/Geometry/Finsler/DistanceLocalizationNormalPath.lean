import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.DistanceLocalizationPullbackLength
import OTSelector.Geometry.Finsler.DistanceLocalizationSmoothLipschitz
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Lipschitz
import OTSelector.Geometry.Finsler.Geodesic.MetricMinimizerComparison
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerDistanceLocalizationNormalPath.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerDistanceLocalizationNormalPath`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.DistanceLocalizationNormalPath

* **Conditions:** A compact portion of a smooth parameter map has a unit nonzero reference velocity; a Lipschitz path has uniformly small reference-velocity perturbation normal almost everywhere.
* **Objects:** A uniform quadratic upper bound on original endpoint distance minus elapsed reference time.
* **Proof detail:** Apply the compact pullback-length Taylor inequality almost everywhere, integrate its actual speed bound and use the Lipschitz length–distance comparison.

Mathematical sources:
- [Jiří Lebl, Basic Analysis I: Introduction to Real Analysis, Volume I](https://www.jirka.org/ra/html/sec_taylor.html): Section 4.3, Theorem 4.3.2 (Taylor), Exercise 4.3.5 and its finite-differentiability footnote (Peano remainder).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 26](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=18): Section 262Q, Rademacher theorem and proof, pp. 18–20; Section 262B(c), p. 10 (Lipschitz implies absolutely continuous on bounded intervals).
- [D. H. Fremlin, Measure Theory, Volume 2, Chapter 22](https://www1.essex.ac.uk/maths/people/fremlin/chap22.pdf#page=29): Section 225E, p. 29 (absolute continuity and indefinite integral); Section 225F, p. 30 (integration by parts).
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, in Riemann–Finsler Geometry, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=11): Section 4, p. 313: the length integral, induced distance and minimizing curves.

Source relation (derived): An integrated normal-variation bound for actual paths; no injectivity or global minimizing foliation is assumed.
-/

/-!
# Distance control for actual normal parameter paths

A compact part of a smooth manifold map gives a common quadratic distance
bound for Lipschitz parameter paths whose perturbation of a unit reference
velocity is normal almost everywhere. All lengths and distances are those of
the original Finsler structure. No injectivity of the parameter map is used.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E V M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Uniform normal speed control integrates to the original distance estimate
for every Lipschitz path in the same compact parameter set. -/
theorem exists_uniform_normal_path_distance_upper (hF : F.IsSmoothStronglyConvex)
    {f : V → M} {U K : Set V} (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ, V) 𝓘(ℝ, E) ∞ f U)
    (hK : IsCompact K) (hKU : K ⊆ U) (v₀ : V)
    (hunit : ∀ q ∈ K, F.mapVariationLength f v₀ (q, 0) = 1) :
    ∃ r > 0, ∃ C : ℝ≥0, ∀ {a b : ℝ}, a ≤ b →
      ∀ {z : ℝ → V} {L : ℝ≥0}, LipschitzOnWith L z (Icc a b) →
      MapsTo z (Icc a b) K → ∀ {d : ℝ}, 0 ≤ d → d ≤ r →
      (∀ᵐ s ∂volume.restrict (Ioo a b), ‖deriv z s - v₀‖ ≤ d ∧
        (fderiv ℝ (fun w : TangentSpace 𝓘(ℝ, E) (f (z s)) ↦
            (F.toFun ⟨f (z s), w⟩ : ℝ))
          (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f (z s) v₀))
            (mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f (z s) (deriv z s - v₀)) = 0) →
      (F.lengthEDist (f (z a)) (f (z b))).toReal - (b - a) ≤
        (b - a) * (C : ℝ) * d ^ 2 := by
  let : MetricSpace M := F.metricSpace
  have hne (q : V) (hq : q ∈ K) : mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q v₀ ≠ 0 := by
    intro hz
    have hh := hunit q hq
    change (F.toFun ⟨f q, mfderiv 𝓘(ℝ, V) 𝓘(ℝ, E) f q (v₀ + (0 : V))⟩ : ℝ) = 1 at hh
    rw [add_zero, hz, F.map_zero] at hh
    norm_num at hh
  obtain ⟨r, hr, C, hb⟩ := hF.exists_uniform_mapVariationLength_upper_of_momentum
    hU hf hK hKU v₀ hne
  obtain ⟨Cf, hCf⟩ := F.exists_lipschitzOnWith_on_compact_of_contMDiffOn hK hU hKU
    (hf.of_le (by simp))
  refine ⟨r, hr, C, ?_⟩
  intro a b hab z L hz hzK d hd hdr hnormal
  have hc : LipschitzOnWith (Cf * L) (f ∘ z) (Icc a b) := hCf.comp hz hzK
  have hi := hF.intervalIntegrable_speed_of_lipschitzOnWith hab hc
  have hspeed : ∀ᵐ s ∂volume.restrict (Ioo a b),
      (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f ∘ z) ⟨s, (1 : ℝ)⟩) : ℝ) ≤
        1 + (C : ℝ) * d ^ 2 := by
    filter_upwards [hnormal,
      ae_restrict_of_ae (hz.ae_differentiableWithinAt_of_mem (μ := volume)),
      ae_restrict_mem measurableSet_Ioo] with s hs hsd hsI
    have hsd' := (hsd (Ioo_subset_Icc_self hsI)).differentiableAt
      (Icc_mem_nhds hsI.1 hsI.2)
    have hq := hzK (Ioo_subset_Icc_self hsI)
    have hp := hb (z s) hq (deriv z s - v₀) (hs.1.trans hdr) hs.2
    rw [hunit (z s) hq] at hp
    have hzD : HasDerivAt z (v₀ + (deriv z s - v₀)) s := by
      rw [show v₀ + (deriv z s - v₀) = deriv z s by abel]
      exact hsd'.hasDerivAt
    rw [F.mapVariationLength_eq_speed
      ((hf.contMDiffAt (hU.mem_nhds (hKU hq))).mdifferentiableAt (by simp)) hzD] at hp
    exact hp.trans (add_le_add_right (mul_le_mul_of_nonneg_left
      (sq_le_sq₀ (norm_nonneg _) hd |>.2 hs.1) C.coe_nonneg) 1)
  have hspeed' : ∀ᵐ s ∂volume.restrict (Icc a b),
      (F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (f ∘ z) ⟨s, (1 : ℝ)⟩) : ℝ) ≤
        1 + (C : ℝ) * d ^ 2 := by
    rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
  have hbound := intervalIntegral.integral_mono_ae_restrict hab hi
    (intervalIntegrable_const (c := 1 + (C : ℝ) * d ^ 2)) hspeed'
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  have hdist := (hF.dist_le_integral_speed_of_lipschitzOnWith hab hc).trans hbound
  change (F.lengthEDist (f (z a)) (f (z b))).toReal ≤ _ at hdist
  nlinarith

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
