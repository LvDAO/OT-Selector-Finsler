import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11LevelCoordinates
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.FiniteLevelPatches

/-!
# Geometry.Finsler.C11FiniteLevelSeeds

* **Conditions:** A compact original calibrated core, a fixed original potential level and any prescribed legal open core neighborhood.
* **Objects:** Finitely many actual Lipschitz C1 kernel sections covering exactly that level of the original potential.
* **Proof detail:** Use calibrated nonzero differential to construct level sections, identify their actual potential values on the core and take a finite compact subcover.

Mathematical sources:
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Zhongmin Shen, Landsberg Curvature, S-Curvature and Riemann Curvature, MSRI Publications 50 (2004)](https://library.slmath.org/books/Book50/files/08Sh.pdf#page=6): Section 2, p. 308, Legendre transformation, inverse Legendre transformation and equation (2–12).
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11FiniteLevelSeeds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11FiniteLevelSeeds`; the selected original proof blocks follow. -/
section

/-!
# Finite original level seeds on compact calibrated cores

Original calibrated partners make the actual extension differential nonzero at
every core point. Each potential level in that compact core therefore has a finite
cover by Lipschitz C1 sections inside any prescribed open core neighborhood. The
same sections cover the exact original-potential level, with no density assumption.
-/

open Set Metric Manifold
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every original potential level in a compact calibrated core has finitely many
actual C1 kernel sections. Their full label balls stay in the prescribed open
neighborhood, and restriction to the original core covers that exact original level. -/
theorem exists_finite_original_levelSeeds (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instFiniteSeedsLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instFiniteSeedsPartners : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    (c : ℝ) :
    let H := K ∩ {x | G x = c}
    ∃ (J : Finset H) (a : H → ℝ) (C : H → ℝ≥0)
      (σ : ∀ x : H, (fderiv ℝ G (x : E)).ker → E),
      (∀ x ∈ J, 0 < a x ∧ σ x 0 = (x : E) ∧
        ContDiffOn ℝ 1 (σ x) (ball 0 (a x)) ∧ LipschitzOnWith (C x) (σ x) (ball 0 (a x)) ∧
        MapsTo (σ x) (ball 0 (a x)) U ∧ (∀ w ∈ ball 0 (a x), G (σ x w) = c) ∧
        (∀ w ∈ ball 0 (a x), σ x w ∈ K →
          u ((extChartAt 𝓘(ℝ, E) old).symm (σ x w)) = c) ∧
        HasFDerivAt (σ x) (fderiv ℝ G (x : E)).ker.subtypeL 0 ∧
        InjOn (σ x) (ball 0 (a x)) ∧
        Module.finrank ℝ (fderiv ℝ G (x : E)).ker + 1 = Module.finrank ℝ E ∧
        ∀ w ∈ ball 0 (a x), Function.Injective (fderiv ℝ (σ x) w)) ∧
      K ∩ {x | u ((extChartAt 𝓘(ℝ, E) old).symm x) = c} =
        ⋃ x ∈ J, σ x '' (ball 0 (a x) ∩ (σ x) ⁻¹' K) := by
  have hp : ∀ x ∈ K, fderiv ℝ G x ≠ 0 := by
    intro x hx
    exact (hF.exists_original_levelCoordinates_of_calibrated_core hcomplete old
      (hKU.trans hUt) hu hG hval hmatch hδ hpartners hx).1
  obtain ⟨J, a, C, σ, hdata, hcover⟩ :=
    exists_finite_lipschitz_levelPatches hK hU hKU hG hp c
  refine ⟨J, a, C, σ, ?_, ?_⟩
  · intro x hx
    obtain ⟨ha, hzero, hσ, hLip, hmap, hlevel, hder, hinj, hdim, himm⟩ := hdata x hx
    refine ⟨ha, hzero, hσ, hLip, hmap, hlevel, ?_, hder, hinj, hdim, himm⟩
    intro w hw hwK
    exact (hval hwK).symm.trans (hlevel w hw)
  · have heq : K ∩ {x | u ((extChartAt 𝓘(ℝ, E) old).symm x) = c} =
        K ∩ {x | G x = c} := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, (hval hx.1).trans hx.2⟩
      · intro hx
        exact ⟨hx.1, (hval hx.1).symm.trans hx.2⟩
    exact heq.trans hcover

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
