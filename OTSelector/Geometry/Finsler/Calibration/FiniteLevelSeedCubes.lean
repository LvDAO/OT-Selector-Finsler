import OTSelector.Analysis.Normed.BallCubeEmbedding
import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteLevelSeeds
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.LengthMetric
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerFiniteLevelSeedCubes.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerFiniteLevelSeedCubes`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.Calibration.FiniteLevelSeedCubes

* **Conditions:** A compact chart core with a C1 value/derivative extension of the potential and a positive common two-sided calibrated reach, at a fixed level.
* **Objects:** A finite family of actual level-seed sections and injective affine cube coordinates with one finite inverse-Lipschitz constant.
* **Proof detail:** Construct transverse level charts using nonvanishing calibrated differential, take a finite subcover, then identify each finite-dimensional kernel with its basis coordinates and enlarge constants finitely.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [Terence Tao, An Epsilon of Room, I: Real Analysis (author preliminary version)](https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110): Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products).
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II](https://www.jirka.org/ra/realanal2.pdf): Sections 8.3–8.4, total derivative, chain rule and mean-value bounds; Section 8.6, higher derivatives.

Source relation (derived): A finite-cover and coordinate specialization of calibrated level sections; the shared cube constant is an elementary finite-family consequence.
-/

/-!
# Fixed cubes for the actual finite original level seeds

The original finite level-section producer supplies actual label balls. Their
explicit affine cube coordinates have one finite inverse Lipschitz constant
across the whole finite family; the original sections and covering are retained.
-/

open Set Metric Manifold
open scoped Topology ContDiff NNReal BigOperators

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The actual finite level seeds admit bounded cube coordinates with one common
inverse Lipschitz constant, without changing their labels or original covering. -/
theorem exists_finite_original_levelSeedCubes (hF : F.IsSmoothStronglyConvex)
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
        ⋃ x ∈ J, σ x '' (ball 0 (a x) ∩ (σ x) ⁻¹' K) ∧
      ∃ (Q : ∀ x : {x : H // x ∈ J}, (fderiv ℝ G (x.val : E)).ker →
          Fin (Module.finrank ℝ (fderiv ℝ G (x.val : E)).ker) → ℝ) (L : ℝ),
        0 < L ∧ ∀ x : {x : H // x ∈ J},
          Continuous (Q x) ∧ Function.Injective (Q x) ∧
          MapsTo (Q x) (ball 0 (a x.val)) (Icc 0 1) ∧
          ∀ w z, ‖w - z‖ ≤ L * ‖Q x w - Q x z‖ := by
  obtain ⟨J, a, C, σ, hdata, hcover⟩ :=
    hF.exists_finite_original_levelSeeds hcomplete old hK hU hKU hUt hu hG hval hmatch
      hδ hpartners c
  let H := K ∩ {x | G x = c}
  let T := {x : H // x ∈ J}
  have hlocal (x : T) := OTSelector.Reconstruction.exists_labelCubeCoordinates_on_ball
    (Module.finBasis ℝ (fderiv ℝ G (x.val : E)).ker) (hdata x.val x.property).1
  choose Q L hQ hinj hL hmap hbound using hlocal
  let L₀ := (∑ x : T, L x) + 1
  have hL₀ : 0 < L₀ := by
    have hsum : 0 ≤ ∑ x : T, L x := Finset.sum_nonneg (fun x _ ↦ (hL x).le)
    dsimp only [L₀]
    linarith
  refine ⟨J, a, C, σ, hdata, hcover, Q, L₀, hL₀, fun x ↦
    ⟨hQ x, hinj x, hmap x, fun w z ↦ ?_⟩⟩
  have hx : L x ≤ L₀ := by
    have hsum := Finset.single_le_sum (f := L)
      (fun y (_ : y ∈ (Finset.univ : Finset T)) ↦ (hL y).le) (Finset.mem_univ x)
    dsimp only [L₀]
    linarith
  exact (hbound x w z).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
