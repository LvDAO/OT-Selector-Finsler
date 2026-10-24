import OTSelector.Geometry.Manifold.ManifoldPositionRank
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.ManifoldFocalFinite.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.ManifoldFocalFinite`; the selected original proof blocks follow. -/
section

/-!
Conditions: A C1 parameter family, continuous central curve and the stated pointwise punctured isolation of rank failure in local charts.

Objects: A discrete intrinsic bad-time set, hence finitely many bad times on a compact interval.

Proof detail: Transfer rank through chart changes, obtain locally isolated failures and use compactness to exclude an infinite accumulation set.

Sources: Jiří Lebl, Section 8.3, Theorem 8.3.7, p. 38; Exercise 8.3.7, p. 45 (differentiate the inverse identity) (https://www.jirka.org/ra/realanal2.pdf#page=38); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Topological rank-finiteness consequence conditional on actual isolation; a Jacobi equation is not smuggled into the statement.
-/

/-!
# Compact-time finiteness of intrinsic position degeneracies

Local isolation may be proved using a different genuine chart at every time. Atlas
invariance transfers it to the intrinsic position-rank property; compactness then gives
finitely many exceptional times without a chart covering the whole segment.
-/

open Set Filter Manifold
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A locally isolating chart gives intrinsic isolation, with the actual manifold
family and original time unchanged. -/
theorem eventually_hasInjectiveManifoldPosition_of_chart
    {Γ : W → ℝ → M} {w₀ : W} {t₀ : ℝ} (old : M)
    (hc : ContinuousAt (Γ w₀) t₀)
    (hΓ : ∀ᶠ t in 𝓝 t₀, ContMDiffAt 𝓘(ℝ, W) 𝓘(ℝ, E) 1 (fun w ↦ Γ w t) w₀)
    (ho : Γ w₀ t₀ ∈ (extChartAt 𝓘(ℝ, E) old).source)
    (hi : ∀ᶠ t in 𝓝[≠] t₀, Function.Injective
      (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀)) :
    ∀ᶠ t in 𝓝[≠] t₀, HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀ := by
  have hs : ∀ᶠ t in 𝓝 t₀, Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source :=
    hc.preimage_mem_nhds ((isOpen_extChartAt_source old).mem_nhds ho)
  filter_upwards [hi, nhdsWithin_le_nhds hs, nhdsWithin_le_nhds hΓ] with t ht hs hΓt
  exact (hasInjectiveManifoldPosition_iff_of_contMDiffAt old hΓt hs).mpr ht

/-- Intrinsic position degeneracies are finite on every compact time set whenever
actual local position degeneracies are isolated in a legal chart around each time.
The chart may vary with time; no single-chart or global clock hypothesis is used. -/
theorem finite_noninjective_manifoldPosition_times
    {Γ : W → ℝ → M} {w₀ : W}
    (hc : Continuous (Γ w₀))
    (hΓ : ∀ t : ℝ, ContMDiffAt 𝓘(ℝ, W) 𝓘(ℝ, E) 1 (fun w ↦ Γ w t) w₀)
    {K : Set ℝ} (hK : IsCompact K)
    (hlocal : ∀ t ∈ K, ∃ old : M,
      Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source ∧
        ∀ᶠ s in 𝓝[≠] t, Function.Injective
          (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w s)) w₀)) :
    {t ∈ K | ¬HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀}.Finite := by
  have hcod : {t | HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀} ∈
      codiscreteWithin K := by
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro t ht
    obtain ⟨old, ho, hi⟩ := hlocal t ht
    filter_upwards [eventually_hasInjectiveManifoldPosition_of_chart old hc.continuousAt
      (Filter.Eventually.of_forall hΓ) ho hi] with s hs
    exact Or.inl hs
  exact (hK.finite_sdiff_of_mem_codiscreteWithin hcod).subset
    (fun _ ht ↦ ⟨ht.1, ht.2⟩)

end OTSelector.Geometry

end
end
