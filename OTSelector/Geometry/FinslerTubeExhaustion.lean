import OTSelector.MeasureTheory.RegularCompactExhaustion
import OTSelector.Geometry.Finsler.RegularTube
import OTSelector.Geometry.FinslerCompleteFocalFinite
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

/-!
# Countably many actual regular Finsler tubes

The original family's finite focal set is derived from its Jacobi data. Compact
regular subsets exhaust the central minimizing segment outside that set, with vanishing
lost mass for the original atomless time measure. Each compact subset has a common
C2 manifold tube for the same family. This is time localization, not a completed
measurable transport atlas or a new nonfocal assumption on the population.
-/

open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [FiniteDimensional ℝ W] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- The same complete normal family's derived finite focal set admits compact
localization with arbitrarily small lost time mass, and an actual C2 tube at each stage. -/
theorem exists_regularTube_exhaustion_of_completeFamily (hF : F.IsSmoothStronglyConvex)
    (hdim : Module.finrank ℝ W + 1 = Module.finrank ℝ E)
    {Γ : W → ℝ → M} {B : Set W} (hB : IsOpen B)
    (hEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hG : ContMDiffOn 𝓘(ℝ, W × ℝ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) 2
      (fun q ↦ tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.1) ⟨q.2, (1 : ℝ)⟩) (B ×ˢ univ))
    {C₀ : ℝ} (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = C₀)
    {w₀ : W} (hw : w₀ ∈ B)
    (hrank : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      Function.Injective (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀))
    (hpair : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      ∀ ξ η : W, canonicalPhasePairing
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ ξ)
        (fderiv ℝ (fun w ↦ F.chartMomentumFamily old Γ (w, t)) w₀ η) = 0)
    (hnormal : ∀ (old : M) (t : ℝ), Γ w₀ t ∈ (extChartAt 𝓘(ℝ, E) old).source →
      ∀ ξ : W, (F.chartMomentumFamily old Γ (w₀, t)).2
        (fderiv ℝ (fun w ↦ extChartAt 𝓘(ℝ, E) old (Γ w t)) w₀ ξ) = 0)
    {a b : ℝ}
    (hiso : letI : MetricSpace M := F.metricSpace; Isometry (fun t : Icc a b ↦ Γ w₀ t))
    (μ : Measure ℝ) [NullSingletonClass μ] (hμ : μ (Icc a b) ≠ (∞ : ℝ≥0∞)) :
    ∃ K : ℕ → Set ℝ, (∀ n, IsCompact (K n)) ∧ Monotone K ∧
      (∀ n, K n ⊆ {t ∈ Icc a b |
        HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀}) ∧
      (⋃ n, K n) = {t ∈ Icc a b |
        HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀} ∧
      Tendsto (fun n ↦ μ (Icc a b \ K n)) atTop (𝓝 0) ∧
      ∀ n, ∃ (T : Set ℝ) (V : Set W) (e : OpenPartialHomeomorph (ℝ × W) M),
        IsOpen T ∧ IsOpen V ∧ K n ⊆ T ∧ w₀ ∈ V ∧ T ×ˢ V ⊆ univ ×ˢ B ∧
        (e : ℝ × W → M) = (fun q ↦ Γ q.2 q.1) ∧ e.source = T ×ˢ V ∧
        e.target = (fun q : ℝ × W ↦ Γ q.2 q.1) '' (T ×ˢ V) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) 2 e e.source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) 2 e.symm e.target := by
  let S := {t ∈ Icc a b |
    ¬HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀}
  have hS : S.Finite := hF.finite_noninjective_manifoldPosition_of_completeFamily
    hdim hB hEL hG henergy hw hrank hpair hnormal isCompact_Icc
  obtain ⟨K, hc, hm, hs, hu, _, hmass⟩ :=
    exists_compact_exhaustion_sdiff_null μ isCompact_Icc hS.isClosed hμ (hS.measure_zero μ)
  have hregular : Icc a b \ S = {t ∈ Icc a b |
      HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀} := by
    ext t
    simp only [Set.mem_sdiff, mem_ofPred_eq, S]
    tauto
  have hs' (n : ℕ) : K n ⊆ {t ∈ Icc a b |
      HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) w₀} :=
    hregular ▸ hs n
  refine ⟨K, hc, hm, hs', hu.trans hregular, hmass, ?_⟩
  intro n
  exact hF.exists_regular_manifoldTube_of_completeFamily hdim hB hEL hG hw hiso
    (hc n) (fun _ ht ↦ (hs' n ht).1)
    (fun t _ old hx ↦ hnormal old t hx) (fun _ ht ↦ (hs' n ht).2)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
