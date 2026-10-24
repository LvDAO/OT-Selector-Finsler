import OTSelector.Geometry.Manifold.FiniteCompactLevelPatches
import OTSelector.Geometry.Finsler.DistanceLocalizationUnitBranch
import OTSelector.Geometry.FinslerDistanceLocalizationSeparatedSeed
import OTSelector.Geometry.Finsler.InitialFamilyIdentity
import OTSelector.Geometry.Finsler.FlowLocalC2

/-!
# Actual original compact level patches with a whole-time quadratic upper bound

The original calibrated partners produce the legal normalization branch. Its
normalized complete flow equals the supplied original family at every true core
seed for all times, so the uniform auxiliary upper bound applies to its actual
endpoints. The larger section ball retains an open inner level image.
-/

open Set Filter Metric MeasureTheory Manifold Bundle
open scoped Topology ContDiff NNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Original calibrated core data produce an actual compact inner level patch
and a uniform quadratic bound for all its original family endpoints with a
positive time gap. No normalization branch or upper-cost estimate is supplied. -/
theorem exists_original_compact_level_upperPatch
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K U : Set E} (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hDG : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _inst : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {Γ : E → ℝ → M}
    (hΓ : ∀ y ∈ U, Γ y 0 = (extChartAt 𝓘(ℝ, E) old).symm y ∧
      F.IsEulerLagrangeOn (Γ y) univ ∧
      F.chartMomentumFamily old Γ (y, 0) = (y, fderiv ℝ G y))
    (lo hi : ℝ) {gap : ℝ} (hgap : 0 < gap) {x : E} (hx : x ∈ K) :
    let W := (fderiv ℝ G x).ker
    ∃ (a C : ℝ) (B : ℝ≥0) (σ : W → E) (V : Set E),
      0 < a ∧ 0 < C ∧ σ 0 = x ∧
      ContDiffOn ℝ 1 σ (ball 0 (2 * a)) ∧ LipschitzOnWith B σ (ball 0 (2 * a)) ∧
      MapsTo σ (ball 0 (2 * a)) U ∧ (∀ w ∈ ball 0 (2 * a), G (σ w) = G x) ∧
      HasFDerivAt σ W.subtypeL 0 ∧ InjOn σ (ball 0 (2 * a)) ∧
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ σ '' ball 0 a = V ∩ {y | G y = G x} ∧
      Module.finrank ℝ W + 1 = Module.finrank ℝ E ∧
      (∀ w ∈ ball 0 (2 * a), Function.Injective (fderiv ℝ σ w)) ∧
      ∀ w ∈ closedBall 0 a, σ w ∈ K → ∀ z ∈ closedBall 0 a, σ z ∈ K →
        ∀ s t : ℝ, lo ≤ s → t ≤ hi → gap ≤ t - s →
        (F.lengthEDist (Γ (σ w) s) (Γ (σ z) t)).toReal - (t - s) ≤ C * ‖z - w‖ ^ 2 := by
  obtain ⟨hp, eL, O, heL, hsource, hInv, hO, hxO, hlegal, hfixed⟩ :=
    hF.exists_original_unit_covector_branch_on_core hcomplete old (hKU.trans hUt)
      hu hG hmatch hδ hpartners hx
  obtain ⟨a, B, σ, V, ha, hσ0, hσ, hσLip, hmap, hlevel, hder, hinj,
      hV, hxV, hVO, himage, hdim, himm⟩ :=
    exists_compact_lipschitz_levelPatch (hU.inter hO) hG.contDiffOn ⟨hKU hx, hxO⟩ hp
  obtain ⟨Phi, hEL, hinit, _⟩ := hF.exists_complete_tangentFamily_C2 hcomplete old 0
  let W := (fderiv ℝ G x).ker
  have hcsub : closedBall (0 : W) a ⊆ ball 0 (2 * a) :=
    closedBall_subset_ball (by linarith)
  have hqlegal (w : W) (hw : w ∈ closedBall 0 a) :
      (σ w, fderiv ℝ G (σ w)) ∈ eL.target := hlegal _ (hmap (hcsub hw)).2
  obtain ⟨C, hC, hupper⟩ := hF.exists_uniform_separated_level_seed_distance_upper old
    hEL hinit heL hsource hInv hG hDG (isCompact_closedBall (0 : W) a)
      (convex_closedBall (0 : W) a) (hσLip.mono hcsub) hqlegal
      (fun w hw ↦ hlevel w (hcsub hw)) lo hi hgap
  have heq (w : W) (hw : w ∈ closedBall 0 a) (hwK : σ w ∈ K) :
      Phi (F.covectorNormalization old eL (1 / 2) (σ w, fderiv ℝ G (σ w))) = Γ (σ w) := by
    have hwU := (hmap (hcsub hw)).1
    obtain ⟨hstart, hELΓ, hmomentum⟩ := hΓ (σ w) hwU
    rw [hfixed (σ w) ⟨hwK, (hmap (hcsub hw)).2⟩]
    apply hF.eq_complete_family_of_chartMomentum old hEL hinit heL hsource hELΓ
      (q := (σ w, fderiv ℝ G (σ w))) _ (hqlegal w hw) hmomentum
    rw [hstart]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hUt hwU)
  refine ⟨a, C, B, σ, V, ha, hC, hσ0, hσ, hσLip,
    (fun w hw ↦ (hmap hw).1), hlevel, hder, hinj, hV, hxV,
    (fun y hy ↦ (hVO hy).1), himage, hdim, himm, ?_⟩
  intro w hw hwK z hz hzK s t hlo hhi hst
  have hh := hupper w hw z hz s t hlo hhi hst
  dsimp only at hh
  rw [heq w hw hwK, heq z hz hzK] at hh
  exact hh

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
