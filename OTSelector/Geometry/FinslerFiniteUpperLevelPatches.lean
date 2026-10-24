import OTSelector.Geometry.FinslerDistanceLocalizationOriginalPatch

/-!
# Finite original level patches with one whole-time quadratic upper bound

The same finite sections both cover the original compact level and carry the
uniform distance bound from their actual complete geodesic families.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M}

/-- Every original compact level has a finite exact section cover, with compact
inner label balls and one uniform quadratic cost bound for all actual endpoints
in a prescribed finite time range with positive time separation. -/
theorem exists_finite_original_compact_level_upperPatches
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instFiniteUpperLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hDG : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instFiniteUpperReach : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {Γ : E → ℝ → M}
    (hΓ : ∀ y ∈ U, Γ y 0 = (extChartAt 𝓘(ℝ, E) old).symm y ∧
      F.IsEulerLagrangeOn (Γ y) univ ∧
      F.chartMomentumFamily old Γ (y, 0) = (y, fderiv ℝ G y))
    (lo hi c : ℝ) {gap : ℝ} (hgap : 0 < gap) :
    let H := K ∩ {x | G x = c}
    ∃ (J : Finset H) (a : H → ℝ) (B : H → ℝ≥0)
        (σ : ∀ x : H, (fderiv ℝ G (x : E)).ker → E) (C : ℝ),
      0 < C ∧
      (∀ x ∈ J, 0 < a x ∧ σ x 0 = (x : E) ∧
        ContDiffOn ℝ 1 (σ x) (ball 0 (2 * a x)) ∧
        LipschitzOnWith (B x) (σ x) (ball 0 (2 * a x)) ∧
        MapsTo (σ x) (ball 0 (2 * a x)) U ∧
        (∀ w ∈ ball 0 (2 * a x), G (σ x w) = c) ∧
        HasFDerivAt (σ x) (fderiv ℝ G (x : E)).ker.subtypeL 0 ∧
        InjOn (σ x) (ball 0 (2 * a x)) ∧
        Module.finrank ℝ (fderiv ℝ G (x : E)).ker + 1 = Module.finrank ℝ E ∧
        (∀ w ∈ ball 0 (2 * a x), Function.Injective (fderiv ℝ (σ x) w)) ∧
        ∀ w ∈ closedBall 0 (a x), σ x w ∈ K →
          ∀ z ∈ closedBall 0 (a x), σ x z ∈ K →
            ∀ s t : ℝ, lo ≤ s → t ≤ hi → gap ≤ t - s →
            (F.lengthEDist (Γ (σ x w) s) (Γ (σ x z) t)).toReal - (t - s) ≤
              C * ‖z - w‖ ^ 2) ∧
      H = ⋃ x ∈ J, σ x '' (ball 0 (a x) ∩ (σ x) ⁻¹' K) ∧
      H = ⋃ x ∈ J, σ x '' (closedBall 0 (a x) ∩ (σ x) ⁻¹' K) ∧
      ∀ x ∈ J, IsCompact (σ x '' (closedBall 0 (a x) ∩ (σ x) ⁻¹' K)) := by
  classical
  let H := K ∩ {x | G x = c}
  have hH : IsCompact H := hK.inter_right (isClosed_eq hG.continuous continuous_const)
  have hlocal (x : H) := hF.exists_original_compact_level_upperPatch hcomplete old
    hU hKU hUt hu hG hDG hmatch hδ hpartners hΓ lo hi hgap x.property.1
  choose a C B σ V ha hC hσ0 hσ hLip hmap hlevel hder hinj hV hxV hVU himage hdim himm
    hupper using hlocal
  obtain ⟨J, hJ⟩ := hH.elim_finite_subcover V hV (by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  let C₀ := (∑ x ∈ J, C x) + 1
  have hC₀ : 0 < C₀ := by
    have hsum : 0 ≤ ∑ x ∈ J, C x := Finset.sum_nonneg (fun x _ ↦ (hC x).le)
    dsimp only [C₀]
    linarith
  have hCle (x : H) (hx : x ∈ J) : C x ≤ C₀ := by
    have hsum := Finset.single_le_sum (f := C) (fun y _ ↦ (hC y).le) hx
    dsimp only [C₀]
    linarith
  refine ⟨J, a, B, σ, C₀, hC₀, ?_, ?_, ?_, ?_⟩
  · intro x hx
    refine ⟨ha x, hσ0 x, hσ x, hLip x, hmap x,
      fun w hw ↦ (hlevel x w hw).trans x.property.2, hder x, hinj x, hdim x, himm x, ?_⟩
    intro w hw hwK z hz hzK s t hlo hhi hst
    exact (hupper x w hw hwK z hz hzK s t hlo hhi hst).trans
      (mul_le_mul_of_nonneg_right (hCle x hx) (sq_nonneg _))
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp (hJ hy)
      have hylevel : G y = G (x : E) := hy.2.trans x.property.2.symm
      obtain ⟨w, hw, hwy⟩ := (himage x).symm ▸
        (show y ∈ V x ∩ {y | G y = G x} from ⟨hyV, hylevel⟩)
      exact mem_iUnion₂.mpr ⟨x, hx, w, ⟨hw, show σ x w ∈ K from hwy.symm ▸ hy.1⟩, hwy⟩
    · intro y hy
      obtain ⟨x, hx, w, ⟨hw, hwK⟩, rfl⟩ := mem_iUnion₂.mp hy
      exact ⟨hwK, (hlevel x w (ball_subset_ball (by linarith [ha x]) hw)).trans
        x.property.2⟩
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp (hJ hy)
      have hylevel : G y = G (x : E) := hy.2.trans x.property.2.symm
      obtain ⟨w, hw, hwy⟩ := (himage x).symm ▸
        (show y ∈ V x ∩ {y | G y = G x} from ⟨hyV, hylevel⟩)
      exact mem_iUnion₂.mpr ⟨x, hx, w,
        ⟨ball_subset_closedBall hw, show σ x w ∈ K from hwy.symm ▸ hy.1⟩, hwy⟩
    · intro y hy
      obtain ⟨x, hx, w, ⟨hw, hwK⟩, rfl⟩ := mem_iUnion₂.mp hy
      exact ⟨hwK, (hlevel x w (closedBall_subset_ball (by linarith [ha x]) hw)).trans
        x.property.2⟩
  · intro x hx
    have hc : ContinuousOn (σ x) (closedBall 0 (a x)) :=
      (hσ x).continuousOn.mono (closedBall_subset_ball (by linarith [ha x]))
    have hcK := hc.preimage_isClosed_of_isClosed isClosed_closedBall hK.isClosed
    have hcompact := (isCompact_closedBall 0 (a x)).of_isClosed_subset hcK inter_subset_left
    exact hcompact.image_of_continuousOn (hc.mono inter_subset_left)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
