import OTSelector.Geometry.FinslerFiniteUpperLevelPatches
import OTSelector.Geometry.Finsler.RationalLevelSeeds
import OTSelector.Analysis.Normed.FiniteBallCubeEmbeddings

/-!
# Finite actual upper seeds in a common cube dimension

The explicit label equivalence retained by the original seed constructor ties
the finite covering, cube coordinates and distance bound to the same sections.
-/

open Set Metric Manifold Bundle Module
open scoped Topology ContDiff NNReal BigOperators
noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The same finite original level seeds have injective continuous cube labels
and one quadratic upper bound on all actual separated-time endpoints. -/
theorem exists_finite_original_upperSeedCubes
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : let _instUpperCubesLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hDG : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ y ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : let _instUpperCubesReach : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {Γ : E → ℝ → M}
    (hΓ : ∀ y ∈ U, Γ y 0 = (extChartAt 𝓘(ℝ, E) old).symm y ∧
      F.IsEulerLagrangeOn (Γ y) univ ∧
      F.chartMomentumFamily old Γ (y, 0) = (y, fderiv ℝ G y))
    (lo hi : ℝ) (q : ℚ) {gap : ℝ} (hgap : 0 < gap) :
    ∃ ι : Type u, Finite ι ∧ ∃ P : ι → CalibratedLevelSeedPatch F u,
      ∃ (Q : ∀ i, (P i).covector.ker → Fin (Module.finrank ℝ E - 1) → Icc (0 : ℝ) 1)
        (C : ℝ), 0 < C ∧
        (∀ i, (P i).level = q ∧ Continuous (Q i) ∧ InjOn (Q i) (P i).labels) ∧
        (⋃ i, (fun w ↦ (P i).curve w 0) '' (P i).labels) =
          (extChartAt 𝓘(ℝ, E) old).symm '' (K ∩ {x | G x = (q : ℝ)}) ∧
        ∀ i, ∀ w ∈ (P i).labels, ∀ z ∈ (P i).labels,
          ∀ s t : ℝ, lo ≤ s → t ≤ hi → gap ≤ t - s →
          (F.lengthEDist ((P i).curve w s) ((P i).curve z t)).toReal - (t - s) ≤
            C * ‖(fun j ↦ (Q i z j : ℝ)) - (fun j ↦ (Q i w j : ℝ))‖ ^ 2 := by
  classical
  obtain ⟨J, a, B, σ, C, hC, hdata, hcover, _, _⟩ :=
    hF.exists_finite_original_compact_level_upperPatches hcomplete old hK hU hKU hUt hu
      hG hDG hmatch hδ hpartners hΓ lo hi (q : ℝ) hgap
  let H := K ∩ {x | G x = (q : ℝ)}
  let T := {x : H // x ∈ J}
  have hpatch (i : T) : ∃ P : CalibratedLevelSeedPatch F u,
      ∃ e : P.covector.ker ≃L[ℝ] (fderiv ℝ G (i.val : E)).ker,
        P.openLabels = e ⁻¹' ball 0 (a i.val) ∧
        P.labels = e ⁻¹' (ball 0 (a i.val) ∩ (σ i.val) ⁻¹' K) ∧
        (∀ w t, P.curve w t = Γ (σ i.val (e w)) t) ∧ P.level = q ∧
        (fun w ↦ P.curve w 0) '' P.labels = (extChartAt 𝓘(ℝ, E) old).symm ''
          (σ i.val '' (ball 0 (a i.val) ∩ (σ i.val) ⁻¹' K)) := by
    obtain ⟨ha, hσ0, hσ, _, hσU, hlevel, hder, hinj, hdim, himm, _⟩ :=
      hdata i.val i.property
    have hsub : ball (0 : (fderiv ℝ G (i.val : E)).ker) (a i.val) ⊆
        ball 0 (2 * a i.val) := ball_subset_ball (by linarith)
    exact hF.exists_levelSeedPatch_of_coreSection_with_coordinates hcomplete old hu
      hK hU hKU hUt hG hDG hmatch hval hactual
      (fun y hy ↦ (hΓ y hy).2.1) (fun y hy ↦ (hΓ y hy).1)
      (fun y hy ↦ (hΓ y hy).2.2) hδ hpartners isOpen_ball
      (hσ.mono hsub) (hσU.mono_left hsub) (hinj.mono hsub) hdim (mem_ball_self ha)
      (by rw [hσ0]; exact i.val.property.1) (by rw [hσ0]) hder
      (fun w hw ↦ himm w (hsub hw)) q (fun w hw ↦ hlevel w (hsub hw))
  choose P e hOpen hLabels hCurve hLevel hImage using hpatch
  let W (i : T) := (fderiv ℝ G (i.val : E)).ker
  have hdim (i : T) : Module.finrank ℝ (W i) = Module.finrank ℝ E - 1 := by
    obtain ⟨_, _, _, _, _, _, _, _, hd, _, _⟩ := hdata i.val i.property
    dsimp only [W]
    omega
  let basis (i : T) : Basis (Fin (Module.finrank ℝ E - 1)) ℝ (W i) :=
    (Module.finBasis ℝ (W i)).reindex (finCongr (hdim i))
  obtain ⟨Q, L₀, hL₀, hQ⟩ := OTSelector.Reconstruction.exists_finite_labelUnitCubeMaps basis
    (r := fun i ↦ a i.val) (fun i ↦ (hdata i.val i.property).1)
  have hmem (i : T) (w : (P i).covector.ker) (hw : w ∈ (P i).labels) :
      e i w ∈ closedBall 0 (a i.val) ∧ σ i.val (e i w) ∈ K := by
    rw [hLabels i] at hw
    exact ⟨ball_subset_closedBall hw.1, hw.2⟩
  refine ⟨T, inferInstance, P, (fun i w ↦ Q i (e i w)), C * L₀ ^ 2,
    mul_pos hC (sq_pos_of_pos hL₀), ?_, ?_, ?_⟩
  · intro i
    refine ⟨hLevel i, (hQ i).1.comp (e i).continuous, ?_⟩
    intro w hw z hz heq
    exact (e i).injective ((hQ i).2.1 (hmem i w hw).1 (hmem i z hz).1 heq)
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      rw [hImage i] at hi
      obtain ⟨x, ⟨w, hw, rfl⟩, hxy⟩ := hi
      refine ⟨σ i.val w, ?_, hxy⟩
      exact (Set.ext_iff.mp hcover _).mpr
        (mem_iUnion₂.mpr ⟨i.val, i.property, w, hw, rfl⟩)
    · rintro y ⟨x, hx, hxy⟩
      rw [hcover] at hx
      obtain ⟨i, hi, w, hw, hwx⟩ := mem_iUnion₂.mp hx
      refine mem_iUnion.mpr ⟨⟨i, hi⟩, ?_⟩
      rw [hImage]
      exact ⟨x, ⟨w, hw, hwx⟩, hxy⟩
  · intro i w hw z hz s t hlo hhi hst
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hupper⟩ := hdata i.val i.property
    simp only [hCurve]
    apply OTSelector.Reconstruction.quadratic_upper_of_labelCube_bound hC.le
      ((hQ i).2.2 (e i z) (hmem i z hz).1 (e i w) (hmem i w hw).1)
    exact hupper (e i w) (hmem i w hw).1 (hmem i w hw).2
      (e i z) (hmem i z hz).1 (hmem i z hz).2 s t hlo hhi hst

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
