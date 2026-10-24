import OTSelector.Geometry.FinslerC11OriginalDeficitTransfer
import OTSelector.Geometry.FinslerSelectedTubeQuadratic

/-!
# Quadratic expansion of the original calibrated distance deficit

The original core and complete family have the actual inverse-compliance coefficient
of their selected smooth family. The existing second-order comparison transfers the
smooth distance expansion, retaining the original potential and allowed labels.
-/

open Set Filter Metric Manifold Bundle Asymptotics
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

private theorem isLittleO_sqsum_of_eventually_norm_le_cube
    {W : Type*} [NormedAddCommGroup W]
    {T : Set (W × W)} {f : W × W → ℝ} {C : ℝ}
    (hf : ∀ᶠ q in 𝓝[T] (0 : W × W), ‖f q‖ ≤ C * ‖q‖ ^ 3) :
    f =o[𝓝[T] (0 : W × W)] fun q ↦ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
  have hbig : f =O[𝓝[T] (0 : W × W)] fun q ↦ ‖q‖ ^ 3 := by
    apply IsBigO.of_bound C
    filter_upwards [hf] with q hq
    simpa only [Real.norm_of_nonneg (pow_nonneg (norm_nonneg q) 3)] using hq
  have hpow : (fun q : W × W ↦ ‖q‖ ^ 3)
      =o[𝓝[T] (0 : W × W)] fun q ↦ ‖q‖ ^ 2 :=
    (isLittleO_norm_pow_norm_pow (E' := W × W) (m := 2) (n := 3)
      (by decide)).mono nhdsWithin_le_nhds
  apply (hbig.trans_isLittleO hpow).trans_le
  intro q
  rw [Real.norm_of_nonneg (sq_nonneg _),
    Real.norm_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)), Prod.norm_def]
  rcases le_total ‖q.1‖ ‖q.2‖ with h | h
  · rw [max_eq_right h]
    exact le_add_of_nonneg_left (sq_nonneg _)
  · rw [max_eq_left h]
    exact le_add_of_nonneg_right (sq_nonneg _)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {G P : E → ℝ} {x : E}


/-- The original allowed-label distance deficit has the actual quadratic coefficient
of a genuine tube for the same selected smooth family, with a second-order little-o
remainder. The tube and its geometric properties are conclusions. -/
theorem exists_original_deficit_quadratic_expansion
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ}
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {K : Set E} (hxK : x ∈ K)
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    (hG : ContDiff ℝ 1 G)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ y ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {A : E → ℝ → M}
    (hA : ∀ y ∈ K,
      A y 0 = (extChartAt 𝓘(ℝ, E) old).symm y ∧
      F.IsEulerLagrangeOn (A y) univ ∧
      F.chartMomentumFamily old A (y, 0) = (y, fderiv ℝ G y))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ y ∈ K, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    (hsecond : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x)
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    {e : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (he : (e : (E × E) → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsub : e.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ e.symm e.target)
    (hp : (x, fderiv ℝ G x) ∈ e.target)
    (hP : ContDiff ℝ ∞ P) (hPx : P x = G x)
    (hDP : fderiv ℝ P x = fderiv ℝ G x)
    (hPsecond : HasFDerivAt (fderiv ℝ P) (fderiv ℝ (fderiv ℝ G) x) x)
    (hdim : Module.finrank ℝ ((fderiv ℝ G x).ker) + 1 = Module.finrank ℝ E)
    {BG B : Set ((fderiv ℝ G x).ker)} {σG σP v : ((fderiv ℝ G x).ker) → E}
    {scale : ((fderiv ℝ G x).ker) → ℝ} {Γ : ((fderiv ℝ G x).ker) → ℝ → M}
    (hBG : IsOpen BG) (h0G : (0 : ((fderiv ℝ G x).ker)) ∈ BG)
    (hσG0 : σG 0 = x) (hσG : HasFDerivAt σG ((fderiv ℝ G x).ker.subtypeL) 0)
    (hGlevel : ∀ w ∈ BG, G (σG w) = G x)
    (hB : IsOpen B) (h0 : (0 : ((fderiv ℝ G x).ker)) ∈ B)
    (hσP : ContDiffOn ℝ ∞ σP B) (hσP0 : σP 0 = x)
    (hPlevel : ∀ w ∈ B, P (σP w) = P x)
    (hσPD : HasFDerivAt σP ((fderiv ℝ G x).ker.subtypeL) 0)
    (hv : ContDiffOn ℝ ∞ v B)
    (hv0 : v 0 = (e.symm (x, fderiv ℝ G x)).2)
    (hscale0 : scale 0 = 1)
    (hstate : ∀ w ∈ B, (σP w, v w) ∈ chartEnergyDomain old)
    (hΓEL : ∀ w ∈ B, F.IsEulerLagrangeOn (Γ w) univ)
    (hΓinit : ∀ w ∈ B,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm (σP w, v w))
    (hm : ∀ w ∈ B, F.chartMomentumFamily old Γ (w, 0) =
      potentialConormalState P σP scale w)
    (henergy : ∀ w ∈ B, ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1 / 2)
    (hjet : HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
      (((fderiv ℝ G x).ker.subtypeL).prod
        ((fderiv ℝ (fderiv ℝ G) x).comp ((fderiv ℝ G x).ker.subtypeL))) 0)
    {a b : ℝ} (hab : a < b)
    (hseg : Icc (a - G x) (b - G x) ⊆ Ioo (-δ) δ) :
    let c := G x
    let S := BG ∩ σG ⁻¹' K
    let X : ℝ → ((fderiv ℝ G x).ker) → M := fun r w ↦ A (σG w) (r - c)
    ∃ Y : OpenPartialHomeomorph (ℝ × (fderiv ℝ G x).ker) M,
      ContMDiffOn 𝓘(ℝ, ℝ × (fderiv ℝ G x).ker) 𝓘(ℝ, E) ∞ Y Y.source ∧
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × (fderiv ℝ G x).ker) ∞ Y.symm Y.target ∧
      (Y : ℝ × (fderiv ℝ G x).ker → M) = (fun q ↦ Γ q.2 q.1) ∧
      (∀ q ∈ Y.source,
        F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2) ∧
      (∀ y ∈ Y.target, ∀ z : TangentSpace 𝓘(ℝ, E) y,
        @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 0) y z)
          (F.toFun ⟨y, z⟩ : ℝ)) ∧
      (∀ t ∈ Icc (a - c) (b - c), (t, (0 : (fderiv ℝ G x).ker)) ∈ Y.source) ∧
      let Q := F.tubeEndpointCompliance Y (Γ 0) (a - c) (b - c)
      (fun q : ((fderiv ℝ G x).ker) × ((fderiv ℝ G x).ker) ↦
        ((F.lengthEDist (X a q.1) (X b q.2)).toReal -
          u (X b q.2) + u (X a q.1)) -
        (1 / 2 : ℝ) * Q.inverse (0, q.2 - q.1) (0, q.2 - q.1))
        =o[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2
 := by
  let : MetricSpace M := F.metricSpace
  let c := G x
  let S := BG ∩ σG ⁻¹' K
  let ta := a - c
  let tb := b - c
  have htab : ta < tb := sub_lt_sub_right hab c
  have hta : ta ∈ Ioo (-δ) δ := hseg (left_mem_Icc.mpr htab.le)
  have htb : tb ∈ Ioo (-δ) δ := hseg (right_mem_Icc.mpr htab.le)
  have hdu (y : E) (hy : y ∈ K) : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u
      ((extChartAt 𝓘(ℝ, E) old).symm y) := by
    have hs : (extChartAt 𝓘(ℝ, E) old).symm y ∈ (chartAt E old).source := by
      simpa only [extChartAt_source] using
        (extChartAt 𝓘(ℝ, E) old).map_target (hKt hy)
    apply (mdifferentiableAt_iff_source_of_mem_source
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, ℝ)) hs).2
    simpa only [(extChartAt 𝓘(ℝ, E) old).right_inv (hKt hy),
      modelWithCornersSelf_coe, range_id, mdifferentiableWithinAt_univ] using
      (hactual y hy).differentiableAt.mdifferentiableAt
  obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners x hxK
  have hmomentum : F.chartMomentumFamily old A (x, 0) =
      (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x) :=
    (hA x hxK).2.2.trans (Prod.ext rfl (hactual x hxK).fderiv.symm)
  obtain ⟨hunitA, _, _, hclockA, hisoA, _⟩ :=
    hF.calibrated_translation_of_chartMomentum hcomplete old hu (hKt hxK)
      (hA x hxK).2.1 (hA x hxK).1 hmomentum (hdu x hxK) hδ ⟨hl, hul⟩ ⟨hr, hur⟩
  obtain ⟨hcenter, _, T, V, Y, _, _, hJT, hV0, hTV, hYeq, hYs, _, hY, hi,
      _, hbound, _⟩ :=
    hF.exists_smooth_calibratedTube_of_levelPositionComparison old hcmp hdim hB h0
      (fun w _ ↦ hP.differentiable (by simp) (σP w)) hσP hσP0 hPlevel hv hscale0
      hDP hstate hΓEL hΓinit hm henergy hjet hisoA isCompact_Icc hseg
  have hstay (t : ℝ) (ht : t ∈ Icc ta tb) : (t, (0 : ((fderiv ℝ G x).ker))) ∈ Y.source := by
    rw [hYs]
    exact ⟨hJT ht, hV0⟩
  have hhalfY (q : ℝ × ((fderiv ℝ G x).ker)) (hq : q ∈ Y.source) :
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2 := by
    rw [hYs] at hq
    exact henergy q.2 (hTV hq).2 q.1
  have hunitΓ : ∀ t : ℝ,
      F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ 0) ⟨t, (1 : ℝ)⟩) = 1 := by
    simpa only [hcenter] using hunitA
  have hclockΓ : ∀ t ∈ Icc (-δ) δ,
      u (Γ 0 t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t := by
    simpa only [hcenter] using hclockA
  have hca := hclockΓ ta ⟨hta.1.le, hta.2.le⟩
  have hcb := hclockΓ tb ⟨htb.1.le, htb.2.le⟩
  have hinner := hF.calibrated_window_of_complete_unit_endpoints hu
    (hΓEL 0 h0) hunitΓ hca hcb
  have houter := hF.calibrated_window_of_complete_unit_endpoints hu
    (hΓEL 0 h0) hunitΓ
    (hclockΓ (-δ) ⟨le_rfl, by linarith⟩) (hclockΓ δ ⟨by linarith, le_rfl⟩)
  have hdist : dist (Γ 0 ta) (Γ 0 tb) = tb - ta := by
    simpa only [Subtype.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr htab.le), neg_sub] using
      hinner.2.1.dist_eq ⟨ta, left_mem_Icc.mpr htab.le⟩ ⟨tb, right_mem_Icc.mpr htab.le⟩
  have hsat : u (Γ 0 tb) - u (Γ 0 ta) = dist (Γ 0 ta) (Γ 0 tb) := by
    rw [hca, hcb, hdist]
    ring
  have hmin := hF.lengthEDist_eq_pathELength_of_isometric_interval htab.le hinner.2.1
  have hduStart := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
    (houter.2.2 ta hta)
  obtain ⟨r, hr, C, _, hrem⟩ := hF.exists_selected_tube_distance_quadratic_remainder
    hcomplete hY hi hYeq hhalfY 0 hbound htab (hΓEL 0 h0) hstay hmin hu hsat hduStart
  refine ⟨Y, hY, hi, hYeq, hhalfY, hbound, hstay, ?_⟩
  let Q := F.tubeEndpointCompliance Y (Γ 0) ta tb
  have htime : tb - ta = b - a := by dsimp [ta, tb]; ring
  have hsmall : ∀ᶠ q : ((fderiv ℝ G x).ker) × ((fderiv ℝ G x).ker)
      in 𝓝[S ×ˢ S] (0, 0), ‖q‖ ≤ r := by
    filter_upwards [nhdsWithin_le_nhds (Metric.closedBall_mem_nhds (0 :
      ((fderiv ℝ G x).ker) × ((fderiv ℝ G x).ker)) hr)] with q hq
    simpa only [Metric.mem_closedBall, dist_zero_right] using hq
  have hquad : (fun q : ((fderiv ℝ G x).ker) × ((fderiv ℝ G x).ker) ↦
      ((F.lengthEDist (Γ q.1 ta) (Γ q.2 tb)).toReal - (b - a)) -
        (1 / 2 : ℝ) * Q.inverse (0, q.2 - q.1) (0, q.2 - q.1))
      =o[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
    apply isLittleO_sqsum_of_eventually_norm_le_cube (C := C)
    filter_upwards [hsmall] with q hq
    simpa only [zero_add, htime] using hrem q.1 q.2 hq
  have htransfer := hF.original_deficit_sub_selected_smooth_isLittleO hcomplete old hu
    hxK hKt hG hval hactual hA hδ hpartners hsecond hcmp he hsub hInv hp hP hPx hDP
    hPsecond hdim hBG h0G hσG0 hσG hGlevel hB h0 hσP hσP0 hPlevel hσPD hv hv0
    hscale0 hstate hΓEL hΓinit hm henergy hjet hab hseg
  exact (htransfer.add hquad).congr_left fun q ↦ by dsimp [Q, ta, tb, c]; ring

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
