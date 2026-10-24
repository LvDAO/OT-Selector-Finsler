import OTSelector.Geometry.FinslerC11GoodCoreQuadratic
import OTSelector.Geometry.Finsler.CalibratedTranslation

/-!
# Original endpoint deficits in a selected good core

The actual original potential clock converts the good-core deficit into the original
length distance minus elapsed time. Only the central curve is identified with the
supplied original curve; nearby endpoint curves stay in the selected core family.
-/

open Set Filter Metric MeasureTheory Manifold Bundle Asymptotics
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The selected good core supplies actual level coordinates and a quadratic
original-distance deficit at a given pair on its identified original central curve.
The nearby endpoint family remains the selected core family A. -/
theorem exists_original_endpoint_quadratic_of_shifted_good_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) {K : Set E}
    (hKt : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ z ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G z) z)
    {A : E → ℝ → M}
    (hA : ∀ z ∈ K,
      A z 0 = (extChartAt 𝓘(ℝ, E) old).symm z ∧
      F.IsEulerLagrangeOn (A z) univ ∧
      F.chartMomentumFamily old A (z, 0) = (z, fderiv ℝ G z))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ z ∈ K, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm z) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm z) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm z) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm z) = δ)
    {x : E} (hgood : F.HasC11PotentialFamilyAt m old 0 u G K x)
    (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    {γ : ℝ → M} {t α β : ℝ}
    (hshift : A x = (fun r ↦ γ (r + t)))
    (hαβ : α < β)
    (hseg : Icc (α - t) (β - t) ⊆ Ioo (-δ) δ) :
    letI : MetricSpace M := F.metricSpace
    let p := fderiv ℝ G x
    let c := G x
    c = u (γ t) ∧
    ∃ eG : OpenPartialHomeomorph E (ℝ × p.ker),
      x ∈ eG.source ∧ eG.source ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      ContDiffOn ℝ 1 eG eG.source ∧ ContDiffOn ℝ 1 eG.symm eG.target ∧
      eG x = (c, 0) ∧ (∀ z : E, (eG z).1 = G z) ∧
      let σ : p.ker → E := fun w ↦ eG.symm (c, w)
      let B := {w : p.ker | (c, w) ∈ eG.target}
      let S := B ∩ σ ⁻¹' K
      IsOpen B ∧ (0 : p.ker) ∈ B ∧ ContDiffOn ℝ 1 σ B ∧ σ 0 = x ∧
      HasFDerivAt σ p.ker.subtypeL 0 ∧ (0 : p.ker) ∈ S ∧
      σ '' S = eG.source ∩ K ∩
        {z | u ((extChartAt 𝓘(ℝ, E) old).symm z) = u (γ t)} ∧
      ∃ (Γ : p.ker → ℝ → M) (Y : OpenPartialHomeomorph (ℝ × p.ker) M),
        A x = Γ 0 ∧ Γ 0 = (fun r ↦ γ (r + t)) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × p.ker) 𝓘(ℝ, E) ∞ Y Y.source ∧
        ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × p.ker) ∞ Y.symm Y.target ∧
        (Y : ℝ × p.ker → M) = (fun q ↦ Γ q.2 q.1) ∧
        (∀ q ∈ Y.source,
          F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2) ∧
        (∀ z ∈ Y.target, ∀ v : TangentSpace 𝓘(ℝ, E) z,
          @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (manifoldFlowTimePotential Y 1 0) z v)
            (F.toFun ⟨z, v⟩ : ℝ)) ∧
        (∀ r ∈ Icc (α - t) (β - t), (r, (0 : p.ker)) ∈ Y.source) ∧
        let τ := ContinuousLinearMap.fst ℝ ℝ p.ker
        let d : p.ker → τ.ker := fun w ↦ ⟨(0, w), by simp [τ]⟩
        let Q := F.tubeLengthKernelCompliance Y τ
          (fun r ↦ γ (r + t)) (α - t) (β - t)
        let X : ℝ → p.ker → M := fun r w ↦ A (σ w) (r - t)
        (∀ r : ℝ, X r 0 = γ r) ∧
        (∀ r ∈ Icc α β, ∀ w ∈ S, u (X r w) = c + (r - t)) ∧
        dist (γ α) (γ β) = β - α ∧
        (fun z : p.ker × p.ker ↦
          ((F.lengthEDist (X α z.1) (X β z.2)).toReal - (β - α)) -
            (1 / 2 : ℝ) * Q.inverse (d (z.2 - z.1)) (d (z.2 - z.1)))
          =o[𝓝[S ×ˢ S] (0, 0)] fun z ↦ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
  let instShiftedGoodCoreMetric : MetricSpace M := F.metricSpace
  let p := fderiv ℝ G x
  let c := G x
  have hxK : x ∈ K := hgood.1
  have hcenter0 : (extChartAt 𝓘(ℝ, E) old).symm x = γ t := by
    calc
      (extChartAt 𝓘(ℝ, E) old).symm x = A x 0 := (hA x hxK).1.symm
      _ = γ t := by simpa only [zero_add] using congrFun hshift 0
  have hc : c = u (γ t) := (hval hxK).trans (congrArg u hcenter0)

  -- Every curve of the selected original core has its actual calibrated clock.
  have hcalibrated (z : E) (hz : z ∈ K) :
      (∀ s ∈ Icc (-δ) δ, u (A z s) = G z + s) ∧
        Isometry (fun s : Icc (-δ) δ ↦ A z s) := by
    obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners z hz
    have hinside : (extChartAt 𝓘(ℝ, E) old).symm z ∈
        OTSelector.Geometry.calibratedInterior u := by
      refine ⟨⟨l, ?_, hul.trans hl.symm⟩, ⟨r, ?_, hur.trans hr.symm⟩⟩
      · exact dist_pos.mp (by rw [hl]; exact hδ)
      · exact dist_pos.mp (by rw [hr]; exact hδ)
    have hdu := hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu hinside
    have hp : F.chartMomentumFamily old A (z, 0) =
        (z, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) z) :=
      (hA z hz).2.2.trans (Prod.ext rfl (hactual z hz).fderiv.symm)
    obtain ⟨_, _, _, hclock, hiso, _⟩ :=
      hF.calibrated_translation_of_chartMomentum hcomplete old hu (hKt hz)
        (hA z hz).2.1 (hA z hz).1 hp hdu hδ ⟨hl, hul⟩ ⟨hr, hur⟩
    refine ⟨?_, hiso⟩
    intro s hs
    exact (hclock s hs).trans (congrArg (fun r : ℝ ↦ r + s) (hval hz).symm)

  -- The old API uses potential-clock endpoints; these are only translated times.
  let a := c + (α - t)
  let b := c + (β - t)
  have ha : a - G x = α - t := by dsimp [a, c]; ring
  have hb : b - G x = β - t := by dsimp [b, c]; ring
  have hab : a < b := by dsimp only [a, b]; linarith
  have hspan : Icc (a - G x) (b - G x) ⊆ Ioo (-δ) δ := by
    simpa only [ha, hb] using hseg
  obtain ⟨eG, hxeG, hsourceG, heG, heiG, heGx, hfirstG, hBG, h0G,
      hσC1, hσ0, hσD, himage, Γ, Y, hΓ0, hY, hYi, hYeq, hhalf,
      hbound, hstay, hquad⟩ :=
    hF.exists_original_length_quadratic_of_good_core hcomplete old m hKt hu hG
      hval hactual hA hδ hpartners hgood hcmp hab hspan
  let σ : p.ker → E := fun w ↦ eG.symm (c, w)
  let B : Set p.ker := {w | (c, w) ∈ eG.target}
  let S := B ∩ σ ⁻¹' K
  let X : ℝ → p.ker → M := fun r w ↦ A (σ w) (r - t)
  let τ := ContinuousLinearMap.fst ℝ ℝ p.ker
  let d : p.ker → τ.ker := fun w ↦ ⟨(0, w), by simp [τ]⟩
  let Q := F.tubeLengthKernelCompliance Y τ
    (fun r ↦ γ (r + t)) (α - t) (β - t)
  change σ 0 = x at hσ0
  have h0S : (0 : p.ker) ∈ S := by
    refine ⟨h0G, ?_⟩
    change σ 0 ∈ K
    rwa [hσ0]
  have hlevel (w : p.ker) (hw : w ∈ S) : G (σ w) = c := by
    simpa only [hfirstG] using congrArg Prod.fst (eG.right_inv hw.1)
  have hXcenter (r : ℝ) : X r 0 = γ r := by
    change A (σ 0) (r - t) = γ r
    rw [hσ0]
    simpa only [sub_add_cancel] using congrFun hshift (r - t)
  have hclock (r : ℝ) (hr : r ∈ Icc α β) (w : p.ker) (hw : w ∈ S) :
      u (X r w) = c + (r - t) := by
    have hrs : r - t ∈ Icc (-δ) δ :=
      Ioo_subset_Icc_self (hseg
        ⟨sub_le_sub_right hr.1 t, sub_le_sub_right hr.2 t⟩)
    exact ((hcalibrated (σ w) hw.2).1 (r - t) hrs).trans
      (congrArg (fun v : ℝ ↦ v + (r - t)) (hlevel w hw))
  have hαwin : α - t ∈ Icc (-δ) δ :=
    Ioo_subset_Icc_self (hseg (left_mem_Icc.mpr (sub_le_sub_right hαβ.le t)))
  have hβwin : β - t ∈ Icc (-δ) δ :=
    Ioo_subset_Icc_self (hseg (right_mem_Icc.mpr (sub_le_sub_right hαβ.le t)))
  have hdist : dist (γ α) (γ β) = β - α := by
    have hd := (hcalibrated x hxK).2.dist_eq ⟨α - t, hαwin⟩ ⟨β - t, hβwin⟩
    change dist (A x (α - t)) (A x (β - t)) = dist (α - t) (β - t) at hd
    calc
      dist (γ α) (γ β) = dist (α - t) (β - t) := by
        simpa only [hshift, sub_add_cancel] using hd
      _ = β - α := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith)]
        ring
  have hquad' :
      (fun z : p.ker × p.ker ↦
        ((F.lengthEDist (X α z.1) (X β z.2)).toReal -
          u (X β z.2) + u (X α z.1)) -
          (1 / 2 : ℝ) * Q.inverse (d (z.2 - z.1)) (d (z.2 - z.1)))
        =o[𝓝[S ×ˢ S] (0, 0)] fun z ↦ ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 := by
    simpa only [ha, hb, hshift, σ, B, S, τ, d, Q, X, p, c] using hquad

  refine ⟨hc, eG, hxeG, hsourceG, heG, heiG, heGx, hfirstG,
    hBG, h0G, hσC1, hσ0, hσD, h0S, ?_, Γ, Y, hΓ0, hΓ0.symm.trans hshift,
    hY, hYi, hYeq, hhalf, hbound, ?_, hXcenter, hclock, hdist, ?_⟩
  · simpa only [hcenter0] using himage
  · simpa only [ha, hb] using hstay
  · apply hquad'.congr' _ (Filter.Eventually.of_forall fun _ ↦ rfl)
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hα := hclock α ⟨le_rfl, hαβ.le⟩ z.1 hz.1
    have hβ := hclock β ⟨hαβ.le, le_rfl⟩ z.2 hz.2
    rw [hα, hβ]
    ring

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
