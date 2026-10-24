import OTSelector.Geometry.Finsler.Calibration.CountablePrescribedReachCover
import OTSelector.Geometry.Finsler.C11ReachAbsoluteContinuity
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CalibratedBackwardIdentity
import OTSelector.Transport.Kantorovich.CalibratedEndpointWindow

/-!
# Original good centers with a sufficient prescribed reach

One preselected rational-reach cover applies to all actual translated section laws
and their occupation law. Countably many fixed rational times give a common full
source set. Every strict interior endpoint pair then has a good center in its own
interval, a reach covering both endpoints, and the same original central curve.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
universe uE uM
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- One original prescribed-reach cover works for all supplied calibrated seed
families and finite physical laws. Every fixed legal time has original-law-a.e.
good witnesses at every applicable positive rational reach. On one full source
set, every strict interior endpoint pair admits a good center with a sufficient
rational reach and the same actual central curve, identified at all times. -/
theorem exists_countable_original_occupation_prescribed_reach_good_cover
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [IsAddHaarMeasure m]
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    letI : MetricSpace M := F.metricSpace
    ∃ ι : Type (max uE uM), Countable ι ∧
      ∃ (old : ι → M) (K U : ι → Set E) (G : ι → E → ℝ) (L : ι → ℝ≥0)
          (A : ι → E → ℝ → M),
        (∀ i, IsCompact (K i) ∧ K i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ContDiff ℝ 1 (G i) ∧ HasCompactSupport (G i) ∧
          LipschitzWith (L i) (fderiv ℝ (G i)) ∧
          EqOn (G i) (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm) (K i) ∧
          EqOn (fderiv ℝ (G i))
            (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)) (K i) ∧
          ∀ x ∈ K i, HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
            (fderiv ℝ (G i) x) x) ∧
        (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' K i) =
          OTSelector.Geometry.calibratedInterior u ∧
        (∀ i, IsOpen (U i) ∧ K i ⊆ U i ∧
          U i ⊆ (extChartAt 𝓘(ℝ, E) (old i)).target ∧
          ∀ x ∈ U i,
            A i x 0 = (extChartAt 𝓘(ℝ, E) (old i)).symm x ∧
            F.IsEulerLagrangeOn (A i x) univ ∧
            ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (A i x) ∧
            F.chartMomentumFamily (old i) (A i) (x, 0) = (x, fderiv ℝ (G i) x)) ∧
        let S : ℚ → Set M := fun q ↦
          OTSelector.Geometry.calibratedReachLevel u (q : ℝ) ∩
            OTSelector.Geometry.calibratedReachLevel (-u) (q : ℝ)
        let C : ι → ℚ → Set E := fun i q ↦
          K i ∩ (extChartAt 𝓘(ℝ, E) (old i)).symm ⁻¹' S q
        (∀ q : ℚ, 0 < q →
          (∀ i, IsCompact (C i q) ∧ ∀ x ∈ C i q, ∃ l r : M,
            dist l ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ) ∧
            u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - u l = (q : ℝ) ∧
            dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) r = (q : ℝ) ∧
            u r - u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ)) ∧
          (⋃ i, (extChartAt 𝓘(ℝ, E) (old i)).symm '' C i q) = S q) ∧
        let Good : ℚ → M → Prop := fun q y ↦ ∃ (i : ι) (x : E), x ∈ C i q ∧
          (extChartAt 𝓘(ℝ, E) (old i)).symm x = y ∧
          F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (C i q) x ∧
          F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (q : ℝ) x
        let GoodAll : M → Prop := fun y ↦ ∀ q : ℚ, 0 < q → y ∈ S q → Good q y
        ∀ (initial : M) (K₀ U₀ : Set E)
          (_hK₀ : IsCompact K₀) (_hU₀ : IsOpen U₀) (_hK₀U₀ : K₀ ⊆ U₀)
          (_hU₀target : U₀ ⊆ (extChartAt 𝓘(ℝ, E) initial).target)
          (G₀ : E → ℝ) (L₀ : ℝ≥0) (_hG₀ : ContDiff ℝ 1 G₀)
          (_hLip₀ : LipschitzWith L₀ (fderiv ℝ G₀))
          (_hmatch₀ : EqOn (fderiv ℝ G₀)
            (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) initial).symm)) K₀)
          (A₀ : E → ℝ → M)
          (_hEL₀ : ∀ x ∈ U₀, F.IsEulerLagrangeOn (A₀ x) univ)
          (_hinit₀ : ∀ x ∈ U₀, A₀ x 0 = (extChartAt 𝓘(ℝ, E) initial).symm x)
          (_hp₀ : ∀ x ∈ U₀,
            F.chartMomentumFamily initial A₀ (x, 0) = (x, fderiv ℝ G₀ x))
          (δ₀ : ℝ) (_hδ₀ : 0 < δ₀)
          (_hpartners₀ : ∀ x ∈ K₀, ∃ l r : M,
            dist l ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ₀ ∧
            u ((extChartAt 𝓘(ℝ, E) initial).symm x) - u l = δ₀ ∧
            dist ((extChartAt 𝓘(ℝ, E) initial).symm x) r = δ₀ ∧
            u r - u ((extChartAt 𝓘(ℝ, E) initial).symm x) = δ₀)
          (η : Measure M) (_hηfinite : IsFiniteMeasure η)
          (_hη : (η.restrict (extChartAt 𝓘(ℝ, E) initial).source).map
            (extChartAt 𝓘(ℝ, E) initial) ≪ m),
          let C₀ := (extChartAt 𝓘(ℝ, E) initial).symm '' K₀
          let I := Ioo (-δ₀) δ₀
          let T : ℝ × M → M := fun q ↦ A₀ (extChartAt 𝓘(ℝ, E) initial q.2) q.1
          let ρ := η.restrict C₀
          (∀ t ∈ I,
            AEMeasurable (fun y ↦ T (t, y)) ρ ∧
            (∀ᵐ y ∂ρ, GoodAll (T (t, y))) ∧
            (∀ᵐ z ∂ρ.map (fun y ↦ T (t, y)), GoodAll z) ∧
            IsFiniteMeasure (ρ.map (fun y ↦ T (t, y))) ∧
            (ρ.map (fun y ↦ T (t, y))) univ = η C₀ ∧
            (∀ᵐ z ∂ρ.map (fun y ↦ T (t, y)),
              z ∈ OTSelector.Geometry.calibratedInterior u) ∧
            ∀ terminal : M,
              (((ρ.map (fun y ↦ T (t, y))).restrict
                (extChartAt 𝓘(ℝ, E) terminal).source).map
                (extChartAt 𝓘(ℝ, E) terminal) ≪ m)) ∧
          (∀ᵐ y ∂ρ,
            (∀ᵐ t ∂(volume : Measure ℝ).restrict I, GoodAll (T (t, y))) ∧
            ∀ α β : ℝ, -δ₀ < α → α < β → β < δ₀ →
              ∃ t ∈ Ioo α β, ∃ q : ℚ, 0 < q ∧
                Icc (α - t) (β - t) ⊆ Ioo (-(q : ℝ)) (q : ℝ) ∧
                ∃ (i : ι) (x : E), x ∈ C i q ∧
                  (extChartAt 𝓘(ℝ, E) (old i)).symm x = T (t, y) ∧
                  F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (C i q) x ∧
                  F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (q : ℝ) x ∧
                  A i x = (fun r ↦
                    A₀ (extChartAt 𝓘(ℝ, E) initial y) (r + t))) := by
  classical
  let : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, A, hdata, hcover, hUA, hreach, hgood⟩ :=
    hF.exists_countable_original_prescribed_reach_good_cover hcomplete m hu
  let S : ℚ → Set M := fun q ↦
    OTSelector.Geometry.calibratedReachLevel u (q : ℝ) ∩
      OTSelector.Geometry.calibratedReachLevel (-u) (q : ℝ)
  let C : ι → ℚ → Set E := fun i q ↦
    K i ∩ (extChartAt 𝓘(ℝ, E) (old i)).symm ⁻¹' S q
  let Good : ℚ → M → Prop := fun q y ↦ ∃ (i : ι) (x : E), x ∈ C i q ∧
    (extChartAt 𝓘(ℝ, E) (old i)).symm x = y ∧
    F.HasC11PotentialFamilyAt m (old i) 0 u (G i) (C i q) x ∧
    F.HasC11LevelPositionComparisonAt (old i) (G i) (A i) (q : ℝ) x
  let GoodAll : M → Prop := fun y ↦ ∀ q : ℚ, 0 < q → y ∈ S q → Good q y
  refine ⟨ι, hcount, old, K, U, G, L, A, hdata, hcover, hUA, hreach, ?_⟩
  dsimp only
  intro initial K₀ U₀ hK₀ hU₀ hK₀U₀ hU₀target G₀ L₀ hG₀ hLip₀ hmatch₀
    A₀ hEL₀ hinit₀ hp₀ δ₀ hδ₀ hpartners₀ η hηfinite hη
  let : IsFiniteMeasure η := hηfinite
  let χ₀ := extChartAt 𝓘(ℝ, E) initial
  let C₀ := χ₀.symm '' K₀
  let I := Ioo (-δ₀) δ₀
  let T : ℝ × M → M := fun q ↦ A₀ (χ₀ q.2) q.1
  let ρ := η.restrict C₀
  let κ : Measure ℝ := volume.restrict I
  let θ := κ.prod ρ
  let Ω := θ.map T
  obtain ⟨hC₀, _hT, hpoint, hsection, hTm, _hΩfinite, _hΩI, hΩchart⟩ :=
    hF.original_reach_translation_and_occupation_chartAC hcomplete initial m
      hK₀ hU₀ hK₀U₀ hU₀target hu hG₀ hLip₀ hmatch₀ hEL₀ hinit₀ hp₀
      hδ₀ hpartners₀ η hη
  have hfixedgood (t : ℝ) (ht : t ∈ I) :
      ∀ᵐ z ∂ρ.map (fun y ↦ T (t, y)), GoodAll z :=
    hgood _ (hsection t ht).2
  have hsourcegood (t : ℝ) (ht : t ∈ I) : ∀ᵐ y ∂ρ, GoodAll (T (t, y)) :=
    ae_of_ae_map (hsection t ht).1 (hfixedgood t ht)
  refine ⟨?_, ?_⟩
  · intro t ht
    have hm := (hsection t ht).1
    have hI : ∀ᵐ z ∂ρ.map (fun y ↦ T (t, y)),
        z ∈ OTSelector.Geometry.calibratedInterior u :=
      (ae_map_iff hm (F.measurableSet_calibratedInterior hcomplete hu)).mpr
        ((ae_restrict_mem hC₀.measurableSet).mono fun y hy ↦
          (hpoint (t, y) ⟨ht, hy⟩).2)
    refine ⟨hm, hsourcegood t ht, hfixedgood t ht, inferInstance, ?_, hI,
      (hsection t ht).2⟩
    rw [Measure.map_apply_of_aemeasurable hm MeasurableSet.univ]
    simp only [preimage_univ, Measure.restrict_apply_univ]
  · have hΩgood : ∀ᵐ z ∂Ω, GoodAll z := hgood Ω hΩchart
    have hprod : ∀ᵐ q ∂θ, GoodAll (T q) := ae_of_ae_map hTm hΩgood
    have hswap : ∀ᵐ q ∂ρ.prod κ, GoodAll (T (q.2, q.1)) :=
      (Measure.measurePreserving_swap (μ := ρ) (ν := κ)).quasiMeasurePreserving.ae hprod
    have htime : ∀ᵐ y ∂ρ, ∀ᵐ t ∂κ, GoodAll (T (t, y)) :=
      Measure.ae_ae_of_ae_prod hswap
    have hrat : ∀ᵐ y ∂ρ, ∀ r : ℚ, (r : ℝ) ∈ I → GoodAll (T (r, y)) := by
      apply ae_all_iff.mpr
      intro r
      by_cases hr : (r : ℝ) ∈ I
      · exact (hsourcegood r hr).mono fun _ h _ ↦ h
      · exact Filter.Eventually.of_forall fun _ h ↦ (hr h).elim
    filter_upwards [htime, hrat, ae_restrict_mem hC₀.measurableSet] with y hytime hyrat hyC₀
    refine ⟨hytime, ?_⟩
    have hχK : χ₀ y ∈ K₀ := by
      obtain ⟨x, hx, rfl⟩ := hyC₀
      change χ₀ (χ₀.symm x) ∈ K₀
      simpa only [χ₀.right_inv (hU₀target (hK₀U₀ hx))] using hx
    have h0I : (0 : ℝ) ∈ I := ⟨neg_lt_zero.mpr hδ₀, hδ₀⟩
    have hdu₀ : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (χ₀.symm (χ₀ y)) := by
      apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
      have h := (hpoint (0, y) ⟨h0I, hyC₀⟩).2
      change A₀ (χ₀ y) 0 ∈ OTSelector.Geometry.calibratedInterior u at h
      rwa [hinit₀ (χ₀ y) (hK₀U₀ hχK)] at h
    have hpactual : F.chartMomentumFamily initial A₀ (χ₀ y, 0) =
        (χ₀ y, fderiv ℝ (u ∘ χ₀.symm) (χ₀ y)) :=
      (hp₀ (χ₀ y) (hK₀U₀ hχK)).trans (Prod.ext rfl (hmatch₀ hχK))
    obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners₀ (χ₀ y) hχK
    obtain ⟨hunit, _, _, hclock, hiso, _⟩ :=
      hF.calibrated_translation_of_chartMomentum hcomplete initial hu
        (hU₀target (hK₀U₀ hχK)) (hEL₀ (χ₀ y) (hK₀U₀ hχK))
        (hinit₀ (χ₀ y) (hK₀U₀ hχK)) hpactual hdu₀ hδ₀ ⟨hl, hul⟩ ⟨hr, hur⟩
    intro α β hα hαβ hβ
    obtain ⟨q, hq, c, d, hcd, hwindow, hsegments⟩ :=
      OTSelector.Geometry.exists_rat_prescribed_reach_endpoint_window hδ₀ hα hαβ hβ
    obtain ⟨s, hcs, hsd⟩ := exists_rat_btwn hcd
    have hsJ : (s : ℝ) ∈ Ioo c d := ⟨hcs, hsd⟩
    have hsPair : (s : ℝ) ∈ Ioo α β := hwindow hsJ
    have hsI : (s : ℝ) ∈ I := ⟨hα.trans hsPair.1, hsPair.2.trans hβ⟩
    have hqR : 0 < (q : ℝ) := by exact_mod_cast hq
    obtain ⟨hpairseg, hcalibseg⟩ := hsegments s hsJ
    have hsS : T (s, y) ∈ S q :=
      OTSelector.Geometry.mem_two_sided_calibratedReach_of_isometry hiso hclock hqR.le
        (hcalibseg.trans Ioo_subset_Icc_self)
    obtain ⟨i, x, hxC, hxy, hpotential, hcomparison⟩ := hyrat s hsI q hq hsS
    refine ⟨s, hsPair, q, hq, hpairseg, i, x, hxC, hxy, hpotential, hcomparison, ?_⟩
    have hxK : x ∈ K i := hxC.1
    have hxU : x ∈ U i := (hUA i).2.1 hxK
    have hxTarget : x ∈ (extChartAt 𝓘(ℝ, E) (old i)).target := (hdata i).2.1 hxK
    have hfamily := (hUA i).2.2.2 x hxU
    have hsource : T (s, y) ∈ (extChartAt 𝓘(ℝ, E) (old i)).source := by
      rw [← hxy]
      exact (extChartAt 𝓘(ℝ, E) (old i)).map_target hxTarget
    have hchart : extChartAt 𝓘(ℝ, E) (old i) (T (s, y)) = x := by
      rw [← hxy]
      exact (extChartAt 𝓘(ℝ, E) (old i)).right_inv hxTarget
    have hd0 : A i x 0 = T (s, y) := hfamily.1.trans hxy
    have hmomentum : eulerLagrangePhaseLift (F.chartEnergy (old i))
        (extChartAt 𝓘(ℝ, E) (old i) ∘ A i x) 0 =
          (extChartAt 𝓘(ℝ, E) (old i) (T (s, y)),
            fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) (old i)).symm)
              (extChartAt 𝓘(ℝ, E) (old i) (T (s, y)))) := by
      change F.chartMomentumFamily (old i) (A i) (x, 0) = _
      rw [hchart]
      exact hfamily.2.2.2.trans (Prod.ext rfl ((hdata i).2.2.2.2.2.2.1 hxK))
    have hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (T (s, y)) :=
      hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
        (hpoint (s, y) ⟨hsI, hyC₀⟩).2
    have hends : -δ₀ < δ₀ := by linarith
    have hsat : u (A₀ (χ₀ y) δ₀) - u (A₀ (χ₀ y) (-δ₀)) = δ₀ - (-δ₀) := by
      rw [hclock δ₀ ⟨hends.le, le_rfl⟩, hclock (-δ₀) ⟨le_rfl, hends.le⟩]
      ring
    exact (hF.eq_timeShift_of_chartMomentum_at_calibrated_point (old i) hu
      (hEL₀ (χ₀ y) (hK₀U₀ hχK)) hfamily.2.1 hends hiso hsat
      ⟨hsI.1.le, hsI.2.le⟩ (hunit s) hdu hsource hd0 hmomentum).1

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
