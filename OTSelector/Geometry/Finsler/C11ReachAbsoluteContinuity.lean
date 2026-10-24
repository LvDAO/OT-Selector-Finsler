import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FiniteTimeLipschitz
import OTSelector.Geometry.Finsler.C11PositionRank
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedReach
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Manifold.ChartOccupationAbsoluteContinuity
import OTSelector.Geometry.Manifold.ChartScalarAbsoluteContinuity
import OTSelector.MeasureTheory.NondegenerateDerivativeNull
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11ReachAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11ReachAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.C11ReachAbsoluteContinuity

* **Conditions:** The existing C1,1 core and actual complete family over a prescribed calibrated reach, with a finite chartwise absolutely continuous law.
* **Objects:** All-reach actual translation AC and a finite occupation law carried by the calibrated interior and AC in every chart.
* **Proof detail:** Use the actual nondegenerate position derivative almost everywhere on the compact core for each translated slice, then apply Fubini to the same time–position maps.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap25.pdf#page=19): Theorems 252B–252C (Fubini) and 252G–252H (Tonelli), pp. 19–25.

Source relation (derived): Extends the short-translation measure-class argument over the prescribed reach by actual rank and occupation, not by introducing a new flow.
-/

/-!
# Original translations and occupation on the full calibrated reach

The original complete family on its existing open neighborhood has a nondegenerate
position derivative almost everywhere on the compact contact core. Its actual
translations throughout the prescribed open reach therefore preserve chart absolute
continuity. Averaging those same physical maps gives a finite, chart-absolutely-
continuous occupation law supported in the original calibrated interior.
-/

open Set Filter Metric Manifold Bundle MeasureTheory MeasureTheory.Measure
open scoped Topology ContDiff NNReal ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The same original family transports its restricted physical law throughout the prescribed
open reach and gives a finite chart-absolutely-continuous interior occupation law. -/
theorem original_reach_translation_and_occupation_chartAC
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {A : E → ℝ → M} (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (A x) univ)
    (hinit : ∀ x ∈ U, A x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily old A (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    (η : Measure M) [IsFiniteMeasure η]
    (hη : (η.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m) :
    letI : MetricSpace M := F.metricSpace
    let C₀ := (extChartAt 𝓘(ℝ, E) old).symm '' K
    let I := Ioo (-δ) δ
    let T := fun q : ℝ × M ↦ A (extChartAt 𝓘(ℝ, E) old q.2) q.1
    let θ := (volume.restrict I).prod (η.restrict C₀)
    let Ω := θ.map T
    IsCompact C₀ ∧ ContinuousOn T (I ×ˢ C₀) ∧
      (∀ q ∈ I ×ˢ C₀, u (T q) = u q.2 + q.1 ∧
        T q ∈ OTSelector.Geometry.calibratedInterior u) ∧
      (∀ t ∈ I, AEMeasurable (fun y ↦ T (t, y)) (η.restrict C₀) ∧
        ∀ terminal : M,
          (((η.restrict C₀).map (fun y ↦ T (t, y))).restrict
            (extChartAt 𝓘(ℝ, E) terminal).source).map
            (extChartAt 𝓘(ℝ, E) terminal) ≪ m) ∧
      AEMeasurable T θ ∧ IsFiniteMeasure Ω ∧
      (∀ᵐ y ∂Ω, y ∈ OTSelector.Geometry.calibratedInterior u) ∧
      ∀ terminal : M,
        (Ω.restrict (extChartAt 𝓘(ℝ, E) terminal).source).map
          (extChartAt 𝓘(ℝ, E) terminal) ≪ m := by
  classical
  let : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) old
  let C₀ := χ.symm '' K
  let I := Ioo (-δ) δ
  let T := fun q : ℝ × M ↦ A (χ q.2) q.1
  let θ := (volume.restrict I).prod (η.restrict C₀)
  let Ω := θ.map T
  have hKt : K ⊆ χ.target := hKU.trans hUt
  have hC : IsCompact C₀ := hK.image_of_continuousOn
    ((continuousOn_extChartAt_symm old).mono hKt)
  have hCsource : C₀ ⊆ χ.source := by
    rintro y ⟨x, hx, rfl⟩
    exact χ.map_target (hKt hx)
  have hχK : MapsTo χ C₀ K := by
    rintro y ⟨x, hx, rfl⟩
    simpa only [χ.right_inv (hKt hx)] using hx
  have hAcont : ∀ t : ℝ, ContinuousOn (fun x ↦ A x t) U :=
    fun t ↦ hF.continuousOn_of_C11_initial_momentum hcomplete old hG hLip
      hU hUt hEL hinit hp t
  have hjoint : ContinuousOn (fun q : E × ℝ ↦ A q.1 q.2) (U ×ˢ univ) := by
    intro q hq
    let ψ := extChartAt 𝓘(ℝ, E) (A q.1 q.2)
    obtain ⟨r, C, hr, _, hlegal, hread⟩ :=
      hF.exists_joint_lipschitz_chart_readout_of_C11_initial_momentum hcomplete old
        hG hLip hU hUt hEL hinit hp hq.1 (A q.1 q.2) q.2
        (mem_extChartAt_source (A q.1 q.2))
    have hc : ContinuousAt (fun z : E × ℝ ↦ ψ (A z.1 z.2)) q :=
      (hread.continuousOn q (mem_closedBall_self hr.le)).continuousAt
        (closedBall_mem_nhds q hr)
    have hi : ContinuousAt ψ.symm (ψ (A q.1 q.2)) :=
      (continuousOn_extChartAt_symm (A q.1 q.2)).continuousAt
        ((isOpen_extChartAt_target (I := 𝓘(ℝ, E)) (A q.1 q.2)).mem_nhds
          (ψ.map_source (mem_extChartAt_source (A q.1 q.2))))
    have heq : (fun z : E × ℝ ↦ A z.1 z.2) =ᶠ[𝓝 q]
        (fun z ↦ ψ.symm (ψ (A z.1 z.2))) := by
      filter_upwards [closedBall_mem_nhds q hr] with z hz
      exact (ψ.left_inv (hlegal hz)).symm
    have hcomp : ContinuousAt (fun z : E × ℝ ↦ ψ.symm (ψ (A z.1 z.2))) q :=
      ContinuousAt.comp (f := fun z : E × ℝ ↦ ψ (A z.1 z.2)) hi hc
    exact (hcomp.congr_of_eventuallyEq heq).continuousWithinAt
  have hT : ContinuousOn T (I ×ˢ C₀) :=
    hjoint.comp
      (((continuousOn_extChartAt old).mono hCsource).comp continuousOn_snd
        (fun q hq ↦ hq.2) |>.prodMk continuousOn_fst)
      (fun q hq ↦ ⟨hKU (hχK hq.2), mem_univ _⟩)
  have hcal (x : E) (hx : x ∈ K) :
      ∀ t ∈ I, u (A x t) = u (χ.symm x) + t ∧
        A x t ∈ OTSelector.Geometry.calibratedInterior u := by
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners x hx
    have hd : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (χ.symm x) := by
      apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
      exact ⟨⟨a, dist_pos.mp (hax.symm ▸ hδ), ha.trans hax.symm⟩,
        ⟨b, dist_pos.mp (hxb.symm ▸ hδ), hb.trans hxb.symm⟩⟩
    have hpx : F.chartMomentumFamily old A (x, 0) =
        (x, fderiv ℝ (u ∘ χ.symm) x) :=
      (hp x (hKU hx)).trans (Prod.ext rfl (hmatch hx))
    obtain ⟨_, _, _, hclock, hiso, _⟩ :=
      hF.calibrated_translation_of_chartMomentum hcomplete old hu (hKt hx)
        (hEL x (hKU hx)) (hinit x (hKU hx)) hpx hd hδ ⟨hax, ha⟩ ⟨hxb, hb⟩
    intro t ht
    have htI : t ∈ Icc (-δ) δ := ⟨ht.1.le, ht.2.le⟩
    have hlo : -δ ∈ Icc (-δ) δ := ⟨le_rfl, by linarith⟩
    have hhi : δ ∈ Icc (-δ) δ := ⟨by linarith, le_rfl⟩
    have hdistlo : dist (A x (-δ)) (A x t) = t + δ := by
      have h := hiso.dist_eq ⟨-δ, hlo⟩ ⟨t, htI⟩
      change dist (A x (-δ)) (A x t) = dist (-δ) t at h
      rw [h, Real.dist_eq, abs_of_nonpos (by linarith [ht.1])]
      ring
    have hdisthi : dist (A x t) (A x δ) = δ - t := by
      have h := hiso.dist_eq ⟨t, htI⟩ ⟨δ, hhi⟩
      change dist (A x t) (A x δ) = dist t δ at h
      rw [h, Real.dist_eq, abs_of_nonpos (by linarith [ht.2])]
      ring
    refine ⟨hclock t htI, ⟨A x (-δ), ?_, ?_⟩, ⟨A x δ, ?_, ?_⟩⟩
    · apply dist_pos.mp
      rw [hdistlo]
      linarith [ht.1]
    · rw [hclock t htI, hclock (-δ) hlo, hdistlo]
      ring
    · apply dist_pos.mp
      rw [hdisthi]
      linarith [ht.2]
    · rw [hclock δ hhi, hclock t htI, hdisthi]
      ring
  have hpoint : ∀ q ∈ I ×ˢ C₀, u (T q) = u q.2 + q.1 ∧
      T q ∈ OTSelector.Geometry.calibratedInterior u := by
    intro q hq
    obtain ⟨hc, hi⟩ := hcal (χ q.2) (hχK hq.2) q.1 hq.1
    rw [χ.left_inv (hCsource hq.2)] at hc
    exact ⟨hc, hi⟩
  let ξ := (η.restrict χ.source).map χ
  have hcoord : ξ.restrict K = (η.restrict C₀).map χ :=
    restrict_map_extChartAt_eq_map_chart_core old η hK.measurableSet hKt
  have hχ : AEMeasurable χ (η.restrict C₀) :=
    AEMeasurable.mono_set hCsource
      ((continuousOn_extChartAt old).aemeasurable (isOpen_extChartAt_source old).measurableSet)
  have hrank := hF.ae_alltime_position_rank_of_calibrated_C11_translation hcomplete old
    (m := m) (ν := m) Measure.AbsolutelyContinuous.rfl hK hU hKU hUt hu hG hLip
    hmatch hEL hinit hp hδ hpartners
  have hfixed : ∀ t ∈ I, AEMeasurable (fun y ↦ T (t, y)) (η.restrict C₀) ∧
      ∀ terminal : M,
        (((η.restrict C₀).map (fun y ↦ T (t, y))).restrict
          (extChartAt 𝓘(ℝ, E) terminal).source).map
          (extChartAt 𝓘(ℝ, E) terminal) ≪ m := by
    intro t ht
    have hAt : AEMeasurable (fun x ↦ A x t) (ξ.restrict K) :=
      ((hAcont t).mono hKU).aemeasurable hK.measurableSet
    have hAtmap : AEMeasurable (fun x ↦ A x t) ((η.restrict C₀).map χ) := by
      rw [← hcoord]
      exact hAt
    have hphysical : AEMeasurable (fun y ↦ T (t, y)) (η.restrict C₀) :=
      hAtmap.comp_aemeasurable hχ
    have hpush : (η.restrict C₀).map (fun y ↦ T (t, y)) =
        (ξ.restrict K).map (fun x ↦ A x t) := by
      rw [hcoord, AEMeasurable.map_map_of_aemeasurable hAtmap hχ]
      rfl
    refine ⟨hphysical, fun terminal ↦ ?_⟩
    let ψ := extChartAt 𝓘(ℝ, E) terminal
    let S := K ∩ (fun x ↦ A x t) ⁻¹' ψ.source
    let f := fun x ↦ ψ (A x t)
    have hS : MeasurableSet S := by
      have hopen := (hAcont t).isOpen_inter_preimage hU
        (isOpen_extChartAt_source (I := 𝓘(ℝ, E)) terminal)
      simpa only [← inter_assoc, inter_eq_left.mpr hKU] using
        hK.measurableSet.inter hopen.measurableSet
    have hf : ContinuousOn f S := (continuousOn_extChartAt terminal).comp
      ((hAcont t).mono (fun x hx ↦ hKU hx.1)) (fun x hx ↦ hx.2)
    have hD : ∀ᵐ x ∂m.restrict S,
        HasFDerivWithinAt f (fderiv ℝ f x) S x ∧ (fderiv ℝ f x).det ≠ 0 := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset
        (show S ⊆ K from inter_subset_left) hrank, ae_restrict_mem hS] with x hx hxS
      obtain ⟨hd, c, hc, hbound, hinj⟩ :=
        hx.2.2.2 terminal t (abs_lt.mpr ht) hxS.2
      refine ⟨hd.hasFDerivAt.hasFDerivWithinAt, ?_⟩
      intro hzero
      exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero)
        (LinearMap.ker_eq_bot.mpr hinj)
    have hrestrict : ((ξ.restrict K).map (fun x ↦ A x t)).restrict ψ.source =
        (ξ.restrict S).map (fun x ↦ A x t) := by
      rw [Measure.restrict_map_of_aemeasurable hAt
        (isOpen_extChartAt_source terminal).measurableSet,
        Measure.restrict_restrict' hK.measurableSet, inter_comm]
    have hψ : AEMeasurable ψ
        (((ξ.restrict K).map (fun x ↦ A x t)).restrict ψ.source) :=
      (continuousOn_extChartAt terminal).aemeasurable
        (isOpen_extChartAt_source terminal).measurableSet
    rw [hrestrict] at hψ
    rw [hpush, hrestrict,
      AEMeasurable.map_map_of_aemeasurable hψ
        (AEMeasurable.mono_set (show S ⊆ K from inter_subset_left) hAt)]
    apply Measure.AbsolutelyContinuous.mk
    intro N hN hzero
    change ((ξ.restrict S).map f) N = 0
    rw [Measure.map_apply_of_aemeasurable (hf.aemeasurable hS) hN,
      Measure.restrict_apply' hS, inter_comm]
    exact hη (measure_inter_preimage_eq_zero_of_ae_hasFDerivWithinAt_det_ne_zero m hD hzero)
  obtain ⟨hTm, hΩac⟩ := chartAC_occupation_of_continuousOn m volume η
    isOpen_Ioo.measurableSet hC.measurableSet hT (fun t ht ↦ (hfixed t ht).2)
  let : IsFiniteMeasure (volume.restrict I) :=
    isFiniteMeasure_restrict.mpr (by
      exact ne_of_lt ((measure_mono Ioo_subset_Icc_self).trans_lt
        (isCompact_Icc.measure_lt_top)))
  have hfinite : IsFiniteMeasure Ω := by
    dsimp only [Ω, θ]
    infer_instance
  have hsupport : ∀ᵐ q ∂θ, q ∈ I ×ˢ C₀ :=
    ((Measure.quasiMeasurePreserving_fst
      (μ := volume.restrict I) (ν := η.restrict C₀)).ae
        (ae_restrict_mem isOpen_Ioo.measurableSet)).and
      ((Measure.quasiMeasurePreserving_snd
        (μ := volume.restrict I) (ν := η.restrict C₀)).ae
          (ae_restrict_mem hC.measurableSet))
  have hinterior : ∀ᵐ y ∂Ω, y ∈ OTSelector.Geometry.calibratedInterior u :=
    (ae_map_iff hTm (F.measurableSet_calibratedInterior hcomplete hu)).mpr
      (hsupport.mono fun q hq ↦ (hpoint q hq).2)
  exact ⟨hC, hT, hpoint, hfixed, hTm, hfinite, hinterior, hΩac⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
