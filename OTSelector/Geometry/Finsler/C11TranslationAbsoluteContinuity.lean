import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11VolumeTranslation
import OTSelector.Geometry.Finsler.CalibratedDistance
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Energy.Transition
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.Geometry.Finsler.PotentialGlobalFamily
import OTSelector.Geometry.Manifold.ChartLipschitzNull
import OTSelector.Geometry.Manifold.ChartScalarAbsoluteContinuity
import OTSelector.Transport.Kantorovich.CalibratedReach
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerC11TranslationAbsoluteContinuity.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerC11TranslationAbsoluteContinuity`; the selected original proof blocks follow. -/
section

/-!
# Geometry.Finsler.C11TranslationAbsoluteContinuity

* **Conditions:** An original compact C1,1 contact core, its actual complete curves, and a physical law chartwise absolutely continuous to Haar measure.
* **Objects:** Short original translations measurable on the retained core and chartwise absolutely continuous in every output chart.
* **Proof detail:** Identify actual core curves with the constructed short C1,1 translation, use a lower Haar image bound to pull null sets back, then transfer AC through smooth chart changes.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=33): Section 4.2, Theorem 4.11, p. 33, Lemmas 4.12–4.13, pp. 34–36, proof of Theorem 4.11, p. 36; Lemma 4.15, p. 37.
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=39): Section 4.3, Lemma 4.21(i)–(iii), p. 39, and proof pp. 40–42.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=38): Proposition 262D, p. 11; Corollary 262N, p. 17; Proposition 264G, pp. 38–39; Theorem 264I, pp. 40–41.
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap26.pdf#page=26): Theorem 263D(i)–(v), pp. 26–28; Lemma 263C, p. 25; decomposition Lemma 262M, pp. 15–17.

Source relation (derived): A measure-class consequence of local near-identity flow bounds. Off-core values of the complete family need no global measurable representation.
-/

/-!
# Original short translations preserve chart absolute continuity

The original complete curves agree on their calibrated core with the short C1,1
translation supplied by the original potential extension. Lower Haar image bounds
therefore preserve absolute continuity of actual restricted physical laws. Smooth
chart changes transfer the conclusion to every output chart. The same core, extension
and complete family are retained, without global measurability of their off-core values.
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E] in
private theorem map_restrict_ac_of_lower_image_bound
    (m ξ : Measure E) (hξ : ξ ≪ m) {D : Set E} (hD : MeasurableSet D)
    {R : E → E} (hR : AEMeasurable R (ξ.restrict D)) {c : ℝ≥0∞}
    (hbound : ∀ B ⊆ D, m B ≤ c * m (R '' B)) :
    (ξ.restrict D).map R ≪ m := by
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hzero
  have himage : m (R '' (R ⁻¹' N ∩ D)) = 0 :=
    measure_mono_null (by rintro _ ⟨x, hx, rfl⟩; exact hx.1) hzero
  have hpre : m (R ⁻¹' N ∩ D) = 0 := by
    apply nonpos_iff_eq_zero.mp
    calc
      m (R ⁻¹' N ∩ D) ≤ c * m (R '' (R ⁻¹' N ∩ D)) :=
        hbound _ inter_subset_right
      _ = 0 := by rw [himage, mul_zero]
  rw [Measure.map_apply_of_aemeasurable hR hN, Measure.restrict_apply' hD]
  exact hξ hpre

omit [T2Space M] [PreconnectedSpace M] in
private theorem chartAC_of_concentrated_chart
    (m : Measure E) [IsAddHaarMeasure m] (ρ : Measure M) (old : M)
    (hac : (ρ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hsource : ρ (extChartAt 𝓘(ℝ, E) old).sourceᶜ = 0) (terminal : M) :
    (ρ.restrict (extChartAt 𝓘(ℝ, E) terminal).source).map
      (extChartAt 𝓘(ℝ, E) terminal) ≪ m := by
  let χ := extChartAt 𝓘(ℝ, E) old
  let ψ := extChartAt 𝓘(ℝ, E) terminal
  apply Measure.AbsolutelyContinuous.mk
  intro N hN hzero
  let S := (ψ ⁻¹' N ∩ ψ.source) ∩ χ.source
  have hNimage : m (ψ '' S) = 0 :=
    measure_mono_null (by rintro _ ⟨x, hx, rfl⟩; exact hx.1.1) hzero
  have hdomain : ψ '' S ⊆ chartTransitionDomain old terminal := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨ψ.map_source hx.1.2, ?_⟩
    change χ.source (ψ.symm (ψ x))
    rw [ψ.left_inv hx.1.2]
    exact hx.2
  have hdiff : DifferentiableOn ℝ (chartTransition (E := E) old terminal) (ψ '' S) :=
    ((contDiffOn_chartTransition old terminal).differentiableOn (by simp)).mono hdomain
  have hz := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero m hdiff hNimage
  have heq : (chartTransition old terminal ∘ ψ) '' S = χ '' S := by
    apply Set.image_congr
    intro x hx
    change χ (ψ.symm (ψ x)) = χ x
    rw [ψ.left_inv hx.1.2]
  rw [image_image] at hz
  change m ((chartTransition old terminal ∘ ψ) '' S) = 0 at hz
  rw [heq] at hz
  have hS : ρ S = 0 := measure_eq_zero_of_null_chart_image m ρ old hac
    (fun _ hx ↦ hx.2) hz
  have hψ : AEMeasurable ψ (ρ.restrict ψ.source) :=
    (continuousOn_extChartAt terminal).aemeasurable
      (isOpen_extChartAt_source terminal).measurableSet
  rw [Measure.map_apply_of_aemeasurable hψ hN,
    Measure.restrict_apply' (isOpen_extChartAt_source terminal).measurableSet]
  exact (measure_inter_conull (s := ψ ⁻¹' N ∩ ψ.source) hsource).symm.trans hS

/-- The retained complete family preserves chart absolute continuity of every original
law under actual short translations of its core. The interval is chosen before the law;
joint coordinate regularity, the original clock and interior membership are retained. -/
theorem exists_original_short_translation_chartAC
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (old : M) (m : Measure E) [IsAddHaarMeasure m]
    {K : Set E} (hKm : MeasurableSet K)
    (hK : K ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {A : E → ℝ → M}
    (hA : ∀ x ∈ K,
      A x 0 = (extChartAt 𝓘(ℝ, E) old).symm x ∧
      F.IsEulerLagrangeOn (A x) univ ∧
      F.chartMomentumFamily old A (x, 0) = (x, fderiv ℝ G x))
    {x₀ : E} (hx₀ : x₀ ∈ K) :
    letI : MetricSpace M := F.metricSpace
    ∃ r τ : ℝ, 0 < r ∧ 0 < τ ∧ τ ≤ δ / 2 ∧
      closedBall x₀ r ⊆ (extChartAt 𝓘(ℝ, E) old).target ∧
      let D := K ∩ closedBall x₀ r
      (∃ C : ℝ≥0, LipschitzOnWith C
        (fun q : ℝ × E ↦ extChartAt 𝓘(ℝ, E) old (A q.2 q.1))
        (Icc (-τ) τ ×ˢ D)) ∧
      ∀ t ∈ Icc (-τ) τ,
        MapsTo (fun x ↦ A x t) D (extChartAt 𝓘(ℝ, E) old).source ∧
        (∀ x ∈ D, u (A x t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t ∧
          A x t ∈ OTSelector.Geometry.calibratedInterior u) ∧
        ∀ η : Measure M,
          (η.restrict (extChartAt 𝓘(ℝ, E) old).source).map
            (extChartAt 𝓘(ℝ, E) old) ≪ m →
          let C₀ := (extChartAt 𝓘(ℝ, E) old).symm '' D
          let T := fun y ↦ A (extChartAt 𝓘(ℝ, E) old y) t
          AEMeasurable T (η.restrict C₀) ∧
            ∀ terminal : M,
              (((η.restrict C₀).map T).restrict
                (extChartAt 𝓘(ℝ, E) terminal).source).map
                (extChartAt 𝓘(ℝ, E) terminal) ≪ m := by
  classical
  let : MetricSpace M := F.metricSpace
  let χ := extChartAt 𝓘(ℝ, E) old
  obtain ⟨r, τ, Γ, hr, hτ, hτhalf, hball, hinit, _, ⟨C, hjoint⟩, hflow, hcal⟩ :=
    hF.exists_C11_calibrated_volume_translation_lipschitz hcomplete old m hK hu
      hG hLip hmatch hδ hpartners hx₀
  let D := K ∩ closedBall x₀ r
  have hD : MeasurableSet D := hKm.inter isClosed_closedBall.measurableSet
  have hDt : D ⊆ χ.target := fun _ hx ↦ hK hx.1
  have htime : Icc (-τ) τ ⊆ Icc (-δ) δ := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have heq (x : E) (hx : x ∈ D) : A x = Γ x := by
    obtain ⟨l, s, hl, hul, hs, hus⟩ := hpartners x hx.1
    have hdu : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (χ.symm x) := by
      apply hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu
      refine ⟨⟨l, ?_, hul.trans hl.symm⟩, ⟨s, ?_, hus.trans hs.symm⟩⟩
      · exact dist_pos.mp (hl.symm ▸ hδ)
      · exact dist_pos.mp (hs.symm ▸ hδ)
    obtain ⟨ha0, haEL, hap⟩ := hA x hx.1
    have hp : F.chartMomentumFamily old A (x, 0) =
        (x, fderiv ℝ (u ∘ χ.symm) x) := by
      rw [hap, hmatch hx.1]
    obtain ⟨haspeed, _, _, haclock, _, _⟩ :=
      hF.calibrated_translation_of_chartMomentum hcomplete old hu (hK hx.1)
        haEL ha0 hp hdu hδ ⟨hl, hul⟩ ⟨hs, hus⟩
    obtain ⟨hg0, hgEL, _, _⟩ := hinit x hx.2
    apply hF.eq_of_complete_unitSpeed_calibrated_curves hu hδ haEL hgEL
      (ha0.trans hg0.symm) haspeed (hcal x hx).1
      (C := u (χ.symm x)) (D := u (χ.symm x))
    · intro t ht
      simpa only [add_comm] using haclock t ⟨by linarith [ht.1], ht.2⟩
    · intro t ht
      simpa only [add_comm] using ((hcal x hx).2.2.1 t
        ⟨by linarith [ht.1], ht.2⟩).1
    · rwa [ha0]
  have hAjoint : LipschitzOnWith C
      (fun q : ℝ × E ↦ χ (A q.2 q.1)) (Icc (-τ) τ ×ˢ D) := by
    intro q hq q' hq'
    change edist (χ (A q.2 q.1)) (χ (A q'.2 q'.1)) ≤ C * edist q q'
    rw [heq q.2 hq.2, heq q'.2 hq'.2]
    exact hjoint ⟨hq.1, hq.2.2⟩ ⟨hq'.1, hq'.2.2⟩
  refine ⟨r, τ, hr, hτ, hτhalf, hball, ⟨C, hAjoint⟩, ?_⟩
  intro t ht
  have hlegal : MapsTo (fun x ↦ A x t) D χ.source := by
    intro x hx
    change A x t ∈ χ.source
    rw [heq x hx]
    exact (hflow t ht).1 hx.2
  refine ⟨hlegal, ?_, ?_⟩
  · intro x hx
    rw [heq x hx]
    exact ⟨((hcal x hx).2.2.1 t (htime ht)).1, ((hcal x hx).2.2.2 t ht).1⟩
  · intro η hη
    let ξ := (η.restrict χ.source).map χ
    let C₀ := χ.symm '' D
    let T : M → M := fun y ↦ A (χ y) t
    let R : E → E := fun x ↦ χ (A x t)
    let ρ := (ξ.restrict D).map (fun x ↦ A x t)
    change AEMeasurable T (η.restrict C₀) ∧
      ∀ terminal : M, (((η.restrict C₀).map T).restrict
        (extChartAt 𝓘(ℝ, E) terminal).source).map
        (extChartAt 𝓘(ℝ, E) terminal) ≪ m
    have hRcont : ContinuousOn R D := hAjoint.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id) (fun x hx ↦ ⟨ht, hx⟩)
    have hAcont : ContinuousOn (fun x ↦ A x t) D :=
      ((continuousOn_extChartAt_symm old).comp hRcont
        (fun x hx ↦ χ.map_source (hlegal hx))).congr
          (fun x hx ↦ (χ.left_inv (hlegal hx)).symm)
    have hAt : AEMeasurable (fun x ↦ A x t) (ξ.restrict D) :=
      hAcont.aemeasurable hD
    have hcoord : ξ.restrict D = (η.restrict C₀).map χ :=
      restrict_map_extChartAt_eq_map_chart_core old η hD hDt
    have hCsource : C₀ ⊆ χ.source := by
      rintro _ ⟨x, hx, rfl⟩
      exact χ.map_target (hDt hx)
    have hχ : AEMeasurable χ (η.restrict C₀) :=
      AEMeasurable.mono_set hCsource
        ((continuousOn_extChartAt old).aemeasurable
          (isOpen_extChartAt_source old).measurableSet)
    have hAtmap : AEMeasurable (fun x ↦ A x t) ((η.restrict C₀).map χ) := by
      rw [← hcoord]
      exact hAt
    have hT : AEMeasurable T (η.restrict C₀) := hAtmap.comp_aemeasurable hχ
    have hpush : (η.restrict C₀).map T = ρ := by
      dsimp only [ρ]
      rw [hcoord, AEMeasurable.map_map_of_aemeasurable hAtmap hχ]
      rfl
    have hρsource : ∀ᵐ y ∂ρ, y ∈ χ.source :=
      (ae_map_iff hAt (isOpen_extChartAt_source old).measurableSet).mpr
        ((ae_restrict_mem hD).mono fun x hx ↦ hlegal hx)
    have hrestrict : ρ.restrict χ.source = ρ :=
      Measure.restrict_eq_self_of_ae_mem hρsource
    have hχρ : AEMeasurable χ ρ := by
      rw [← hrestrict]
      exact (continuousOn_extChartAt old).aemeasurable
        (isOpen_extChartAt_source old).measurableSet
    have hac : (ρ.restrict χ.source).map χ ≪ m := by
      rw [hrestrict]
      change ((ξ.restrict D).map (fun x ↦ A x t)).map χ ≪ m
      rw [AEMeasurable.map_map_of_aemeasurable hχρ hAt]
      apply map_restrict_ac_of_lower_image_bound m ξ hη hD (hRcont.aemeasurable hD)
        (c := (2 : ℝ≥0∞) ^ Module.finrank ℝ E)
      intro B hB
      have hvol := ((hflow t ht).2.2 B (fun x hx ↦ (hB hx).2)).2
      have himage : (fun x ↦ χ (Γ x t)) '' B = R '' B := by
        apply Set.image_congr
        intro x hx
        change χ (Γ x t) = χ (A x t)
        rw [heq x (hB hx)]
      rwa [himage] at hvol
    refine ⟨hT, fun terminal ↦ ?_⟩
    rw [hpush]
    exact chartAC_of_concentrated_chart m ρ old hac
      (mem_ae_iff.mp hρsource) terminal

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
