import OTSelector.Geometry.Finsler.Basic
import OTSelector.Geometry.Finsler.C11FamilyCover
import OTSelector.Geometry.Finsler.C11FiniteLevelSeeds
import OTSelector.Geometry.Finsler.C11FiniteTimeLipschitz
import OTSelector.Geometry.Finsler.C11TimeLabelLocalization
import OTSelector.Geometry.Finsler.CalibratedInterior
import OTSelector.Geometry.Finsler.CalibratedLevelSeedPatch
import OTSelector.Geometry.Finsler.CalibratedTranslation
import OTSelector.Geometry.Finsler.CompleteHamiltonianFamily
import OTSelector.Geometry.Finsler.Energy.Basic
import OTSelector.Geometry.Finsler.Geodesic.Defs
import OTSelector.Geometry.Finsler.LengthMetric
import OTSelector.MeasureTheory.ContinuousConstraintWindow
import OTSelector.Transport.Kantorovich.CalibratedReach

/-!
# Geometry.Finsler.RationalLevelSeeds

* **Conditions:** The actual compact calibrated core sections at rational potential levels and their complete original families.
* **Objects:** Constructed original seed records with kernel coordinates and a countable local readout cover; all rational-level interior points are covered.
* **Proof detail:** Transport each genuine level section into a common kernel model, retain its actual curves/clock and enumerate finite sections over the countable core/level collection.

Mathematical sources:
- [Rotem Assouline, Curvature-Dimension for Autonomous Lagrangians, arXiv:2409.08001v6 (10 February 2026)](https://arxiv.org/pdf/2409.08001v6#page=38): Section 4.3, Proposition 4.18(i)–(iv), pp. 38–39, especially change of variables (4.13); Lemma 4.23 and proof, pp. 46–47.
- [Jiří Lebl, Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)](https://www.jirka.org/ra/realanal2.pdf#page=51): Section 8.5, Theorem 8.5.1, pp. 51–52; Remark 8.5.8, p. 57.
- [D. H. Fremlin, Measure Theory, Volume 4, Appendix](https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=24): Sections 4A2G(e), pp. 15–16; 4A2N(b), p. 22; 4A2Q(h) and proof, pp. 24–25.

Source relation (derived): Derived from the cited geometric/analytic principles with the exact actual source hypotheses. The local construction and its original phase/covector data are retained, rather than asserted as a verbatim source statement.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.FinslerRationalLevelSeeds.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.FinslerRationalLevelSeeds`; the selected original proof blocks follow. -/
section

/-!
# Countable actual seeds at all rational potential levels

Finite original level sections of the exact compact calibrated cover produce a
countable family of measurable seeds. Every seed retains its complete original
unit curves and a countable local Lipschitz coordinate cover.
-/

open Set Metric Manifold Bundle
open scoped Topology ContDiff NNReal

noncomputable section
universe u v
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E : Type u} {M : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The actual seed constructor retains its original section coordinates,
including the exact labels and the entire original complete family. -/
theorem exists_levelSeedPatch_of_coreSection_with_coordinates (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ y ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {p : E →L[ℝ] ℝ} {V : Set p.ker} {σ : p.ker → E}
    (hV : IsOpen V) (hσ : ContDiffOn ℝ 1 σ V) (hσU : MapsTo σ V U)
    (hinj : InjOn σ V)
    (hdim : Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E)
    (h0V : (0 : p.ker) ∈ V) (hcenter : σ 0 ∈ K)
    (hcovector : p = fderiv ℝ G (σ 0))
    (hσD : HasFDerivAt σ p.ker.subtypeL 0)
    (himm : ∀ w ∈ V, Function.Injective (fderiv ℝ σ w))
    (q : ℚ) (hGlevel : ∀ w ∈ V, G (σ w) = (q : ℝ)) :
    ∃ A : CalibratedLevelSeedPatch F u, ∃ e : A.covector.ker ≃L[ℝ] p.ker,
      A.openLabels = e ⁻¹' V ∧ A.labels = e ⁻¹' (V ∩ σ ⁻¹' K) ∧
      (∀ w t, A.curve w t = Γ (σ (e w)) t) ∧ A.level = q ∧
      (fun w ↦ A.curve w 0) '' A.labels =
        (extChartAt 𝓘(ℝ, E) old).symm '' (σ '' (V ∩ σ ⁻¹' K)) := by
  classical
  let _instRationalSeedMetric : MetricSpace M := F.metricSpace
  have hlevel (w) (hw : w ∈ V) (hwK : σ w ∈ K) :
      u ((extChartAt 𝓘(ℝ, E) old).symm (σ w)) = (q : ℝ) :=
    (hval hwK).symm.trans (hGlevel w hw)
  have hcal (x : E) (hx : x ∈ K) :
      (∀ t : ℝ, F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ x)
        ⟨t, (1 : ℝ)⟩) = 1) ∧
      ∀ t ∈ Icc (-δ) δ,
        u (Γ x t) = u ((extChartAt 𝓘(ℝ, E) old).symm x) + t := by
    obtain ⟨a, b, hax, ha, hxb, hb⟩ := hpartners x hx
    have hi : (extChartAt 𝓘(ℝ, E) old).symm x ∈ calibratedInterior u := by
      refine ⟨⟨a, ?_, ha.trans hax.symm⟩, ⟨b, ?_, hb.trans hxb.symm⟩⟩
      · exact dist_pos.mp (hax.symm ▸ hδ)
      · exact dist_pos.mp (hxb.symm ▸ hδ)
    have hm : F.chartMomentumFamily old Γ (x, 0) =
        (x, fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) x) := by
      rw [hp x (hKU hx), hmatch hx]
    have ht := hF.calibrated_translation_of_chartMomentum hcomplete old hu
      (hUt (hKU hx)) (hEL x (hKU hx)) (hinit x (hKU hx)) hm
      (hF.mdifferentiableAt_of_mem_calibratedInterior hcomplete hu hi) hδ
      ⟨hax, ha⟩ ⟨hxb, hb⟩
    exact ⟨ht.1, ht.2.2.2.1⟩
  have hmeas : MeasurableSet (V ∩ σ ⁻¹' K) := by
    simpa only [Set.ofPred_true, inter_univ] using
      measurableSet_calibratedWindow_labels (f := fun _ ↦ (0 : ℝ))
        (g := fun _ ↦ (0 : ℝ)) (c := 0) (d := 0)
        hV.measurableSet hσ.continuousOn hK.isClosed continuousOn_const continuousOn_const
  have hdim' : Module.finrank ℝ (ℝ × p.ker) = Module.finrank ℝ E := by
    rw [Module.finrank_prod, Module.finrank_self, add_comm]
    exact hdim
  obtain ⟨Z, hZ, hZV, r, C, hlocal, hcover⟩ :=
    hF.exists_countable_lipschitz_timeLabel_chart_cover hcomplete old hG hLip hU hUt
      hEL hinit hp hV hσ hσU
  let A : CalibratedLevelSeedPatch F u :=
    { covector := p
      level := q
      openLabels := V
      openLabels_open := hV
      labels := V ∩ σ ⁻¹' K
      labels_measurable := hmeas
      labels_subset := inter_subset_left
      normalization := ContinuousLinearEquiv.ofFinrankEq hdim'
      curve := fun w t ↦ Γ (σ w) t
      c11_presentation := ⟨{
        initialChart := old
        core := K
        domain := U
        potential := G
        gradientConstant := L
        position := σ
        ambient := Γ
        core_compact := hK
        domain_open := hU
        core_subset := hKU
        domain_target := hUt
        potential_contDiff := hG
        gradient_lipschitz := hLip
        potential_eq := hval
        potential_derivative := hactual
        position_contDiff := hσ
        position_domain := hσU
        position_injective := hinj
        position_immersion := himm
        labels_eq := rfl
        curve_eq := rfl
        ambient_complete := hEL
        ambient_initial := hinit
        ambient_momentum := hp
        level_eq := hGlevel
        zero_mem := h0V
        center_mem := hcenter
        covector_eq := hcovector
        position_derivative := hσD }⟩
      continuous_at_time := fun t ↦
        (hF.continuousOn_of_C11_initial_momentum hcomplete old hG hLip hU hUt
          hEL hinit hp t).comp hσ.continuousOn hσU
      complete := fun w hw ↦ hEL (σ w) (hσU hw.1)
      unit := fun w hw ↦ (hcal (σ w) hw.2).1
      initial_injective := by
        intro w hw z hz heq
        apply hinj hw.1 hz.1
        have heq' : (extChartAt 𝓘(ℝ, E) old).symm (σ w) =
            (extChartAt 𝓘(ℝ, E) old).symm (σ z) := by
          simpa only [hinit (σ w) (hσU hw.1), hinit (σ z) (hσU hz.1)] using heq
        exact (extChartAt 𝓘(ℝ, E) old).symm.injOn (hUt (hσU hw.1))
          (hUt (hσU hz.1)) heq'
      reach := δ
      reach_pos := hδ
      clock := by
        intro w hw t ht
        rw [(hcal (σ w) hw.2).2 t ht, hlevel w hw.1 hw.2]
      centers := Z
      centers_countable := hZ
      centers_subset := hZV
      radius := r
      constant := C
      local_data := hlocal
      local_cover := hcover }
  refine ⟨A, ContinuousLinearEquiv.refl ℝ _, rfl, rfl, fun _ _ ↦ rfl, rfl, ?_⟩
  change (fun w ↦ Γ (σ w) 0) '' (V ∩ σ ⁻¹' K) = _
  rw [← image_comp]
  apply image_congr
  intro w hw
  exact hinit (σ w) (hσU hw.1)



theorem exists_levelSeedPatch_of_coreSection (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUt : U ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {G : E → ℝ} {L : ℝ≥0} (hG : ContDiff ℝ 1 G)
    (hLip : LipschitzWith L (fderiv ℝ G))
    (hmatch : EqOn (fderiv ℝ G)
      (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) K)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) K)
    (hactual : ∀ y ∈ K,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {Γ : E → ℝ → M}
    (hEL : ∀ x ∈ U, F.IsEulerLagrangeOn (Γ x) univ)
    (hinit : ∀ x ∈ U, Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x)
    (hp : ∀ x ∈ U, F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x))
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ x ∈ K, ∃ a b : M,
        dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
        u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ)
    {p : E →L[ℝ] ℝ} {V : Set p.ker} {σ : p.ker → E}
    (hV : IsOpen V) (hσ : ContDiffOn ℝ 1 σ V) (hσU : MapsTo σ V U)
    (hinj : InjOn σ V)
    (hdim : Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E)
    (h0V : (0 : p.ker) ∈ V) (hcenter : σ 0 ∈ K)
    (hcovector : p = fderiv ℝ G (σ 0))
    (hσD : HasFDerivAt σ p.ker.subtypeL 0)
    (himm : ∀ w ∈ V, Function.Injective (fderiv ℝ σ w))
    (q : ℚ) (hGlevel : ∀ w ∈ V, G (σ w) = (q : ℝ)) :
    ∃ A : CalibratedLevelSeedPatch F u, A.level = q ∧
      (fun w ↦ A.curve w 0) '' A.labels =
        (extChartAt 𝓘(ℝ, E) old).symm '' (σ '' (V ∩ σ ⁻¹' K)) := by
  obtain ⟨A, _, _, _, _, hlevel, himage⟩ :=
    hF.exists_levelSeedPatch_of_coreSection_with_coordinates hcomplete old hu
      hK hU hKU hUt hG hLip hmatch hval hactual hEL hinit hp hδ hpartners hV hσ hσU
      hinj hdim h0V hcenter hcovector hσD himm q hGlevel
  exact ⟨A, hlevel, himage⟩

/-- All rational levels of the actual calibrated interior have a countable exact
family of measurable original seeds, with complete unit curves and local readouts. -/
theorem exists_countable_rational_levelSeedPatches (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    {u : M → ℝ} (hu : let _instRationalSeedsLip : MetricSpace M := F.metricSpace
      LipschitzWith 1 u) :
    let _instRationalSeedsMetric : MetricSpace M := F.metricSpace
    ∃ κ : Type (max u v), Countable κ ∧ ∃ A : κ → CalibratedLevelSeedPatch F u,
      (⋃ k, (fun w ↦ (A k).curve w 0) '' (A k).labels) =
        {y | y ∈ calibratedInterior u ∧ ∃ q : ℚ, u y = (q : ℝ)} := by
  classical
  let _instRationalSeedsMetric : MetricSpace M := F.metricSpace
  obtain ⟨ι, hcount, old, K, U, G, L, δ, B, Γ, hdata, hcover, hreach, hfamily⟩ :=
    hF.exists_countable_calibrated_C11_family_cover hcomplete hu
  let _instRationalSeedsCountable : Countable ι := hcount
  have hpartners (i : ι) (x : E) (hx : x ∈ K i) : ∃ a b : M,
      dist a ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i ∧
      u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) - u a = δ i ∧
      dist ((extChartAt 𝓘(ℝ, E) (old i)).symm x) b = δ i ∧
      u b - u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = δ i := by
    obtain ⟨a, _, b, _, ha, hfa, hb, hfb⟩ := (hreach i).2.2 x hx
    exact ⟨a, b, ha, hfa, hb, hfb⟩
  have hfinite (i : ι) (q : ℚ) :=
    hF.exists_finite_original_levelSeeds hcomplete (old i) (hdata i).1
      (hfamily i).1 (hfamily i).2.1 (hfamily i).2.2.1 hu
      (hdata i).2.2.1 (hdata i).2.2.2.2.2.1 (hdata i).2.2.2.2.2.2.1
      (hreach i).1 (hpartners i) (q : ℝ)
  choose J a C σ hsection hslice using hfinite
  let H (i : ι) (q : ℚ) := K i ∩ {x | G i x = (q : ℝ)}
  let κ := Σ i : ι, Σ q : ℚ, {x : H i q // x ∈ J i q}
  have hpatch (k : κ) : ∃ A : CalibratedLevelSeedPatch F u, A.level = k.2.1 ∧
      (fun w ↦ A.curve w 0) '' A.labels =
        (extChartAt 𝓘(ℝ, E) (old k.1)).symm ''
          (σ k.1 k.2.1 k.2.2.val ''
            (ball 0 (a k.1 k.2.1 k.2.2.val) ∩ (σ k.1 k.2.1 k.2.2.val) ⁻¹' K k.1)) := by
    obtain ⟨ha, hσ0, hσ, _, hσU, hGlevel, _, hσD, hinj, hdim, himm⟩ :=
      hsection k.1 k.2.1 k.2.2.val k.2.2.property
    exact hF.exists_levelSeedPatch_of_coreSection hcomplete (old k.1) hu
      (hdata k.1).1 (hfamily k.1).1 (hfamily k.1).2.1 (hfamily k.1).2.2.1
      (hdata k.1).2.2.1 (hdata k.1).2.2.2.2.1 (hdata k.1).2.2.2.2.2.2.1
      (hdata k.1).2.2.2.2.2.1 (hdata k.1).2.2.2.2.2.2.2
      (fun x hx ↦ ((hfamily k.1).2.2.2 x hx).2.1)
      (fun x hx ↦ ((hfamily k.1).2.2.2 x hx).1)
      (fun x hx ↦ ((hfamily k.1).2.2.2 x hx).2.2.2)
      (hreach k.1).1 (hpartners k.1) isOpen_ball hσ hσU hinj hdim
      (Metric.mem_ball_self ha) (by rw [hσ0]; exact k.2.2.val.property.1)
      (by rw [hσ0]) hσD himm k.2.1 hGlevel
  choose A hlevel himage using hpatch
  refine ⟨κ, inferInstance, A, ?_⟩
  apply Subset.antisymm
  · intro y hy
    obtain ⟨k, hy⟩ := mem_iUnion.mp hy
    rw [himage k] at hy
    obtain ⟨z, ⟨w, hw, rfl⟩, rfl⟩ := hy
    refine ⟨?_, k.2.1, ?_⟩
    · rw [← hcover]
      exact mem_iUnion.mpr ⟨k.1, σ k.1 k.2.1 k.2.2.val w, hw.2, rfl⟩
    · exact (hsection k.1 k.2.1 k.2.2.val k.2.2.property).2.2.2.2.2.2.1 w hw.1 hw.2
  · rintro y ⟨hy, q, hq⟩
    rw [← hcover] at hy
    obtain ⟨i, z, hz, rfl⟩ := mem_iUnion.mp hy
    have hslicez : z ∈ K i ∩ {x | u ((extChartAt 𝓘(ℝ, E) (old i)).symm x) = (q : ℝ)} :=
      ⟨hz, hq⟩
    rw [hslice i q] at hslicez
    obtain ⟨x, hx, w, hw, hwz⟩ := mem_iUnion₂.mp hslicez
    let k : κ := ⟨i, q, ⟨x, hx⟩⟩
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [himage k]
    exact ⟨z, ⟨w, hw, hwz⟩, rfl⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

end
end
