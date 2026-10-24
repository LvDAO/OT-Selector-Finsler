import OTSelector.Geometry.FinslerOriginalDeficitTransfer
import OTSelector.Geometry.FinslerTwoSectionPhaseJet
import OTSelector.Geometry.Finsler.InitialFamilyIdentity
import OTSelector.Geometry.FinslerCalibratedPhaseData
import OTSelector.Geometry.FinslerCalibratedTubeDistanceJet
import OTSelector.Geometry.Finsler.C11LevelSmoothTube
import OTSelector.Geometry.FinslerPhaseActionTube
import OTSelector.Geometry.Finsler.CalibratedCompleteCylinder

/-!
# Original deficit on the selected calibrated core

The original core, its C1 potential extension and the same selected smooth level
family supply the geometric data of the second-order deficit transfer. No action
stationarity, distance jet or potential-remainder estimate is assumed separately.
The comparison retains the original complete curves and the given smooth family.
-/

open Set Filter Metric Manifold Bundle Asymptotics
open scoped Topology ContDiff NNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [PreconnectedSpace M]
  {F : ContinuousFinslerNorm E M} {G P : E → ℝ} {x : E}


/-- The actual original calibrated core and the same selected smooth level family
have second-order equivalent distance deficits on the allowed original labels.
The intermediate phase jets, stationary action and distance jet are all derived. -/
theorem original_deficit_sub_selected_smooth_isLittleO
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
    let Y : ℝ → ((fderiv ℝ G x).ker) → M := fun r w ↦ Γ w (r - c)
    (fun q : ((fderiv ℝ G x).ker) × ((fderiv ℝ G x).ker) ↦
      ((F.lengthEDist (X a q.1) (X b q.2)).toReal -
        u (X b q.2) + u (X a q.1)) -
      ((F.lengthEDist (Y a q.1) (Y b q.2)).toReal - (b - a)))
      =o[𝓝[S ×ˢ S] (0, 0)] fun q ↦ ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
  let : MetricSpace M := F.metricSpace
  let c := G x
  let S := BG ∩ σG ⁻¹' K
  let ta := a - c
  let tb := b - c
  let z₀ := e.symm (x, fderiv ℝ G x)
  let R : ((fderiv ℝ G x).ker) → E × E := fun w ↦ e.symm (σG w, fderiv ℝ G (σG w))
  let N : ((fderiv ℝ G x).ker) → E × E := fun w ↦ (σP w, v w)
  have hz₀ : z₀ ∈ chartEnergyDomain old := hsub (e.map_target hp)
  have hzfst : z₀.1 = x := (parametricLegendre_inverse_components he hp).1
  have hzleg : fiberLegendre (F.chartEnergy old) z₀ = fderiv ℝ G x :=
    (parametricLegendre_inverse_components he hp).2
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
  obtain ⟨Phi, hΦEL, hΦinit, hΦC2⟩ :=
    hF.exists_complete_tangentFamily_C2 hcomplete old 0
  obtain ⟨hR0, hN0, hR, hN, hlegal⟩ :=
    hF.same_initial_phaseJet_of_two_sections old 0 hsecond he hsub hInv hp hB h0
      hσG0 hσG hσP0 hσPD (hv.continuousOn.continuousAt (hB.mem_nhds h0))
      hv0 hstate (fun w hw ↦ hΓEL w hw 0 (mem_univ _)) hΓinit hjet
  change R 0 = z₀ at hR0
  change N 0 = z₀ at hN0
  have hNcurve (w : ((fderiv ℝ G x).ker)) (hw : w ∈ B) : Phi (N w) = Γ w := by
    funext t
    exact hF.eqOn_of_isEulerLagrangeOn isOpen_univ isPreconnected_univ
      (hΦEL (N w) (hstate w hw)) (hΓEL w hw) (mem_univ 0)
      ((hΦinit (N w) (hstate w hw)).trans (hΓinit w hw).symm) (mem_univ t)
  have hcentral : Phi z₀ = Γ 0 := by
    simpa only [hN0] using hNcurve 0 h0
  have hNunit (w : ((fderiv ℝ G x).ker)) (hw : w ∈ B) : (F.chartLength old (N w) : ℝ) = 1 := by
    have heN := (congrArg F.energy (hΓinit w hw)).symm.trans (henergy w hw 0)
    change F.chartEnergy old (N w) = 1 / 2 at heN
    rw [F.chartLength_eq_sqrt_energy, heN]
    norm_num
  have hzunit : (F.chartLength old z₀ : ℝ) = 1 := by
    simpa only [hN0] using hNunit 0 h0
  have hmatch : fderiv ℝ P z₀.1 =
      fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) z₀ := by
    calc
      fderiv ℝ P z₀.1 = fderiv ℝ G x := by rw [hzfst, hDP]
      _ = fiberLegendre (F.chartEnergy old) z₀ := hzleg.symm
      _ = fiberLegendre (fun z ↦ (F.chartLength old z : ℝ)) z₀ := by
        simpa only [fiberLegendre, hzunit, one_smul] using
          hF.chartLegendre_eq_length_smul_fderiv old hz₀
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
  obtain ⟨hdC, _, hd⟩ := hF.tubeCoordinateDistance_jet_of_calibrated_curve hcomplete
    hY hi hYeq hhalfY 0 hbound htab (hΓEL 0 h0) hstay hmin hu hsat hduStart
  obtain ⟨hActionC2, hAction0⟩ := hF.stationary_phaseLengthAction_of_manifoldTube old
    hΦEL hΦinit hΦC2 hz₀ (hP.contDiffAt.of_le (by simp)) hmatch hY hi hYeq
    (hstay ta (left_mem_Icc.mpr htab.le)) (hstay tb (right_mem_Icc.mpr htab.le))
    hcentral (hdC.of_le (by simp)) hd
  have hPGx : (fun y ↦ P y - G y) =o[𝓝 x] fun y ↦ ‖y - x‖ ^ 2 :=
    matched_second_jets_sub_isLittleO
      (Eventually.of_forall fun y ↦ (hP.differentiable (by simp) y).hasFDerivAt)
      (Eventually.of_forall fun y ↦ (hG.differentiable one_ne_zero y).hasFDerivAt)
      hPsecond hsecond hPx hDP
  have hPG : (fun y ↦ P y - G y) =o[𝓝 z₀.1] fun y ↦ ‖y - z₀.1‖ ^ 2 := by
    simpa only [hzfst] using hPGx
  have hReq : ∀ᶠ w in 𝓝[S] (0 : ((fderiv ℝ G x).ker)), Phi (R w) = A (σG w) := by
    filter_upwards [hlegal.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hw hwS
    have hy : σG w ∈ K := hwS.2
    have hs : A (σG w) 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
      rw [(hA (σG w) hy).1]
      exact (extChartAt 𝓘(ℝ, E) old).map_target (hKt hy)
    exact hF.eq_complete_family_of_chartMomentum old hΦEL hΦinit he hsub
      (hA (σG w) hy).2.1 hs hw.1 (hA (σG w) hy).2.2
  have hRdata : ∀ᶠ w in 𝓝[S] (0 : ((fderiv ℝ G x).ker)),
      (F.chartLength old (R w) : ℝ) = 1 ∧
      u (Phi (R w) ta) = G (R w).1 + ta ∧
      u (Phi (R w) tb) = G (R w).1 + tb := by
    filter_upwards [hlegal.filter_mono nhdsWithin_le_nhds,
      nhdsWithin_le_nhds (hBG.mem_nhds h0G), self_mem_nhdsWithin] with w hw hwG hwS
    have hy : σG w ∈ K := hwS.2
    have hgrad := (hactual (σG w) hy).fderiv
    have htarget : (σG w, fderiv ℝ
        (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (σG w)) ∈ e.target := by
      simpa only [hgrad] using hw.1
    obtain ⟨l, r, hl, hul, hr, hur⟩ := hpartners (σG w) hy
    have hdata := hF.calibrated_phase_data_of_original_covector hcomplete old hu
      hΦEL hΦinit he hsub htarget (hdu (σG w) hy) hδ ⟨hl, hul⟩ ⟨hr, hur⟩
    rw [hgrad] at hdata
    have hbase : (R w).1 = σG w := (parametricLegendre_inverse_components he hw.1).1
    have hvalue : u ((extChartAt 𝓘(ℝ, E) old).symm (σG w)) = G x :=
      (hval hy).symm.trans (hGlevel w hwG)
    refine ⟨hdata.1, ?_, ?_⟩
    · simpa only [hbase, hGlevel w hwG, hvalue] using
        hdata.2 ta ⟨hta.1.le, hta.2.le⟩
    · simpa only [hbase, hGlevel w hwG, hvalue] using
        hdata.2 tb ⟨htb.1.le, htb.2.le⟩
  have hNdata : ∀ᶠ w in 𝓝[S] (0 : ((fderiv ℝ G x).ker)),
      (F.chartLength old (N w) : ℝ) = 1 ∧ P (N w).1 = P z₀.1 := by
    filter_upwards [nhdsWithin_le_nhds (hB.mem_nhds h0)] with w hw
    exact ⟨hNunit w hw, (hPlevel w hw).trans (congrArg P hzfst).symm⟩
  have htransfer := F.original_deficit_sub_smooth_isLittleO_of_phaseAction old
    Phi P G u a b c hActionC2 hAction0 hR.hasFDerivWithinAt hN.hasFDerivWithinAt
    hR0 hN0 hPG hRdata hNdata
  have hNeq : ∀ᶠ w in 𝓝[S] (0 : ((fderiv ℝ G x).ker)), Phi (N w) = Γ w := by
    filter_upwards [nhdsWithin_le_nhds (hB.mem_nhds h0)] with w hw
    exact hNcurve w hw
  apply htransfer.congr' ?_ (Filter.EventuallyEq.rfl)
  have hboth := Filter.Eventually.prod_mk (hReq.and hNeq) (hReq.and hNeq)
  rw [← nhdsWithin_prod_eq] at hboth
  filter_upwards [hboth] with q hq
  rw [hq.1.1, hq.2.1, hq.1.2, hq.2.2]

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
