import OTSelector.Analysis.Calculus.CommonLevelSection
import OTSelector.Geometry.FinslerPolynomialFamilyJet
import OTSelector.Geometry.FinslerPolynomialFamilyData
import OTSelector.Geometry.FinslerPolynomialFamilyLocalData
import OTSelector.Geometry.FinslerFixedLabelPositionRank
import OTSelector.Geometry.FinslerPolynomialTubeFromCore

/-!
# Calibrated tubes for the actual polynomial family in fixed labels

Original calibrated core data determine the initial phase jet and the central
clock. A smooth polynomial level section with the fixed projection transfers the
established position comparison to its own labels. These data construct a smooth
calibrated tube of the prescribed normalized family on every inner time interval.
-/

open Set Filter Metric MeasureTheory MeasureTheory.Measure Manifold Bundle
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] {F : ContinuousFinslerNorm E M}

/-- The original core, its actual second derivative, and the established position
comparison construct a calibrated tube for the same normalized polynomial family.
No tube, rank, initial phase jet, or distance expansion is assumed. -/
theorem exists_polynomial_calibratedTube_of_original_core
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace) (old : M)
    (m : Measure E) [IsAddHaarMeasure m]
    {C : Set E} (hCt : C ⊆ (extChartAt 𝓘(ℝ, E) old).target)
    {u : M → ℝ} (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hinterior : letI : MetricSpace M := F.metricSpace
      MapsTo (extChartAt 𝓘(ℝ, E) old).symm C
        (OTSelector.Geometry.calibratedInterior u))
    {G : E → ℝ} (hG : ContDiff ℝ 1 G)
    (hval : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) C)
    (hactual : ∀ y ∈ C,
      HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y)
    {x : E} (hxC : x ∈ C)
    (hdensity : Tendsto
      (fun r ↦ m (C ∩ closedBall x r) / m (closedBall x r))
      (𝓝[>] 0) (𝓝 1))
    (hsecond : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) x) x)
    {eL : OpenPartialHomeomorph (E × E) (E × (E →L[ℝ] ℝ))}
    (heL : (eL : E × E → E × (E →L[ℝ] ℝ)) =
      parametricLegendre (F.chartEnergy old))
    (hsource : eL.source ⊆ chartEnergyDomain old)
    (hInv : ContDiffOn ℝ ∞ eL.symm eL.target)
    (hlegal : ∀ y ∈ C, (y, fderiv ℝ G y) ∈ eL.target)
    {Φ : (E × E) → ℝ → M}
    (hEL : ∀ z ∈ chartEnergyDomain old, F.IsEulerLagrangeOn (Φ z) univ)
    (hinit : ∀ z ∈ chartEnergyDomain old,
      tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Φ z) ⟨0, (1 : ℝ)⟩ =
        (extChartAt (𝓘(ℝ, E).prod 𝓘(ℝ, E))
          (⟨old, 0⟩ : TangentBundle 𝓘(ℝ, E) M)).symm z)
    {δ : ℝ} (hδ : 0 < δ)
    (hpartners : letI : MetricSpace M := F.metricSpace
      ∀ y ∈ C, ∃ l r : M,
        dist l ((extChartAt 𝓘(ℝ, E) old).symm y) = δ ∧
        u ((extChartAt 𝓘(ℝ, E) old).symm y) - u l = δ ∧
        dist ((extChartAt 𝓘(ℝ, E) old).symm y) r = δ ∧
        u r - u ((extChartAt 𝓘(ℝ, E) old).symm y) = δ)
    {A : E → ℝ → M} (hcmp : F.HasC11LevelPositionComparisonAt old G A δ x)
    (p₀ : E →L[ℝ] ℝ) (v₀ : E) (hp₀ : p₀ v₀ ≠ 0)
    (hp : (fderiv ℝ G x) v₀ ≠ 0)
    {O : Set (ScalarSecondJet E)} {B : Set p₀.ker}
    (hO : IsOpen O) (hB : IsOpen B) (h0B : (0 : p₀.ker) ∈ B)
    (hj : (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x) ∈ O)
    {σ : ScalarSecondJet E × p₀.ker → E} (hσ : ContDiffOn ℝ ∞ σ (O ×ˢ B))
    (hσ₀ : σ ((x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x), 0) = x)
    (hlevel : let j : ScalarSecondJet E :=
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      ∀ w ∈ B, scalarSecondJetPolynomial j (σ (j, w)) = G x)
    (hprojection :
      let j : ScalarSecondJet E :=
        (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
      let π₀ := (ContinuousLinearMap.fst ℝ p₀.ker ℝ).comp
        (covectorSplitting p₀ v₀ hp₀).symm.toContinuousLinearMap
      ∀ w ∈ B, π₀ (σ (j, w) - x) = w)
    {a b : ℝ} (hab : a < b) (ha : a ∈ Ioo (-δ) δ) (hb : b ∈ Ioo (-δ) δ) :
    Nonempty (F.CalibratedTube (F.polynomialPhaseFamily old Φ eL σ
      (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)) a b u) := by
  let j : ScalarSecondJet E :=
    (x, G x, fderiv ℝ G x, fderiv ℝ (fderiv ℝ G) x)
  let s : p₀.ker → E := fun w ↦ σ (j, w)
  let Γ := F.polynomialPhaseFamily old Φ eL σ j
  let R := p₀.ker.subtypeL -
    ((fderiv ℝ G x).comp p₀.ker.subtypeL).smulRight
      (((fderiv ℝ G x) v₀)⁻¹ • v₀)
  have hs : ContDiffOn ℝ ∞ s B :=
    hσ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hw ↦ ⟨hj, hw⟩)
  have hcore := hF.original_core_unit_energy_clock_and_isometry hcomplete old hu
    hCt hval hactual hEL hinit heL hsource hlegal hδ hpartners x hxC
  have henergy : F.chartEnergy old (eL.symm (x, fderiv ℝ G x)) = 1 / 2 := hcore.2.1
  obtain ⟨B', hB', h0B', hB'B, hlegal', _⟩ :=
    hF.polynomialPhaseFamily_local_data old heL hsource hInv hB h0B hs hσ₀
      (hlegal x hxC) henergy
  have hs' : ContDiffOn ℝ ∞ s B' := hs.mono hB'B
  have hσD : HasFDerivAt s R 0 := by
    apply hasFDerivAt_levelSection_of_fixedProjection p₀ v₀ hp₀
      (hasFDerivAt_scalarSecondJetPolynomial_center j) hp
      ((hs.contDiffAt (hB.mem_nhds h0B)).differentiableAt (by simp)) hσ₀
    · filter_upwards [hB.mem_nhds h0B] with w hw
      exact (hlevel w hw).trans
        (by simp only [scalarSecondJetPolynomial, j, secondJetPolynomial_self])
    · filter_upwards [hB.mem_nhds h0B] with w hw
      exact hprojection w hw
  have hσC1 : ContDiffOn ℝ 1 σ (O ×ˢ B) := hσ.of_le (by simp)
  obtain ⟨hvalue, hjet⟩ :=
    hF.polynomialPhaseFamily_initial_firstJet_of_calibrated_core hcomplete old m
      hCt hu hinterior hG hactual hxC hdensity hsecond heL hsource hInv (hlegal x hxC)
      henergy hO hB h0B hj hσC1 hσ₀ hEL hinit
  change HasFDerivAt (fun w ↦ F.chartMomentumFamily old Γ (w, 0))
    ((fderiv ℝ s 0).prod ((fderiv ℝ (fderiv ℝ G) x).comp (fderiv ℝ s 0))) 0 at hjet
  rw [hσD.fderiv] at hjet
  have hd (w : p₀.ker) (hw : w ∈ B') :=
    hF.polynomialPhaseFamily_seed_data old heL hsource hInv hEL hinit σ j (hlegal' w hw)
  have hΓEL : ∀ w ∈ B', F.IsEulerLagrangeOn (Γ w) univ :=
    fun w hw ↦ (hd w hw).2.2.1
  have hΓsource (w : p₀.ker) (hw : w ∈ B') :
      Γ w 0 ∈ (extChartAt 𝓘(ℝ, E) old).source := by
    dsimp only [Γ]
    rw [(hd w hw).2.2.2.1]
    exact (extChartAt 𝓘(ℝ, E) old).map_target (hd w hw).2.1.1
  have hΓenergy : ∀ w ∈ B', ∀ t : ℝ,
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ w) ⟨t, (1 : ℝ)⟩) = 1 / 2 :=
    fun w hw ↦ (hd w hw).2.2.2.2.2
  have hΓsmooth := (hF.polynomialPhaseFamily_contMDiff old heL hsource hInv
    hEL hinit hB' hs' hlegal').1
  obtain ⟨_, hrank⟩ := levelPositionComparison_of_fixedProjection_phaseJet old hcmp
    p₀ v₀ hp₀ hp hB' h0B' hΓEL hΓsource hjet hvalue
  have hnormal (w : p₀.ker) (hw : w ∈ B') (t : ℝ) (terminal : M)
      (ht : Γ w t ∈ (extChartAt 𝓘(ℝ, E) terminal).source) (ξ : p₀.ker) :
      (F.chartMomentumFamily terminal Γ (w, t)).2
        (fderiv ℝ (fun z ↦ extChartAt 𝓘(ℝ, E) terminal (Γ z t)) w ξ) = 0 := by
    exact hF.polynomialPhaseFamily_gauss_zero old heL hsource hInv hEL hinit hB' hs'
      hlegal' (fun z hz ↦ hlevel z (hB'B hz)) hw terminal t ht ξ
  have hN := ((hF.covectorNormalization_spec old heL hsource hInv
    (show (0 : ℝ) < 1 / 2 by norm_num)).2.2 _ (hlegal x hxC)).2.2.2.2 henergy
  have hcentral : Γ 0 = Φ (eL.symm (x, fderiv ℝ G x)) := by
    funext t
    change Φ (F.covectorNormalization old eL (1 / 2)
      (σ (j, 0), fderiv ℝ (scalarSecondJetPolynomial j) (σ (j, 0)))) t = _
    rw [hσ₀, (hasFDerivAt_scalarSecondJetPolynomial_center j).fderiv, hN]
  have hiso : letI : MetricSpace M := F.metricSpace
      Isometry (fun t : Icc (-δ) δ ↦ Γ 0 t) := by
    simpa only [hcentral] using hcore.2.2.2
  have hseg : Icc a b ⊆ Ioo (-δ) δ :=
    fun _ ht ↦ ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  have hregular (t : ℝ) (ht : t ∈ Icc a b) :
      HasInjectiveManifoldPosition (E := E) (fun w ↦ Γ w t) 0 := by
    intro terminal htarget
    exact (hrank terminal t (abs_lt.mpr (hseg ht)) htarget).2
  have hdim : Module.finrank ℝ p₀.ker + 1 = Module.finrank ℝ E := by
    simpa using (covectorSplitting p₀ v₀ hp₀).toLinearEquiv.finrank_eq
  obtain ⟨T, V, Y, _, _, hJT, h0V, hTV, hYeq, hYs, _, hY, hi, _, hbound, _⟩ :=
    hF.exists_smooth_manifoldTube_calibration hdim hB' hΓEL hΓsmooth hΓenergy
      hnormal h0B' hiso isCompact_Icc
      (fun _ ht ↦ ⟨(hseg ht).1.le, (hseg ht).2.le⟩) hregular 0
  have hstay (t : ℝ) (ht : t ∈ Icc a b) : (t, (0 : p₀.ker)) ∈ Y.source := by
    rw [hYs]
    exact ⟨hJT ht, h0V⟩
  have hhalf (q : ℝ × p₀.ker) (hq : q ∈ Y.source) :
      F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Γ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2 := by
    rw [hYs] at hq
    exact hΓenergy q.2 (hTV hq).2 q.1
  exact ⟨hF.polynomialTubeOfOriginalCore hcomplete old hu hCt hval hactual hEL hinit
    heL hsource hInv hlegal hδ hpartners hxC hσ₀ hY hi hYeq hhalf 0 hbound
    hab ha hb hstay⟩

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
