import OTSelector.Reconstruction.FinslerOriginalAeOpenChartData
import OTSelector.Reconstruction.FinslerOriginalWindowChartUnconditional
import OTSelector.Reconstruction.FinslerOriginalCalibratedInteriorHypothesis
import OTSelector.Reconstruction.FinslerPopulationSeedPhysicalRecovery

/-!
# The open regular set in the population lane

This file installs, in the population lane, the topological hypothesis isolated by
|FinslerOriginalAeOpenChartData|.  The a.e. C1,1 chart datum of
|FinslerOriginalWindowChartAe| carries its pointwise potential/partner data only
on a full-measure Borel set |good|, and the open-domain transfer
|CoreSectionChartDataAe.toCoreSectionChartDataOn| needs |good| to be open.  We
determine exactly what the population lane can and cannot supply.

## What the population lane does supply (section 1)

Every population window is a |CalibratedSeedWindow| whose seed retains a
|C11LevelSeedPresentation|.  The presentation of the seed of window |j| is

* an *open* chart domain |domain| with |domain ⊆ target| and a compact core
  |core ⊆ domain|;
* a C1 potential |potential| with Lipschitz derivative, matching the original
  potential |u| and its derivative on |core|;
* the complete Euler--Lagrange family |ambient| with unit speed, actual initial
  position and actual momentum equal to the potential derivative on the whole
  *open* domain |domain|;
* a C1 level section |position| on the *open* label set |openLabels| mapping into
  |domain|, with injective derivative and exact level law
  |potential (position w) = level|.

Thus the open chart window with its full pointwise curve datum is available
*unconditionally* in the population lane: it is the seed presentation.  We also
prove that the label image lies in the calibrated interior (the population lane's
full-measure set), and that every label initial point has *exact* two-sided
calibration partners at the seed's own reach |reach| (a new pointwise partner
identity, proved from the calibrated-window isometry of
|calibrated_window_of_complete_unit_endpoints|).  This is precisely the partner
datum consumed by the C1,1 chart constructions.

## What the population lane cannot supply from a.e. data (section 2)

The population lane's calibrated interior is full measure under both original
laws (|AeRayClusterData.chartInterior_ae_full|).  Full measure does not produce an
open set: a full-measure Borel set need not contain any open set.  We prove the
sharp form: the existence of an *exact* chart datum, or of an a.e. chart datum
whose full-measure set is open and nonempty, is *equivalent* to the calibrated
interior having nonempty manifold interior.  Hence the open-domain upgrade is not
a consequence of the a.e. population hypotheses; it is exactly the remaining
geometric input.

## The unconditional producer once that input is available (section 3)

Given one interior point of the calibrated interior, the population lane yields
the a.e. window producer |WindowChartDataAe| with an *open* full-measure set for
every window, so |toCoreSectionChartDataOn| applies unconditionally
(|exists_openGood_windowChartDataAe_of_interior|), and the exact window producer
carries a level-seed patch for every window
(|exists_levelSeedPatches_of_interior|), which is the input of the pointwise
consumers.

## Exact remaining sub-gap

|(interior (chartInterior F u)).Nonempty| is not derivable from the population
lane's almost-everywhere data (nor from the geometric C1,1 good cover, which only
gives compact cores).  It is a genuine topological hypothesis, equivalent to the
endgame itself.  The present file reduces the open regular set producer to that
single hypothesis and proves that every other field is constructed, not assumed.
-/
open Set Function Metric Manifold OTSelector.Geometry MeasureTheory
open scoped Topology ContDiff ENNReal NNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe uE uM

variable {E : Type uE} {M : Type uM}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## 1. The open regular set carried by every population window -/

/-- **The open chart domain of a population window seed.**  The seed of every
window retains a C1,1 presentation whose chart domain is open and sits in the
chart target. -/
theorem windowSeed_openDomain (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    IsOpen (windowSeedPresentation P j).domain :=
  (windowSeedPresentation P j).domain_open

/-- **The compact potential core inside the open chart domain.** -/
theorem windowSeed_core_compact (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    IsCompact (windowSeedPresentation P j).core :=
  (windowSeedPresentation P j).core_compact

/-- The compact core lies in the open chart domain. -/
theorem windowSeed_core_subset_domain (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    (windowSeedPresentation P j).core ⊆ (windowSeedPresentation P j).domain :=
  (windowSeedPresentation P j).core_subset

/-- The open chart domain lies in the selected chart target. -/
theorem windowSeed_domain_target (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    (windowSeedPresentation P j).domain ⊆
      (extChartAt 𝓘(ℝ, E) (windowSeedPresentation P j).initialChart).target :=
  (windowSeedPresentation P j).domain_target

/-- The chart potential is C1 with Lipschitz derivative on the chart target. -/
theorem windowSeed_potential_data (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    ContDiff ℝ 1 (windowSeedPresentation P j).potential ∧
      LipschitzWith (windowSeedPresentation P j).gradientConstant
        (fderiv ℝ (windowSeedPresentation P j).potential) :=
  ⟨(windowSeedPresentation P j).potential_contDiff,
    (windowSeedPresentation P j).gradient_lipschitz⟩

/-- The chart potential represents the original potential, with its actual
derivative, on the compact core. -/
theorem windowSeed_potential_core (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    EqOn (windowSeedPresentation P j).potential
        (u ∘ (extChartAt 𝓘(ℝ, E) (windowSeedPresentation P j).initialChart).symm)
        (windowSeedPresentation P j).core ∧
      ∀ y ∈ (windowSeedPresentation P j).core,
        HasFDerivAt
          (u ∘ (extChartAt 𝓘(ℝ, E) (windowSeedPresentation P j).initialChart).symm)
          (fderiv ℝ (windowSeedPresentation P j).potential y) y :=
  ⟨(windowSeedPresentation P j).potential_eq, (windowSeedPresentation P j).potential_derivative⟩

/-- **The complete curve field is exact on the whole open chart domain.**  Every
chart point of the open domain carries its complete Euler--Lagrange curve with
unit speed, actual initial position and actual momentum equal to the potential
derivative. -/
theorem windowSeed_curves_on_openDomain (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    ∀ y ∈ (windowSeedPresentation P j).domain,
      F.IsEulerLagrangeOn ((windowSeedPresentation P j).ambient y) univ ∧
        (windowSeedPresentation P j).ambient y 0 =
          (extChartAt 𝓘(ℝ, E) (windowSeedPresentation P j).initialChart).symm y ∧
        F.chartMomentumFamily (windowSeedPresentation P j).initialChart
            (windowSeedPresentation P j).ambient (y, 0) =
          (y, fderiv ℝ (windowSeedPresentation P j).potential y) := by
  intro y hy
  exact ⟨(windowSeedPresentation P j).ambient_complete y hy,
    (windowSeedPresentation P j).ambient_initial y hy,
    (windowSeedPresentation P j).ambient_momentum y hy⟩

/-- **The level section is exact on the open label set.** -/
theorem windowSeed_level_section (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    ContDiffOn ℝ 1 (windowSeedPresentation P j).position
        (P j).seed.openLabels ∧
      MapsTo (windowSeedPresentation P j).position (P j).seed.openLabels
        (windowSeedPresentation P j).domain ∧
      InjOn (windowSeedPresentation P j).position (P j).seed.openLabels ∧
      (∀ w ∈ (P j).seed.openLabels,
        (windowSeedPresentation P j).potential ((windowSeedPresentation P j).position w) =
          ((P j).seed.level : ℝ)) :=
  ⟨(windowSeedPresentation P j).position_contDiff,
    (windowSeedPresentation P j).position_domain,
    (windowSeedPresentation P j).position_injective,
    (windowSeedPresentation P j).level_eq⟩

/-- **The population lane's full-measure set in its own coordinates: the label
image of every window lies in the calibrated interior.** -/
theorem windowSeed_labelImage_subset_chartInterior
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ) :
    (fun w => (P j).seed.curve w 0) '' (P j).seed.labels ⊆ chartInterior F u := by
  letI : MetricSpace M := F.metricSpace
  rintro x ⟨w, hw, rfl⟩
  exact (P j).seed.mapsTo_initial_calibratedInterior hF hu hw

/-- **Exact two-sided calibration partners on the population window's label
curves.**  Every initial seed point of a retained label has a predecessor and a
successor at the seed's own reach, with exact potential differences.  This is a
pointwise identity, not an almost-everywhere one: it is the partner datum used by
the C1,1 ball/chart constructions. -/
theorem windowSeed_label_partners (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (P : ℕ → F.CalibratedSeedWindow u) (j : ℕ)
    {w : (P j).seed.covector.ker} (hw : w ∈ (P j).seed.labels) :
    letI : MetricSpace M := F.metricSpace
    let S := (P j).seed
    dist (S.curve w (-S.reach)) (S.curve w 0) = S.reach ∧
      u (S.curve w 0) - u (S.curve w (-S.reach)) = S.reach ∧
        dist (S.curve w 0) (S.curve w S.reach) = S.reach ∧
          u (S.curve w S.reach) - u (S.curve w 0) = S.reach := by
  letI : MetricSpace M := F.metricSpace
  let S := (P j).seed
  have hr : 0 < S.reach := S.reach_pos
  have hleft : -S.reach ∈ Icc (-S.reach) S.reach := ⟨le_rfl, by linarith⟩
  have hright : S.reach ∈ Icc (-S.reach) S.reach := ⟨by linarith, le_rfl⟩
  have hzero : (0 : ℝ) ∈ Icc (-S.reach) S.reach := ⟨by linarith, by linarith⟩
  have ha : u (S.curve w (-S.reach)) = (S.level : ℝ) + (-S.reach) :=
    S.clock w hw (-S.reach) hleft
  have hb : u (S.curve w S.reach) = (S.level : ℝ) + S.reach :=
    S.clock w hw S.reach hright
  have h0 : u (S.curve w 0) = (S.level : ℝ) := by
    simpa using S.clock w hw 0 hzero
  obtain ⟨-, hiso, -⟩ :=
    hF.calibrated_window_of_complete_unit_endpoints hu
      (S.complete w hw) (S.unit w hw) ha hb
  have hdist : ∀ t ∈ Icc (-S.reach) S.reach,
      dist (S.curve w 0) (S.curve w t) = |t| := by
    intro t ht
    have h := hiso.dist_eq (⟨0, hzero⟩ : Icc (-S.reach) S.reach) ⟨t, ht⟩
    simpa only [Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg] using h
  have hpred : dist (S.curve w (-S.reach)) (S.curve w 0) = S.reach := by
    have h := hdist (-S.reach) hleft
    rw [abs_neg, abs_of_pos hr] at h
    rw [dist_comm]
    exact h
  have hsucc : dist (S.curve w 0) (S.curve w S.reach) = S.reach := by
    have h := hdist S.reach hright
    rwa [abs_of_pos hr] at h
  refine ⟨hpred, ?_, hsucc, ?_⟩
  · rw [h0, ha]
    ring
  · rw [h0, hb]
    ring

/-! ## 2. The open-domain upgrade is exactly nonempty calibrated interior -/

/-- **Every exact chart datum forces nonempty manifold interior of the calibrated
interior.**  Its open chart domain carries uniform two-sided partners at distance
|δ > 0|, so the open chart image of the domain is an open subset of the
calibrated interior. -/
theorem interior_nonempty_of_chartData
    (C : CoreSectionChartData (F := F) (u := u)) :
    (interior (chartInterior F u)).Nonempty := by
  letI : MetricSpace M := F.metricSpace
  classical
  let e : OpenPartialHomeomorph M E := chartAt E C.old
  have htarget : (extChartAt 𝓘(ℝ, E) C.old).target = (chartAt E C.old).target :=
    extChartAt_target_eq_chartAt
  have hUball : C.U ⊆ e.target := by
    intro z hz
    show z ∈ (chartAt E C.old).target
    rw [← htarget]
    exact C.U_target hz
  have himg : IsOpen (e.symm '' C.U) := e.isOpen_image_symm_of_subset_target C.U_open hUball
  have hne : (e.symm '' C.U).Nonempty :=
    ⟨e.symm (C.σ 0), mem_image_of_mem _ (C.σ_mapsTo C.zero_V)⟩
  have hsymm : ∀ z : E, e.symm z = (extChartAt 𝓘(ℝ, E) C.old).symm z := by
    intro z
    show (chartAt E C.old).symm z = (extChartAt 𝓘(ℝ, E) C.old).symm z
    exact (extChartAt_symm_apply_eq_chartAt (x := C.old) z).symm
  have hsub : e.symm '' C.U ⊆ chartInterior F u := by
    rintro w ⟨z, hz, rfl⟩
    obtain ⟨a, b, ha, hua, hb, hub⟩ := C.partners_U z hz
    rw [hsymm z]
    change (extChartAt 𝓘(ℝ, E) C.old).symm z ∈
      OTSelector.Geometry.calibratedInterior u
    refine ⟨⟨a, ?_, ?_⟩, ⟨b, ?_, ?_⟩⟩
    · exact dist_pos.mp (by rw [ha]; exact C.δ_pos)
    · exact hua.trans ha.symm
    · exact dist_pos.mp (by rw [hb]; exact C.δ_pos)
    · exact hub.trans hb.symm
  exact Set.Nonempty.mono (interior_maximal hsub himg) hne

/-- **A nonempty manifold interior of the calibrated interior supplies the exact
chart datum unconditionally** (through the chart-ball construction of
|FinslerOriginalWindowChartUnconditional|). -/
theorem nonempty_chartData_of_interior_nonempty
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : (interior (chartInterior F u)).Nonempty) :
    Nonempty (CoreSectionChartData (F := F) (u := u)) := by
  obtain ⟨P, ⟨W⟩⟩ :=
    exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx
  exact ⟨W.chartData 0⟩

/-- **Characterization at the exact chart-data level.**  The exact open-domain
chart datum exists exactly when the calibrated interior has nonempty manifold
interior. -/
theorem nonempty_chartData_iff_interior_nonempty
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    Nonempty (CoreSectionChartData (F := F) (u := u)) ↔
      (interior (chartInterior F u)).Nonempty :=
  ⟨fun h => h.elim interior_nonempty_of_chartData,
    nonempty_chartData_of_interior_nonempty hF hcomplete hu⟩

/-- **Characterization at the a.e. chart-data level.**  An a.e. chart datum whose
full-measure set is open and nonempty exists exactly when the calibrated interior
has nonempty manifold interior.  This is the sharp form of the topological
hypothesis isolated by |FinslerOriginalAeOpenChartData|: the open-domain upgrade is
equivalent to the endgame input, hence not a consequence of the a.e. population
data. -/
theorem exists_openGood_aeChartData_iff_interior_nonempty
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    (∃ (μ : Measure E) (A : CoreSectionChartDataAe (F := F) (u := u) μ),
        IsOpen A.good ∧ A.good.Nonempty) ↔
      (interior (chartInterior F u)).Nonempty := by
  constructor
  · rintro ⟨μ, A, hgood, hne⟩
    letI : MetricSpace M := F.metricSpace
    classical
    let e : OpenPartialHomeomorph M E := chartAt E A.old
    have htarget : (extChartAt 𝓘(ℝ, E) A.old).target = (chartAt E A.old).target :=
      extChartAt_target_eq_chartAt
    have hgood_target : A.good ⊆ e.target := by
      intro z hz
      show z ∈ (chartAt E A.old).target
      rw [← htarget]
      exact A.U_target (A.good_subset hz)
    have himg : IsOpen (e.symm '' A.good) :=
      e.isOpen_image_symm_of_subset_target hgood hgood_target
    have hne' : (e.symm '' A.good).Nonempty := hne.image e.symm
    have hsymm : ∀ z : E, e.symm z = (extChartAt 𝓘(ℝ, E) A.old).symm z := by
      intro z
      show (chartAt E A.old).symm z = (extChartAt 𝓘(ℝ, E) A.old).symm z
      exact (extChartAt_symm_apply_eq_chartAt (x := A.old) z).symm
    have hsub : e.symm '' A.good ⊆ chartInterior F u := by
      rintro w ⟨z, hz, rfl⟩
      obtain ⟨a, b, ha, hua, hb, hub⟩ := A.partners_good z hz
      rw [hsymm z]
      change (extChartAt 𝓘(ℝ, E) A.old).symm z ∈
        OTSelector.Geometry.calibratedInterior u
      refine ⟨⟨a, ?_, ?_⟩, ⟨b, ?_, ?_⟩⟩
      · exact dist_pos.mp (by rw [ha]; exact A.δ_pos)
      · exact hua.trans ha.symm
      · exact dist_pos.mp (by rw [hb]; exact A.δ_pos)
      · exact hub.trans hb.symm
    exact Set.Nonempty.mono (interior_maximal hsub himg) hne'
  · intro hx
    obtain ⟨P, ⟨W⟩⟩ :=
      exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx
    refine ⟨0, (W.chartData 0).toAe 0, ?_, ?_⟩
    · rw [CoreSectionChartData.toAe_good]
      exact (W.chartData 0).U_open
    · rw [CoreSectionChartData.toAe_good]
      exact ⟨_, (W.chartData 0).σ_mapsTo (W.chartData 0).zero_V⟩

/-! ## 3. The unconditional producer once one interior point is available -/

/-- **A.e. window producer with an open full-measure set.**  Given one interior
point of the calibrated interior, the population lane yields a window family and
an a.e. window chart producer whose full-measure set is open in every window (so
|CoreSectionChartDataAe.toCoreSectionChartDataOn| applies unconditionally) and
contains the section point. -/
theorem exists_openGood_windowChartDataAe_of_interior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : (interior (chartInterior F u)).Nonempty) (μ : Measure E) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker)
      (W : WindowChartDataAe (F := F) (u := u) κ μ),
      (∀ j, IsOpen ((W.chartData j).good)) ∧
        (∀ j, (W.chartData j).σ 0 ∈ (W.chartData j).good) := by
  obtain ⟨P, ⟨W⟩⟩ :=
    exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx
  refine ⟨P, fun _ => 0, W.toAe (fun _ => 0) μ, ?_, ?_⟩
  · intro j
    show IsOpen (((W.chartData j).toAe μ).good)
    rw [CoreSectionChartData.toAe_good]
    exact (W.chartData j).U_open
  · intro j
    show ((W.chartData j).toAe μ).σ 0 ∈ ((W.chartData j).toAe μ).good
    rw [CoreSectionChartData.toAe_σ, CoreSectionChartData.toAe_good]
    exact (W.chartData j).σ_mapsTo (W.chartData j).zero_V

/-- **A level-seed patch for every window in the population lane.**  Given one
interior point of the calibrated interior, the exact window producer realizes
every window seed through a chart datum and a compact parent core, and the
level-seed constructor supplies the patch fields (open label set, label set,
complete curve family, level) for every window.  These are the patches consumed by
the pointwise reconstruction. -/
theorem exists_levelSeedPatches_of_interior
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (hx : (interior (chartInterior F u)).Nonempty) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u) (W : WindowChartData P),
      ∀ j, ∃ (A : F.CalibratedLevelSeedPatch u)
          (e : A.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
        A.openLabels = e ⁻¹' (W.chartData j).V ∧
          A.labels = e ⁻¹' ((W.chartData j).V ∩
            (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
            (∀ w t, A.curve w t =
              (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
              A.level = (W.chartData j).q := by
  obtain ⟨P, ⟨W⟩⟩ :=
    exists_windowChartData_of_interior (F := F) (u := u) hF hcomplete hu hx
  refine ⟨P, W, fun j => ?_⟩
  exact exists_levelSeedPatch_of_chartData (F := F) (u := u) hF hcomplete hu
    (W.chartData j) (W.parentCore_compact j) (W.parentCore_subset j)
    (W.parentCore_center j)

end OTSelector.Reconstruction
