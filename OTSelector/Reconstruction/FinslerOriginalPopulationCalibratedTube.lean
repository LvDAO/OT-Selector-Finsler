import OTSelector.Geometry.Finsler.CalibratedSeedWindow
import OTSelector.Reconstruction.FinslerOriginalInteriorNonempty

/-!
# The calibrated tube inside the population lane

|FinslerOriginalInteriorNonempty| proved that the paper's local calibrated tube
(main.tex:1063, Section "Local geometry of calibrated Finsler ray tubes", label
sec:raytube) yields the endgame input |(interior (chartInterior F u)).Nonempty|.
This file instantiates that tube from the population-lane seed data.

## The instantiation

A constructed calibrated level seed supplies, with no extra hypothesis:

* the open time interval |Ioo (-reach) reach| (or the window's rational interval),
* complete unit-speed Euler--Lagrange radial curves (fields |complete| and |unit|),
* the calibration clock |u (curve w t) = level + t| on the reach (field |clock|),
* C^1 regularity of every radial curve (|hF.contMDiffOn_of_isEulerLagrangeOn|),
* a nonempty transverse label set, because the C11 presentation's |position 0| lies
  in the compact core (|zero_mem| and |center_mem|),
* the calibrated interior containment of the whole tube image: the complete-curve
  cylinder theorem |calibrated_window_of_complete_unit_endpoints| turns the seed
  clock into two-sided calibration (|seedTubeImage_subset_chartInterior|).

The single field of |CalibratedTube| the seed records do not supply is the
openness of the tube image.  The seed labels are only Borel (field
|labels_measurable|), so the tube image is the Borel ray-cluster parametrization
of main.tex:1173-1185, not an open smooth foliation; main.tex:1076-1078 says
exactly that the smooth calibrated tube "is a local geometric hypothesis; we do
not assume that arbitrary marginals already supply such tubes."  Accordingly
|seedCalibratedTube| takes the image openness as its only extra argument and
discharges every other tube field from the population data.

## Consequence

Granting one population seed with a nonempty open piece in its tube image
(the weakest explicit form of the missing input), the calibrated interior has
nonempty manifold interior, and hence the a.e.-to-exact upgrade produces the
open-domain window data and the per-window level-seed patches.
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

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Subtracting a constant from the potential does not change the calibrated
interior: the two calibration equations only involve potential differences.
This is the harmless additive normalization that reconciles the seed clock
|u (curve w t) = level + t| with the tube clock of the paper. -/
theorem calibratedInterior_sub_const {M₀ : Type*} [MetricSpace M₀]
    (u : M₀ → ℝ) (c : ℝ) :
    OTSelector.Geometry.calibratedInterior (fun x => u x - c) =
      OTSelector.Geometry.calibratedInterior u := by
  ext x
  simp only [OTSelector.Geometry.calibratedInterior, mem_ofPred_eq]
  have key : ∀ a : M₀, (u x - c) - (u a - c) = u x - u a := fun a => by ring
  have key' : ∀ b : M₀, (u b - c) - (u x - c) = u b - u x := fun b => by ring
  constructor
  · rintro ⟨⟨a, ha, hua⟩, ⟨b, hb, hub⟩⟩
    exact ⟨⟨a, ha, by simpa only [key a] using hua⟩,
      ⟨b, hb, by simpa only [key' b] using hub⟩⟩
  · rintro ⟨⟨a, ha, hua⟩, ⟨b, hb, hub⟩⟩
    exact ⟨⟨a, ha, by simpa only [← key a] using hua⟩,
      ⟨b, hb, by simpa only [← key' b] using hub⟩⟩

/-! ## The seed tube image and its unconditional calibrated containment -/

/-- The population-lane tube image: the seed curves over the open reach interval
and the seed label set.  This is the Borel ray-cluster parametrization of the
seed data (main.tex:1173-1185). -/
def seedTubeImage (A : F.CalibratedLevelSeedPatch u) : Set M :=
  tubeImage (Ioo (-A.reach) A.reach) A.labels A.curve

/-- **Every point of a seed tube image is in the calibrated interior.**  The seed
clock at the two reach endpoints plus the complete-curve cylinder theorem give
two-sided calibration at every interior time, so no openness is needed here. -/
theorem seedTubeImage_subset_chartInterior (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    seedTubeImage A ⊆ chartInterior F u := by
  letI : MetricSpace M := F.metricSpace
  rintro x ⟨⟨r, w⟩, ⟨hr, hw⟩, rfl⟩
  have horder : -A.reach ≤ A.reach := by linarith [A.reach_pos]
  have hwin := hF.calibrated_window_of_complete_unit_endpoints
    (u := u) hu (c := A.curve w) (a := -A.reach) (b := A.reach)
    (q := (A.level : ℝ))
    (A.complete w hw) (A.unit w hw)
    (A.clock w hw (-A.reach) (left_mem_Icc.mpr horder))
    (A.clock w hw A.reach (right_mem_Icc.mpr horder))
  change A.curve w r ∈ OTSelector.Geometry.calibratedInterior u
  exact hwin.2.2 r hr

/-! ## The calibrated tube instantiated from a population seed -/

/-- **The paper's calibrated tube from a population seed.**  All fields of
|CalibratedTube| are discharged from the constructed seed except the openness of
the tube image, which is the seed's genuine missing geometric input; the tube is
stated for the shifted potential |u - level| so that the seed clock is the tube
clock. -/
def seedCalibratedTube (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (himg : IsOpen (seedTubeImage A)) :
    CalibratedTube F (fun x : M => u x - (A.level : ℝ)) A.covector.ker where
  J := Ioo (-A.reach) A.reach
  J_open := isOpen_Ioo
  J_nonempty := ⟨0, by constructor <;> linarith [A.reach_pos]⟩
  J_convex := by
    intro r hr r' hr' t ht
    exact ⟨lt_of_lt_of_le hr.1 ht.1, lt_of_le_of_lt ht.2 hr'.2⟩
  base := A.labels
  base_nonempty := by
    obtain ⟨P⟩ := A.c11_presentation
    refine ⟨0, ?_⟩
    rw [P.labels_eq]
    exact ⟨P.zero_mem, P.center_mem⟩
  curve := A.curve
  image_open := himg
  curve_contMDiff := fun w hw =>
    (hF.contMDiffOn_of_isEulerLagrangeOn (A.complete w hw)).of_le (by simp)
  unit_speed := fun w hw t => A.unit w hw t
  clock := by
    intro w hw r hr
    have h := A.clock w hw r (Ioo_subset_Icc_self hr)
    show u (A.curve w r) - (A.level : ℝ) = r
    linarith

/-- **A population seed with an open tube image closes the endgame input.** -/
theorem interior_nonempty_of_seed_tube_open (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (seedTubeImage A)) :
    (interior (chartInterior F u)).Nonempty := by
  letI : MetricSpace M := F.metricSpace
  have hu' : LipschitzWith 1 (fun x : M => u x - (A.level : ℝ)) := by
    intro x y
    simpa only [edist_dist, Real.dist_eq, sub_sub_sub_cancel_right] using hu x y
  have hmain :
      (interior (chartInterior F (fun x : M => u x - (A.level : ℝ)))).Nonempty :=
    (seedCalibratedTube A hF himg).interior_nonempty hu'
  have hchart :
      chartInterior F (fun x : M => u x - (A.level : ℝ)) = chartInterior F u := by
    show OTSelector.Geometry.calibratedInterior (fun x : M => u x - (A.level : ℝ)) =
      OTSelector.Geometry.calibratedInterior u
    exact calibratedInterior_sub_const u (A.level : ℝ)
  rwa [hchart] at hmain

/-- **The weakest explicit form of the missing geometric input**: a nonempty open
piece of one population seed's tube image already forces the endgame input. -/
theorem interior_nonempty_of_seed_open_piece (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {O : Set M} (hO : IsOpen O) (hOne : O.Nonempty)
    (hOsub : O ⊆ seedTubeImage A) :
    (interior (chartInterior F u)).Nonempty :=
  Set.Nonempty.mono
    (interior_maximal (hOsub.trans (seedTubeImage_subset_chartInterior A hF hu)) hO) hOne

/-! ## Window form and the a.e.-to-exact upgrade -/

/-- The tube image of a calibrated window seed. -/
def windowSeedTubeImage (P : F.CalibratedSeedWindow u) : Set M :=
  seedTubeImage P.seed

/-- **The paper's calibrated tube from a window seed.** -/
def windowSeedCalibratedTube (P : F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (himg : IsOpen (windowSeedTubeImage P)) :
    CalibratedTube F (fun x : M => u x - (P.seed.level : ℝ)) P.seed.covector.ker :=
  seedCalibratedTube P.seed hF himg

/-- Every point of a window seed's tube image is calibrated interior. -/
theorem windowSeedTubeImage_subset_chartInterior (P : F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u) :
    windowSeedTubeImage P ⊆ chartInterior F u :=
  seedTubeImage_subset_chartInterior P.seed hF hu

/-- **A window seed with an open tube image closes the endgame input.** -/
theorem interior_nonempty_of_window_tube_open (P : F.CalibratedSeedWindow u)
    (hF : F.IsSmoothStronglyConvex)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (windowSeedTubeImage P)) :
    (interior (chartInterior F u)).Nonempty :=
  interior_nonempty_of_seed_tube_open P.seed hF hu himg

/-- **Open-good a.e. window producer from an open seed tube image.** -/
theorem exists_openGood_windowChartDataAe_of_seed_tube_open
    (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (seedTubeImage A)) (μ : Measure E) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u)
      (κ : ∀ j, Measure (P j).seed.covector.ker)
      (W : WindowChartDataAe (F := F) (u := u) κ μ),
      (∀ j, IsOpen ((W.chartData j).good)) ∧
        (∀ j, (W.chartData j).σ 0 ∈ (W.chartData j).good) :=
  exists_openGood_windowChartDataAe_of_interior_nonempty hF hcomplete hu
    (interior_nonempty_of_seed_tube_open A hF hu himg) μ

/-- **Level-seed patches from an open seed tube image.** -/
theorem exists_levelSeedPatches_of_seed_tube_open
    (A : F.CalibratedLevelSeedPatch u)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (himg : IsOpen (seedTubeImage A)) :
    ∃ (P : ℕ → F.CalibratedSeedWindow u) (W : WindowChartData P),
      ∀ j, ∃ (A' : F.CalibratedLevelSeedPatch u)
          (e : A'.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
        A'.openLabels = e ⁻¹' (W.chartData j).V ∧
          A'.labels = e ⁻¹' ((W.chartData j).V ∩
            (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
            (∀ w t, A'.curve w t =
              (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
              A'.level = (W.chartData j).q :=
  exists_levelSeedPatches_of_interior_nonempty hF hcomplete hu
    (interior_nonempty_of_seed_tube_open A hF hu himg)

end OTSelector.Reconstruction
