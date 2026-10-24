import OTSelector.Reconstruction.FinslerOriginalWindowChartData
import OTSelector.Reconstruction.FinslerOriginalReadoutLipschitzFromAtlas
import OTSelector.Reconstruction.FinslerOriginalCalibratedInteriorHypothesis
import OTSelector.Geometry.Finsler.Geodesic.ConstantSpeedDistance

/-!
# Almost-everywhere window chart data: the paper-faithful producer

Task-192 showed that the paper (|main.tex|) does not assume nonempty manifold
interior of the calibrated interior |T_phi^o|: Theorem 1.1 assumes only the base
Finsler data and states explicitly that no raywise interior-support condition is
assumed, and |T_phi^o| is introduced as a Borel set of full |mu| and |nu|
measure.  The general argument works with almost-everywhere ray geometry (the
Assouline ray clusters of |main.tex|, around line 1136: injective locally
Lipschitz parametrisations on Borel domains with compact transverse bases, up to
null sets), never with an open smooth foliation.

This file provides the corresponding producer interface and its consumer
statement.

## Contents

1. |CoreSectionChartDataAe|: the almost-everywhere chart datum.  It carries the
   same chart functions as |CoreSectionChartData| (potential |G|, Euler--Lagrange
   family |Gamma|, section |sigma|, covector |p|, level |q|), but the chart
   domain |U| is only a Borel set (|U_measurable|, no open set) and the
   potential/partner/curve data hold only on a full-measure Borel subset
   |good : Set E|, |mu (U \ good) = 0|.
2. |WindowChartDataAe|: the almost-everywhere window producer.  Compact parent
   cores sit inside the full-measure set |good| (the paper's compact transverse
   base), and the window realization of the labels and curves is only required
   almost everywhere for the window label laws |kappa|.
3. |CoreSectionChartData.toAe| and |WindowChartData.toAe|: the exact producer is
   the degenerate case |good = U| of the a.e. producer, so the a.e. interface is
   a faithful weakening of |WindowChartData|.
4. Null-set consumer lemmas: |restrict_good_eq| (the exceptional set contributes
   zero to the chart measure), |windowLabelLaw_eq_chart| and
   |windowReadout_eq_chart| (the frozen pressure readout integrates against the
   label law, and replacing the window curves by their chart realization on the
   full-measure set leaves the readout law unchanged).  This is exactly the
   sense in which "the null set contributes 0" for the frozen readout.
5. |AeRayClusterData|: the paper's a.e. ray-cluster package as a structure
   (Borel ray domain, calibrated unit-speed Euler--Lagrange rays, clock and
   locally minimizing short segments on a full-measure subset, no open set), the
   a.e. version of the calibrated tube of
   |FinslerOriginalCalibratedInteriorHypothesis|; the exact calibrated tube
   embeds into it (|CalibratedRayTube.toAeRayCluster|).  Every good cluster
   point is a calibrated interior point (|good_subset_chartInterior|), hence the
   calibrated interior is full-measure inside the cluster domain
   (|chartInterior_ae_full|): the a.e. ray-cluster data supplies exactly the
   a.e. interiority that the paper's general argument uses.

## Exact remaining sub-gap

The paper-faithful a.e. producer cannot be turned into the exact producer
|WindowChartData|, because the exact chart datum requires the pointwise
potential/partner data on an *open* chart domain (the input of
|exists_levelSeedPatch_of_chartData| and of the frozen core entry bound), while
|CoreSectionChartDataAe| only supplies it on a full-measure Borel set.  Closing
the unconditional producer therefore requires either (a) an a.e. version of the
C1,1 potential-core construction and of the level-seed constructor, or (b) an
argument upgrading the a.e. ray clusters to one open calibrated tube.  Neither
the paper (which cites Assouline's ray-cluster package) nor this repository
(currently) contains such a construction; the frozen pressure readout itself,
however, only consumes the a.e. data by items 4 above, so the a.e. producer
suffices for that readout by construction.
-/
open Set Function Metric Manifold OTSelector.Geometry MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe uE uM uZ

variable {E : Type uE} {M : Type uM}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-! ## The almost-everywhere chart datum -/

/-- **Almost-everywhere chart datum.**  The chart functions are the same as in
|CoreSectionChartData|; the chart domain |U| is only required to be a Borel set
(no open set), and the potential, partner and curve data hold on a
full-measure Borel subset |good| of |U|. -/
structure CoreSectionChartDataAe (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (μ : Measure E) where
  old : M
  G : E → ℝ
  L : ℝ≥0
  /-- The Borel chart domain. -/
  U : Set E
  U_measurable : MeasurableSet U
  U_target : U ⊆ (extChartAt 𝓘(ℝ, E) old).target
  /-- The full-measure Borel subset carrying the pointwise data. -/
  good : Set E
  good_measurable : MeasurableSet good
  good_subset : good ⊆ U
  good_null : μ (U \ good) = 0
  Γ : E → ℝ → M
  δ : ℝ
  δ_pos : 0 < δ
  p : E →L[ℝ] ℝ
  V : Set p.ker
  V_open : IsOpen V
  σ : p.ker → E
  G_contDiff : ContDiff ℝ 1 G
  G_lip : LipschitzWith L (fderiv ℝ G)
  match_good : EqOn (fderiv ℝ G) (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) old).symm)) good
  val_good : EqOn G (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) good
  actual_good : ∀ y ∈ good,
    HasFDerivAt (u ∘ (extChartAt 𝓘(ℝ, E) old).symm) (fderiv ℝ G y) y
  EL_good : ∀ x ∈ good, F.IsEulerLagrangeOn (Γ x) univ
  init_good : ∀ x ∈ good, Γ x 0 = (extChartAt 𝓘(ℝ, E) old).symm x
  mom_good : ∀ x ∈ good, F.chartMomentumFamily old Γ (x, 0) = (x, fderiv ℝ G x)
  partners_good : letI : MetricSpace M := F.metricSpace; ∀ x ∈ good, ∃ a b : M,
    dist a ((extChartAt 𝓘(ℝ, E) old).symm x) = δ ∧
    u ((extChartAt 𝓘(ℝ, E) old).symm x) - u a = δ ∧
    dist ((extChartAt 𝓘(ℝ, E) old).symm x) b = δ ∧
    u b - u ((extChartAt 𝓘(ℝ, E) old).symm x) = δ
  σ_contDiff : ContDiffOn ℝ 1 σ V
  σ_mapsTo : MapsTo σ V U
  σ_inj : InjOn σ V
  dim : Module.finrank ℝ p.ker + 1 = Module.finrank ℝ E
  zero_V : (0 : p.ker) ∈ V
  covector_eq : p = fderiv ℝ G (σ 0)
  σ_deriv : HasFDerivAt σ p.ker.subtypeL 0
  σ_imm : ∀ w ∈ V, Function.Injective (fderiv ℝ σ w)
  q : ℚ
  G_level : ∀ w ∈ V, G (σ w) = (q : ℝ)

/-- **The exceptional set contributes zero to the chart measure.**  On the
full-measure Borel subset the chart datum carries the whole chart measure. -/
theorem CoreSectionChartDataAe.restrict_good_eq
    (A : CoreSectionChartDataAe (F := F) (u := u) μ) :
    μ.restrict A.good = μ.restrict A.U := by
  refine MeasureTheory.Measure.restrict_congr_set ?_
  rw [MeasureTheory.ae_eq_set]
  exact ⟨by rw [Set.sdiff_eq_empty.mpr A.good_subset]; simp, A.good_null⟩

/-- **Null-set form of the chart integral.**  Any integral over the ambient chart
domain equals the integral over the full-measure Borel subset. -/
theorem CoreSectionChartDataAe.integral_restrict_good_eq
    (A : CoreSectionChartDataAe (F := F) (u := u) μ) (f : E → ℝ) :
    ∫ x in A.good, f x ∂μ = ∫ x in A.U, f x ∂μ := by
  rw [A.restrict_good_eq]

/-! ## The almost-everywhere window producer -/

/-- **Almost-everywhere window chart producer.**  The per-window chart datum is
only an a.e. datum (Borel domain, full-measure good subset); the compact parent
core is contained in the full-measure subset (the paper's compact transverse
base); and the window realization of the labels and curves is only required
almost everywhere for the window label laws |kappa|. -/
structure WindowChartDataAe {P : ℕ → F.CalibratedSeedWindow u}
    (κ : ∀ j, Measure (P j).seed.covector.ker) (μ : Measure E) where
  chartData : (j : ℕ) → CoreSectionChartDataAe (F := F) (u := u) μ
  parentCore : (j : ℕ) → Set E
  parentCore_compact : ∀ j, IsCompact (parentCore j)
  /-- The compact parent core sits inside the full-measure Borel subset. -/
  parentCore_subset_good : ∀ j, parentCore j ⊆ (chartData j).good
  parentCore_center : ∀ j, (chartData j).σ 0 ∈ parentCore j
  parentEquiv : (j : ℕ) → (P j).seed.covector.ker ≃L[ℝ] (chartData j).p.ker
  /-- Label realization, almost everywhere for the window label law. -/
  parent_labels_ae : ∀ j, ∀ᵐ w ∂(κ j),
    (w ∈ (P j).seed.labels ↔
      (parentEquiv j) w ∈
        (chartData j).V ∩ (chartData j).σ ⁻¹' (parentCore j))
  /-- Curve realization, almost everywhere for the window label law. -/
  parent_curves_ae : ∀ j, ∀ᵐ w ∂(κ j), ∀ t : ℝ,
    (P j).seed.curve w t =
      (chartData j).Γ ((chartData j).σ ((parentEquiv j) w)) t

/-! ## The exact producer is the degenerate a.e. producer -/

/-- **Exact chart datum as an a.e. chart datum.**  Taking |good = U| (an open
set is Borel and has null complement) turns |CoreSectionChartData| into
|CoreSectionChartDataAe|. -/
def CoreSectionChartData.toAe (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : CoreSectionChartDataAe (F := F) (u := u) μ where
  old := C.old
  G := C.G
  L := C.L
  U := C.U
  U_measurable := C.U_open.measurableSet
  U_target := C.U_target
  good := C.U
  good_measurable := C.U_open.measurableSet
  good_subset := subset_refl _
  good_null := by simp
  Γ := C.Γ
  δ := C.δ
  δ_pos := C.δ_pos
  p := C.p
  V := C.V
  V_open := C.V_open
  σ := C.σ
  G_contDiff := C.G_contDiff
  G_lip := C.G_lip
  match_good := C.match_U
  val_good := C.val_U
  actual_good := C.actual_U
  EL_good := C.EL_U
  init_good := C.init_U
  mom_good := C.mom_U
  partners_good := C.partners_U
  σ_contDiff := C.σ_contDiff
  σ_mapsTo := C.σ_mapsTo
  σ_inj := C.σ_inj
  dim := C.dim
  zero_V := C.zero_V
  covector_eq := C.covector_eq
  σ_deriv := C.σ_deriv
  σ_imm := C.σ_imm
  q := C.q
  G_level := C.G_level

/-- Projection bookkeeping for the exact-to-a.e. chart datum conversion. -/
@[simp] theorem CoreSectionChartData.toAe_U (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).U = C.U := rfl

@[simp] theorem CoreSectionChartData.toAe_good (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).good = C.U := rfl

@[simp] theorem CoreSectionChartData.toAe_V (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).V = C.V := rfl

@[simp] theorem CoreSectionChartData.toAe_σ (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).σ = C.σ := rfl

@[simp] theorem CoreSectionChartData.toAe_p (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).p = C.p := rfl

@[simp] theorem CoreSectionChartData.toAe_Γ (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).Γ = C.Γ := rfl

@[simp] theorem CoreSectionChartData.toAe_old (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).old = C.old := rfl

@[simp] theorem CoreSectionChartData.toAe_q (C : CoreSectionChartData (F := F) (u := u))
    (μ : Measure E) : (C.toAe μ).q = C.q := rfl

/-- **Exact window producer as an a.e. window producer.**  The exact producer
|WindowChartData| satisfies the a.e. interface for every label-law family
|kappa|: exact realization is realization almost everywhere. -/
def WindowChartData.toAe {P : ℕ → F.CalibratedSeedWindow u}
    (W : WindowChartData P) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (μ : Measure E) : WindowChartDataAe (F := F) (u := u) κ μ where
  chartData := fun j => (W.chartData j).toAe μ
  parentCore := W.parentCore
  parentCore_compact := W.parentCore_compact
  parentCore_subset_good := W.parentCore_subset
  parentCore_center := W.parentCore_center
  parentEquiv := W.parentEquiv
  parent_labels_ae := fun j => Filter.Eventually.of_forall fun w => by
    rw [W.parent_labels j]
    simp
  parent_curves_ae := fun j => Filter.Eventually.of_forall fun w => W.parent_curves j w

/-! ## The frozen readout consumes only the a.e. fields -/

section Consumer

variable {Z : Type uZ} [MeasurableSpace Z]

/-- **The window label law at time zero.**  The law of the label readout
|a (curve w 0)| used by the frozen pressure readout of a window. -/
noncomputable def windowLabelLaw (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (j : ℕ) : Measure Z :=
  (κ j).map fun w => a ((P j).seed.curve w 0)

/-- **The chart-realized window label law.**  The same law with the window curves
replaced by their chart realization. -/
noncomputable def chartWindowLabelLaw {P : ℕ → F.CalibratedSeedWindow u} (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker)
    (W : WindowChartDataAe (F := F) (u := u) κ μ) (j : ℕ) : Measure Z :=
  (κ j).map fun w =>
    a ((W.chartData j).Γ ((W.chartData j).σ ((W.parentEquiv j) w)) 0)

/-- **The a.e. realization leaves the frozen readout law unchanged.**  The label
law is a pushforward of the window label law, so the null set where the curve
realization fails contributes zero. -/
theorem windowLabelLaw_eq_chart {P : ℕ → F.CalibratedSeedWindow u} (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker)
    (W : WindowChartDataAe (F := F) (u := u) κ μ) (j : ℕ) :
    windowLabelLaw P a κ j = chartWindowLabelLaw a κ W j := by
  unfold windowLabelLaw chartWindowLabelLaw
  refine MeasureTheory.Measure.map_congr ?_
  filter_upwards [W.parent_curves_ae j] with w hw
  rw [hw 0]

/-- **The frozen readout is unchanged.**  Any readout functional of the label law
gives the same value computed from the window curves and from their chart
realization: the exceptional null set contributes zero. -/
theorem windowReadout_eq_chart {P : ℕ → F.CalibratedSeedWindow u} (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker)
    (W : WindowChartDataAe (F := F) (u := u) κ μ) (j : ℕ) (readout : Z → ℝ) :
    ∫ z, readout z ∂(windowLabelLaw P a κ j) =
      ∫ z, readout z ∂(chartWindowLabelLaw a κ W j) := by
  rw [windowLabelLaw_eq_chart a κ W j]

end Consumer

/-! ## The paper's almost-everywhere ray-cluster package -/

/-- **Almost-everywhere calibrated ray-cluster data** (the paper's Assouline ray
clusters, in the metric form consumed by the reconstruction): a Borel ray
domain, a full-measure subset on which every ray is a complete unit-speed
Euler--Lagrange curve with the calibration clock and globally minimizing short
segments, and no open set.  This is the a.e. version of the calibrated tube of
|FinslerOriginalCalibratedInteriorHypothesis|. -/
structure AeRayClusterData (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    (ν : Measure M) where
  /-- The Borel set of ray parameters. -/
  domain : Set M
  domain_measurable : MeasurableSet domain
  /-- The full-measure subset carrying the calibrated ray data. -/
  good : Set M
  good_measurable : MeasurableSet good
  good_subset : good ⊆ domain
  good_null : ν (domain \ good) = 0
  curve : M → ℝ → M
  curve_zero : ∀ x ∈ good, curve x 0 = x
  el : ∀ x ∈ good, F.IsEulerLagrangeOn (curve x) univ
  radius : M → ℝ
  radius_pos : ∀ x ∈ good, 0 < radius x
  speed_one : ∀ x ∈ good, ∀ t ∈ Ioo (-(radius x)) (radius x),
    F.toFun (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (curve x) ⟨t, (1 : ℝ)⟩) = 1
  locally_minimizing : ∀ x ∈ good, ∀ a b : ℝ, a ≤ b →
    a ∈ Icc (-(radius x)) (radius x) → b ∈ Icc (-(radius x)) (radius x) →
    (letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm;
      F.lengthEDist (curve x a) (curve x b) =
        Manifold.pathELength 𝓘(ℝ, E) (curve x) a b)
  clock : ∀ x ∈ good, ∀ t ∈ Icc (-(radius x)) (radius x),
    u (curve x t) = u x + t

/-- **Every good ray-cluster point is a calibrated interior point.**  The
unit-speed globally minimizing radial segment gives the distance formula and the
clock identity gives two-sided calibrated partners.  Same computation as for the
exact calibrated tube, now only on the full-measure subset. -/
theorem AeRayClusterData.good_subset_chartInterior (H : AeRayClusterData F u ν) :
    H.good ⊆ chartInterior F u := by
  intro x hx
  letI : MetricSpace M := F.metricSpace
  letI : ∀ y : M, ENorm (TangentSpace 𝓘(ℝ, E) y) := F.enorm
  have hr : 0 < H.radius x := H.radius_pos x hx
  have hdist : ∀ t ∈ Icc (-(H.radius x)) (H.radius x),
      dist x (H.curve x t) = |t| := by
    have hform := F.dist_eq_mul_abs_sub_of_locally_minimizing
      (c := H.curve x) (t₀ := 0) (δ := H.radius x) (s := 1) hr ?_ ?_
    · intro t ht
      have h := hform t (by simpa using ht)
      rw [H.curve_zero x hx] at h
      simpa using h
    · intro t ht
      exact H.speed_one x hx t (by simpa using ht)
    · intro a ha b hb hab
      exact H.locally_minimizing x hx a b hab (by simpa using ha) (by simpa using hb)
  have hhalf : H.radius x / 2 ∈ Icc (-(H.radius x)) (H.radius x) :=
    ⟨by linarith, by linarith⟩
  have hneghalf : -(H.radius x / 2) ∈ Icc (-(H.radius x)) (H.radius x) :=
    ⟨by linarith, by linarith⟩
  have hprev : dist (H.curve x (-(H.radius x / 2))) x = H.radius x / 2 := by
    have h := hdist (-(H.radius x / 2)) hneghalf
    rw [dist_comm, h, abs_neg, abs_of_pos (by linarith : (0 : ℝ) < H.radius x / 2)]
  have hnext : dist x (H.curve x (H.radius x / 2)) = H.radius x / 2 := by
    have h := hdist (H.radius x / 2) hhalf
    rwa [abs_of_pos (by linarith : (0 : ℝ) < H.radius x / 2)] at h
  have hclock_prev : u x - u (H.curve x (-(H.radius x / 2))) = H.radius x / 2 := by
    have h := H.clock x hx (-(H.radius x / 2)) hneghalf
    linarith
  have hclock_next : u (H.curve x (H.radius x / 2)) - u x = H.radius x / 2 := by
    have h := H.clock x hx (H.radius x / 2) hhalf
    linarith
  change x ∈ OTSelector.Geometry.calibratedInterior u
  refine ⟨⟨H.curve x (-(H.radius x / 2)), ?_, ?_⟩,
    ⟨H.curve x (H.radius x / 2), ?_, ?_⟩⟩
  · exact dist_pos.mp (by rw [hprev]; linarith)
  · exact hclock_prev.trans hprev.symm
  · exact dist_pos.mp (by rw [hnext]; linarith)
  · exact hclock_next.trans hnext.symm

/-- **The calibrated interior is full-measure inside the a.e. ray domain.**  The
exceptional set where the calibrated ray data fails is null, so the calibrated
interior covers the whole cluster domain up to a null set.  This is the a.e.
interiority that the paper's general argument uses. -/
theorem AeRayClusterData.chartInterior_ae_full (H : AeRayClusterData F u ν) :
    ν (H.domain \ chartInterior F u) = 0 := by
  have hsub : H.domain \ chartInterior F u ⊆ H.domain \ H.good := by
    intro x hx
    exact ⟨hx.1, fun hxgood => hx.2 (H.good_subset_chartInterior hxgood)⟩
  have hle : ν (H.domain \ chartInterior F u) ≤ ν (H.domain \ H.good) :=
    MeasureTheory.measure_mono hsub
  exact le_antisymm (hle.trans (le_of_eq H.good_null)) (by positivity)

/-- **Two-sided calibrated partners on the good a.e. set.**  The calibrated
interior membership unwinds to explicit predecessor and successor partners. -/
theorem AeRayClusterData.exists_twoSidedPartners (H : AeRayClusterData F u ν)
    {x : M} (hx : x ∈ H.good) :
    letI : MetricSpace M := F.metricSpace
    (∃ a : M, a ≠ x ∧ u x - u a = dist a x) ∧
      (∃ b : M, x ≠ b ∧ u b - u x = dist x b) := by
  letI : MetricSpace M := F.metricSpace
  exact H.good_subset_chartInterior hx

/-- **The exact calibrated tube is an a.e. ray cluster.**  The paper's exact
calibrated tube of |FinslerOriginalCalibratedInteriorHypothesis| is the
degenerate a.e. cluster with |good = domain = region| and |nu (region \ region) =
0|. -/
def CalibratedRayTube.toAeRayCluster (H : CalibratedRayTube F u)
    (ν : Measure M) : AeRayClusterData F u ν where
  domain := H.region
  domain_measurable := H.region_open.measurableSet
  good := H.region
  good_measurable := H.region_open.measurableSet
  good_subset := subset_refl _
  good_null := by simp
  curve := H.curve
  curve_zero := H.curve_zero
  el := H.el
  radius := H.radius
  radius_pos := H.radius_pos
  speed_one := H.speed_one
  locally_minimizing := H.locally_minimizing
  clock := H.clock

end OTSelector.Reconstruction
