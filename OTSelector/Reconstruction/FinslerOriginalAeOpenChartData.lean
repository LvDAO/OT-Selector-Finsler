import OTSelector.Reconstruction.FinslerOriginalWindowChartAe
import OTSelector.Reconstruction.FinslerOriginalRefinementGeometry

/-!
# A.e. C1,1 potential core and the open-domain chart datum

Task-197 produced the paper-faithful *almost-everywhere* chart and window data
(|CoreSectionChartDataAe|, |WindowChartDataAe|): the potential, partner, curve
and label data hold on a full-measure Borel subset |good| of a Borel chart
domain |U|.  Task-201 showed that the frozen-core lane consumes only that a.e.
data.  The remaining pointwise consumers are the level-seed constructor
|exists_levelSeedPatch_of_chartData| and the closed-ball constructor
|exists_chartData_and_core_of_ballCore|; both require the exact
|CoreSectionChartData| on an open chart domain.

This file attacks the a.e.-to-open transfer.  The results are:

1. **The a.e. C1,1 potential core.**  From the a.e. datum the potential is C1
   on |good| (|contDiffOn_potential|), its derivative is globally |L|-Lipschitz
   on |good| (|lipschitzOnWith_fderiv_potential|, i.e. C1,1), and it satisfies
   the derivative identity within |good| (|hasFDerivWithinAt_potential|).  So
   the C1,1 potential core is *derived* from the a.e. datum; it is not assumed.

2. **The exact chart datum on any open subset of the good set.**  If |O| is
   open, |O ⊆ good| and |σ 0 ∈ O|, then restricting the a.e. datum to |O|
   (and shrinking the label set |V| to |V ∩ σ⁻¹'O|) gives the *exact*
   |CoreSectionChartData| with chart domain |O|: the potential,
   Euler--Lagrange curve, momentum, partner and label data all hold pointwise
   on |O|.  This is |CoreSectionChartDataAe.toCoreSectionChartDataOn|, with the
   special case |O = good| in |toCoreSectionChartData|.

3. **The level-seed constructor from a.e. data.**  Consequently, for every
   compact core |K ⊆ good| containing the section point, the level-seed
   constructor applies: there is a calibrated level-seed patch whose label set
   is the preimage of |V ∩ σ⁻¹'K| and whose curves are the chart curves
   (|CoreSectionChartDataAe.exists_levelSeedPatch|).  Applied window by window
   to |WindowChartDataAe| this yields a level-seed patch for every window
   (|WindowChartDataAe.exists_levelSeedPatches|); the patch fields are
   constructed by choice through the constructor, not assumed.

4. **The exact window producer from a.e. data + pointwise realization.**
   |WindowChartDataAe.toWindowChartData| assembles the exact producer once the
   label and curve realization is pointwise; the a.e. producer itself gives
   realization only for the label law.

5. **The natural sufficient condition for openness.**  If the exceptional set
   |U \ good| is closed (for instance when the a.e. identities are equalities of
   continuous functions), then |good| is open
   (|isOpen_good_of_isOpen_U_of_isClosed_sdiff|).  Conversely exact data is the
   degenerate case |good = U| open (|CoreSectionChartData.isOpen_good_toAe|).

## Exact remaining sub-gap

The a.e.-to-open transfer for the *chart datum* is therefore reduced to one
topological hypothesis: the full-measure Borel set |good| must be open (or the
compact parent core must lie inside an open |O ⊆ good|).  The a.e. ray-cluster
package does not by itself supply such an open set around the compact core: the
cluster images are Borel full-measure sets, and no open calibrated tube is
available (task-197 established this).  Two fields are also genuinely
pointwise-only and cannot be continued from a.e. data by the continuity
argument that handles the potential:

* the Euler--Lagrange curve family |Γ|: continuation from dense data would need
  uniform convergence/compactness of the curve family on the exceptional set,
  which is not available;
* the two-sided partner data: it is an existential condition at a fixed
  distance |δ|, and the witnesses do not converge (the manifold |M| is not
  compact).

They are supplied pointwise by the closed-ball construction
(|BallCorePotentialData|), which remains the pointwise-only input of
|exists_chartData_and_core_of_ballCore|.
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

universe uE uM

variable {E : Type uE} {M : Type uM}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {μ : Measure E}

/-! ## The a.e. C1,1 potential core -/

/-- **The potential is C1 on the full-measure good set.**  The chart expression
of the potential agrees with the globally C1 function |G| on |good|, hence is C1
there. -/
theorem CoreSectionChartDataAe.contDiffOn_potential
    (A : CoreSectionChartDataAe (F := F) (u := u) μ) :
    ContDiffOn ℝ 1 (u ∘ (extChartAt 𝓘(ℝ, E) A.old).symm) A.good :=
  A.G_contDiff.contDiffOn.congr fun x hx => (A.val_good hx).symm

/-- **The a.e. C1,1 potential core.**  The derivative of the chart expression of
the potential is |L|-Lipschitz on |good|, because it agrees there with the
globally |L|-Lipschitz derivative of |G|.  Together with |contDiffOn_potential|
this says that the C1,1 potential core holds on the full-measure Borel set,
derived from the a.e. datum. -/
theorem CoreSectionChartDataAe.lipschitzOnWith_fderiv_potential
    (A : CoreSectionChartDataAe (F := F) (u := u) μ) :
    LipschitzOnWith A.L (fderiv ℝ (u ∘ (extChartAt 𝓘(ℝ, E) A.old).symm)) A.good :=
  fun x hx y hy => by
    rw [← A.match_good hx, ← A.match_good hy]
    exact A.G_lip x y

/-- **The derivative identity holds within the good set.** -/
theorem CoreSectionChartDataAe.hasFDerivWithinAt_potential
    (A : CoreSectionChartDataAe (F := F) (u := u) μ) :
    ∀ y ∈ A.good,
      HasFDerivWithinAt (u ∘ (extChartAt 𝓘(ℝ, E) A.old).symm)
        (fderiv ℝ A.G y) A.good y :=
  fun y hy => (A.actual_good y hy).hasFDerivWithinAt

/-! ## When is the full-measure set open? -/

/-- **Openness from a closed exceptional set.**  If the chart domain is open and
the exceptional set |U \ good| is closed --- the situation whenever the a.e.
identities are equalities of continuous functions --- then the full-measure set
|good| is open.  This is the natural sufficient condition for the open-domain
transfer below. -/
theorem CoreSectionChartDataAe.isOpen_good_of_isOpen_U_of_isClosed_sdiff
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hU : IsOpen A.U) (hex : IsClosed (A.U \ A.good)) : IsOpen A.good := by
  have h : A.U \ (A.U \ A.good) = A.good := by
    ext x
    constructor
    · rintro ⟨hxU, hxn⟩
      by_contra hx
      exact hxn ⟨hxU, hx⟩
    · intro hx
      exact ⟨A.good_subset hx, fun h => h.2 hx⟩
  rw [← h]
  exact hU.sdiff hex

/-- **Exact data is the degenerate open case.**  The a.e. producer of task-197
associated with an exact chart datum has |good = U|, which is open.  Hence the
openness hypothesis of the transfer below is exactly the gap between the a.e.
producer and the exact producer. -/
theorem CoreSectionChartData.isOpen_good_toAe
    (C : CoreSectionChartData (F := F) (u := u)) (μ : Measure E) :
    IsOpen (C.toAe μ).good := by
  rw [CoreSectionChartData.toAe_good]
  exact C.U_open

/-! ## The exact chart datum on an open subset of the good set -/

/-- **A.e. chart datum restricted to an open subset of the good set.**  If |O| is
open, |O ⊆ good| and the section point lies in |O|, then the a.e. datum restricts
to an *exact* |CoreSectionChartData| with chart domain |O| and label set
|V ∩ σ⁻¹'O|.  All pointwise fields hold because they hold on |good|; the label
set is shrunk so that the section maps into the chart domain. -/
def CoreSectionChartDataAe.toCoreSectionChartDataOn
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    CoreSectionChartData (F := F) (u := u) where
  old := A.old
  G := A.G
  L := A.L
  U := O
  U_open := hO
  U_target := fun x hx => A.U_target (A.good_subset (hO_sub hx))
  Γ := A.Γ
  δ := A.δ
  δ_pos := A.δ_pos
  p := A.p
  V := A.V ∩ A.σ ⁻¹' O
  V_open := A.σ_contDiff.continuousOn.isOpen_inter_preimage A.V_open hO
  σ := A.σ
  G_contDiff := A.G_contDiff
  G_lip := A.G_lip
  match_U := by intro x hx; exact A.match_good (hO_sub hx)
  val_U := by intro x hx; exact A.val_good (hO_sub hx)
  actual_U := fun y hy => A.actual_good y (hO_sub hy)
  EL_U := fun x hx => A.EL_good x (hO_sub hx)
  init_U := fun x hx => A.init_good x (hO_sub hx)
  mom_U := fun x hx => A.mom_good x (hO_sub hx)
  partners_U := fun x hx => A.partners_good x (hO_sub hx)
  σ_contDiff := A.σ_contDiff.mono Set.inter_subset_left
  σ_mapsTo := fun w hw => hw.2
  σ_inj := by
    intro x hx y hy h
    exact A.σ_inj hx.1 hy.1 h
  dim := A.dim
  zero_V := ⟨A.zero_V, hσ0⟩
  covector_eq := A.covector_eq
  σ_deriv := A.σ_deriv
  σ_imm := fun w hw => A.σ_imm w hw.1
  q := A.q
  G_level := fun w hw => A.G_level w hw.1

/-- **A.e. chart datum as an exact chart datum on the good set** (the case
|O = good| of |toCoreSectionChartDataOn|): the topological hypothesis is exactly
that the full-measure set is open. -/
def CoreSectionChartDataAe.toCoreSectionChartData
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good) :
    CoreSectionChartData (F := F) (u := u) :=
  A.toCoreSectionChartDataOn A.good hopen (subset_refl _) hσ0

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartData_U
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good) :
    (A.toCoreSectionChartData hopen hσ0).U = A.good := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartData_V
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good) :
    (A.toCoreSectionChartData hopen hσ0).V = A.V ∩ A.σ ⁻¹' A.good := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartData_σ
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good) :
    (A.toCoreSectionChartData hopen hσ0).σ = A.σ := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartData_Γ
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good) :
    (A.toCoreSectionChartData hopen hσ0).Γ = A.Γ := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartData_p
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good) :
    (A.toCoreSectionChartData hopen hσ0).p = A.p := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartData_q
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good) :
    (A.toCoreSectionChartData hopen hσ0).q = A.q := rfl

/-- **Removing the redundant restriction to the good set.**  When a compact core
|K| is contained in |good|, the label set |V ∩ σ⁻¹'good ∩ σ⁻¹'K| of the
open-domain transfer agrees with |V ∩ σ⁻¹'K|. -/
theorem CoreSectionChartDataAe.V_inter_preimage_of_subset
    (A : CoreSectionChartDataAe (F := F) (u := u) μ) {K : Set E}
    (hK : K ⊆ A.good) :
    A.V ∩ A.σ ⁻¹' A.good ∩ A.σ ⁻¹' K = A.V ∩ A.σ ⁻¹' K := by
  rw [Set.inter_assoc]
  exact congrArg (fun T => A.V ∩ T)
    (Set.inter_eq_right.mpr (Set.preimage_mono hK))

/-! Projection bookkeeping for the open-domain transfer. -/

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_U
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).U = O := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_V
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).V = A.V ∩ A.σ ⁻¹' O := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_σ
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).σ = A.σ := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_Γ
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).Γ = A.Γ := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_p
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).p = A.p := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_q
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).q = A.q := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_G
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).G = A.G := rfl

@[simp] theorem CoreSectionChartDataAe.toCoreSectionChartDataOn_old
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (O : Set E) (hO : IsOpen O) (hO_sub : O ⊆ A.good) (hσ0 : A.σ 0 ∈ O) :
    (A.toCoreSectionChartDataOn O hO hO_sub hσ0).old = A.old := rfl

/-! ## The level-seed patch from a.e. data -/

/-- **The level-seed constructor from a.e. chart data.**  For every compact core
|K| inside the full-measure set (with the section point in |K|) the level-seed
constructor applies to the exact chart datum obtained by restricting to |good|,
producing a calibrated level-seed patch.  The patch fields --- open label set,
label set, curve family and level --- are all constructed (by choice inside the
constructor) from the a.e. datum; none is assumed. -/
theorem CoreSectionChartDataAe.exists_levelSeedPatch
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (A : CoreSectionChartDataAe (F := F) (u := u) μ)
    (hopen : IsOpen A.good) (hσ0 : A.σ 0 ∈ A.good)
    {K : Set E} (hK : IsCompact K) (hKg : K ⊆ A.good) (hc : A.σ 0 ∈ K) :
    ∃ (A' : F.CalibratedLevelSeedPatch u) (e : A'.covector.ker ≃L[ℝ] A.p.ker),
      A'.openLabels = e ⁻¹' (A.V ∩ A.σ ⁻¹' A.good) ∧
      A'.labels = e ⁻¹' (A.V ∩ A.σ ⁻¹' K) ∧
      (∀ w t, A'.curve w t = A.Γ (A.σ (e w)) t) ∧ A'.level = A.q := by
  obtain ⟨A', e, h1, h2, h3, h4⟩ :=
    exists_levelSeedPatch_of_chartData (F := F) (u := u) hF hcomplete hu
      (A.toCoreSectionChartData hopen hσ0) hK
      (by rw [CoreSectionChartDataAe.toCoreSectionChartData_U]; exact hKg)
      (by rw [CoreSectionChartDataAe.toCoreSectionChartData_σ]; exact hc)
  refine ⟨A', e, ?_, ?_, ?_, ?_⟩
  · rw [CoreSectionChartDataAe.toCoreSectionChartData_V] at h1
    exact h1
  · rw [h2]
    congr 1
    exact CoreSectionChartDataAe.V_inter_preimage_of_subset A hKg
  · rw [CoreSectionChartDataAe.toCoreSectionChartData_Γ,
      CoreSectionChartDataAe.toCoreSectionChartData_σ] at h3
    exact h3
  · rw [CoreSectionChartDataAe.toCoreSectionChartData_q] at h4
    exact h4

/-! ## Window by window -/

/-- **A level-seed patch for every window, from a.e. window data.**  The compact
parent core of each window lies in the window's full-measure set and contains
the section point; hence the a.e. window producer yields a calibrated level-seed
patch for every window as soon as each full-measure set is open.  The label set
is the preimage of |V ∩ σ⁻¹'parentCore| (the redundant restriction to |good| is
removed since the compact core lies in |good|). -/
theorem WindowChartDataAe.exists_levelSeedPatches
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : letI : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    {P : ℕ → F.CalibratedSeedWindow u}
    {κ : ∀ j, Measure (P j).seed.covector.ker}
    (W : WindowChartDataAe (F := F) (u := u) κ μ)
    (hopen : ∀ j, IsOpen (W.chartData j).good) :
    ∀ j, ∃ (A' : F.CalibratedLevelSeedPatch u)
      (e : A'.covector.ker ≃L[ℝ] (W.chartData j).p.ker),
      A'.openLabels =
        e ⁻¹' ((W.chartData j).V ∩ (W.chartData j).σ ⁻¹' (W.chartData j).good) ∧
      A'.labels =
        e ⁻¹' ((W.chartData j).V ∩ (W.chartData j).σ ⁻¹' (W.parentCore j)) ∧
      (∀ w t, A'.curve w t = (W.chartData j).Γ ((W.chartData j).σ (e w)) t) ∧
      A'.level = (W.chartData j).q := by
  intro j
  have hσ0 : (W.chartData j).σ 0 ∈ (W.chartData j).good :=
    W.parentCore_subset_good j (W.parentCore_center j)
  obtain ⟨A', e, h1, h2, h3, h4⟩ :=
    CoreSectionChartDataAe.exists_levelSeedPatch (F := F) (u := u) hF hcomplete hu
      (W.chartData j) (hopen j) hσ0 (W.parentCore_compact j)
      (W.parentCore_subset_good j) (W.parentCore_center j)
  exact ⟨A', e, h1, h2, h3, h4⟩

/-- **The exact window producer from a.e. data and pointwise realization.**
Once the label and curve realization is pointwise for the window label, the a.e.
window producer upgrades to the exact |WindowChartData|: the chart data are
obtained from the open-domain transfer, and the compact parent cores are
unchanged. -/
def WindowChartDataAe.toWindowChartData
    {P : ℕ → F.CalibratedSeedWindow u}
    {κ : ∀ j, Measure (P j).seed.covector.ker}
    (W : WindowChartDataAe (F := F) (u := u) κ μ)
    (hopen : ∀ j, IsOpen (W.chartData j).good)
    (hlabels : ∀ j, (P j).seed.labels =
      (W.parentEquiv j) ⁻¹'
        ((W.chartData j).V ∩ (W.chartData j).σ ⁻¹' (W.parentCore j)))
    (hcurves : ∀ j (w : (P j).seed.covector.ker) (t : ℝ),
      (P j).seed.curve w t =
        (W.chartData j).Γ ((W.chartData j).σ ((W.parentEquiv j) w)) t) :
    WindowChartData P where
  chartData := fun j =>
    (W.chartData j).toCoreSectionChartData (hopen j)
      (W.parentCore_subset_good j (W.parentCore_center j))
  parentCore := W.parentCore
  parentCore_compact := W.parentCore_compact
  parentCore_subset := fun j => W.parentCore_subset_good j
  parentCore_center := W.parentCore_center
  parentEquiv := W.parentEquiv
  parent_labels := fun j => by
    rw [hlabels j]
    congr 1
    rw [CoreSectionChartDataAe.toCoreSectionChartData_V,
      CoreSectionChartDataAe.toCoreSectionChartData_σ]
    exact (CoreSectionChartDataAe.V_inter_preimage_of_subset (W.chartData j)
      (W.parentCore_subset_good j)).symm
  parent_curves := hcurves

end OTSelector.Reconstruction
