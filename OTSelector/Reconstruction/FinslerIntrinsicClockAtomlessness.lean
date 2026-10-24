import OTSelector.Reconstruction.FinslerIntrinsicRayCouplingMeasurable
import OTSelector.Reconstruction.FinslerScalarVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Clock atomlessness of the conditional plans

This module closes the geometric input isolated by
`FinslerIntrinsicRayCouplingMeasurable.lean`: the atomlessness, for almost
every ray label, of the two potential-clock marginals of the conditional
surface plans of the optimal face.

## What the paper assumes

`main.tex`, `prop:general-optimal-face` (:422) states that there are
*absolutely continuous probability kernels* `\alpha_z, \beta_z` in the
potential coordinate `r`, with `\mu = \int (\gamma_z)_\#\alpha_z\,\Lambda(dz)`,
`\nu = \int (\gamma_z)_\#\beta_z\,\Lambda(dz)`, and that every optimal plan is
`\pi = \int (\gamma_z\times\gamma_z)_\#\kappa_z\,\Lambda(dz)` with
`\kappa_z \in \Pi(\alpha_z,\beta_z)`.  The proof (`main.tex`:462--480) obtains
the absolute continuity from Ohta's ray-disintegration theorem: the reference
volume disintegrates as `m_{0,z} = h_z(r)\,dr`, hence the conditional
measures `f_A m_{0,z}/a(z)` are absolutely continuous in arc length; it also
records that *all assertions about a given disintegration hold for
`\Lambda`-almost every label*.

Consequently the paper supplies the a.e. absolute continuity of the clock
marginals of the conditional plans, hence (as proved below) their a.e.
atomlessness.  It does *not* supply atomlessness at every label: an exceptional
label may carry clock atoms (such plans are still optimal), and the set of good
labels need not be measurable in a way that permits a measurable replacement of
the bad conditional kernels.  This is the exact remaining sub-gap for the
pointwise hypothesis form of `rayCoupling_regularity`; we prove a concrete
counterexample (`exists_clockAbsolutelyContinuous_not_pointwise_atomless`).

## Main results

* `atomless_of_absolutelyContinuous_volume`, `clock_atomless_of_map_absolutelyContinuous`:
  absolute continuity of a clock pushforward to Lebesgue measure kills all atoms;
* `ClockAbsolutelyContinuous` (a.e. form) and `ClockAbsolutelyContinuousAll`
  (pointwise form) are the paper's absolutely continuous conditional clock
  kernels, expressed as pushforwards of the conditional plans;
* `clockAbsolutelyContinuous_of_isCoupling`: a conditional plan whose marginals
  are the two absolutely continuous conditional position laws has absolutely
  continuous clock marginals;
* `eventually_clock_atomless_of_clockAbsolutelyContinuous`: a.e. atomlessness;
* `rayCoupling_regularity_of_clockAbsolutelyContinuousAll`: the pointwise form
  feeds the regularity package `rayCoupling_regularity` of
  `FinslerIntrinsicRayCouplingMeasurable.lean`, hence the paper segment test is
  Borel (`measurableSet_paper_segmentTest_of_clockAbsolutelyContinuousAll`);
* `eventually_continuous_rayFlux_of_clockAbsolutelyContinuous` and
  `eventually_segmentMin_eq_ratFamily_of_clockAbsolutelyContinuous`: the a.e.
  form yields a.e. continuity of the conditional ray surplus and a.e. equality
  of the paper segment test with the unconditionally Borel rational segment
  family of `measurable_segmentMinRatFamily_rayCoupling`;
* `exists_finsler_clock_atomless_conditional`: for the constructed Finsler
  disintegration, every optimal plan admits a conditional coupling kernel whose
  clock marginals are a.e. atomless and whose conditional ray surplus is a.e.
  continuous in the ray parameter.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped Topology ContDiff ENNReal MeasureTheory

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section General

variable {M Z : Type*} [MeasurableSpace Z] [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- An absolutely continuous measure on `ℝ` has no atoms. -/
theorem atomless_of_absolutelyContinuous_volume {μ : Measure ℝ} (h : μ ≪ volume)
    (r : ℝ) : μ {r} = 0 :=
  h (s := {r}) Real.volume_singleton

/-- If the pushforward of a measure on pairs under a clock is absolutely
continuous, then the clock level set has zero mass. -/
theorem clock_atomless_of_map_absolutelyContinuous {γ : Measure (M × M)}
    {v : M × M → ℝ} (hv : Measurable v) (h : γ.map v ≪ volume) (r : ℝ) :
    γ {p : M × M | v p = r} = 0 := by
  have hmeas : MeasurableSet {p : M × M | v p = r} :=
    (measurableSet_singleton r).preimage hv
  have hmap : (Measure.map v γ) {r} = γ {p : M × M | v p = r} := by
    rw [Measure.map_apply hv (measurableSet_singleton r)]
    rfl
  rw [← hmap]
  exact h (s := {r}) Real.volume_singleton

/-- **The paper's absolutely continuous conditional clock kernels (a.e. form).**
For almost every ray label of the common label law, the two potential-clock
pushforwards of the conditional surface plan are absolutely continuous with
respect to Lebesgue measure.  This is the content of the absolutely continuous
kernels `\alpha_z, \beta_z` of `prop:general-optimal-face` when read through the
conditional plans `\kappa_z \in \Pi(\alpha_z,\beta_z)`. -/
def ClockAbsolutelyContinuous (κ : Kernel Z (M × M)) (u : M → ℝ) (law : Measure Z) : Prop :=
  ∀ᵐ z ∂law,
    (κ z).map (fun p : M × M => u p.1) ≪ volume ∧
    (κ z).map (fun p : M × M => u p.2) ≪ volume

/-- **Pointwise form** of the paper's absolutely continuous conditional clock
kernels: the clock pushforwards of every conditional plan are absolutely
continuous.  This pointwise strengthening is what the hypothesis form of
`rayCoupling_regularity` consumes; it is *not* a consequence of the a.e. form
(`exists_clockAbsolutelyContinuous_not_pointwise_atomless`). -/
def ClockAbsolutelyContinuousAll (κ : Kernel Z (M × M)) (u : M → ℝ) : Prop :=
  ∀ z : Z,
    (κ z).map (fun p : M × M => u p.1) ≪ volume ∧
    (κ z).map (fun p : M × M => u p.2) ≪ volume

/-- The pointwise form implies the a.e. form for any label law. -/
theorem clockAbsolutelyContinuous_of_clockAbsolutelyContinuousAll {κ : Kernel Z (M × M)}
    {u : M → ℝ} {law : Measure Z} (h : ClockAbsolutelyContinuousAll κ u) :
    ClockAbsolutelyContinuous κ u law :=
  Filter.Eventually.of_forall h

/-- **A.e. atomlessness of the conditional clock marginals.** -/
theorem eventually_clock_atomless_of_clockAbsolutelyContinuous {law : Measure Z}
    {κ : Kernel Z (M × M)} {u : M → ℝ} (hu : Measurable u)
    (h : ClockAbsolutelyContinuous κ u law) :
    ∀ᵐ z ∂law,
      (∀ r : ℝ, (κ z) {p : M × M | u p.1 = r} = 0) ∧
      (∀ r : ℝ, (κ z) {p : M × M | u p.2 = r} = 0) := by
  filter_upwards [h] with z hz
  exact ⟨fun r => clock_atomless_of_map_absolutelyContinuous (hu.comp measurable_fst) hz.1 r,
    fun r => clock_atomless_of_map_absolutelyContinuous (hu.comp measurable_snd) hz.2 r⟩

/-- **Coupling transfer.**  If a conditional plan has a.e. the two absolutely
continuous conditional position laws as marginals, then its clock marginals are
a.e. absolutely continuous. -/
theorem clockAbsolutelyContinuous_of_isCoupling {law : Measure Z}
    {κ : Kernel Z (M × M)} {α β : Z → Measure M} {u : M → ℝ} (hu : Measurable u)
    (hcouple : ∀ᵐ z ∂law, (κ z).map Prod.fst = α z ∧ (κ z).map Prod.snd = β z)
    (hα : ∀ᵐ z ∂law, (α z).map u ≪ volume)
    (hβ : ∀ᵐ z ∂law, (β z).map u ≪ volume) :
    ClockAbsolutelyContinuous κ u law := by
  filter_upwards [hcouple, hα, hβ] with z hz hαz hβz
  have h1 : (κ z).map (fun p : M × M => u p.1) = (α z).map u := by
    rw [show (fun p : M × M => u p.1) = u ∘ Prod.fst from rfl]
    rw [← Measure.map_map hu measurable_fst, hz.1]
  have h2 : (κ z).map (fun p : M × M => u p.2) = (β z).map u := by
    rw [show (fun p : M × M => u p.2) = u ∘ Prod.snd from rfl]
    rw [← Measure.map_map hu measurable_snd, hz.2]
  exact ⟨h1 ▸ hαz, h2 ▸ hβz⟩

end General

section Chain

variable {M Z : Type*} [MeasurableSpace Z] [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **A.e. continuity of the conditional ray surplus.**  A.e. absolute
continuity of the conditional clock kernels gives continuity in the ray
parameter of the conditional ray surplus at almost every label. -/
theorem eventually_continuous_rayFlux_of_clockAbsolutelyContinuous {law : Measure Z}
    {κ : Kernel Z (M × M)} [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (h : ClockAbsolutelyContinuous κ u law) :
    ∀ᵐ z ∂law, Continuous fun r : ℝ => rayFlux (rayCoupling (κ z) u) r := by
  have hmeas : Measurable u := hu.continuous.measurable
  have hatom : ∀ᵐ z ∂law, (∀ r : ℝ, (κ z) {p : M × M | u p.1 = r} = 0) ∧
      (∀ r : ℝ, (κ z) {p : M × M | u p.2 = r} = 0) :=
    eventually_clock_atomless_of_clockAbsolutelyContinuous (κ := κ) hmeas h
  filter_upwards [hatom] with z hz
  refine rayCoupling_continuous_of_atomless (κ := κ) hmeas z ?_ ?_
  · intro r
    rw [rayCoupling_atom_first hmeas z r]
    exact hz.1 r
  · intro r
    rw [rayCoupling_atom_second hmeas z r]
    exact hz.2 r

/-- **A.e. equality of the paper segment test with the rational segment
family.**  At almost every label, the paper's segment test `segmentMin` over
the compact segment coincides with the rational segment family, which is Borel
measurable in `(z, r)` without any atomlessness hypothesis
(`measurable_segmentMinRatFamily_rayCoupling`). -/
theorem eventually_segmentMin_eq_ratFamily_of_clockAbsolutelyContinuous {law : Measure Z}
    {κ : Kernel Z (M × M)} [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (h : ClockAbsolutelyContinuous κ u law) (q : ℕ → ℚ) (j : ℕ) :
    ∀ᵐ z ∂law, ∀ x : ℝ,
      segmentMin (fun r : ℝ => rayFlux (rayCoupling (κ z) u) r) x ((q j : ℚ) : ℝ)
        = segmentMinRatFamily (fun z r => rayFlux (rayCoupling (κ z) u) r) q j (z, x) := by
  have hcont := eventually_continuous_rayFlux_of_clockAbsolutelyContinuous hu h
  filter_upwards [hcont] with z hz x
  exact (segmentMinRat_eq_segmentMin hz (x := x) (y := ((q j : ℚ) : ℝ))).symm

/-- **Pointwise atomlessness of the conditional clock marginals.** -/
theorem clock_atomless_all_of_clockAbsolutelyContinuousAll {κ : Kernel Z (M × M)}
    {u : M → ℝ} (hu : Measurable u) (h : ClockAbsolutelyContinuousAll κ u) :
    (∀ z r, (κ z) {p : M × M | u p.1 = r} = 0) ∧
    (∀ z r, (κ z) {p : M × M | u p.2 = r} = 0) :=
  ⟨fun z r => clock_atomless_of_map_absolutelyContinuous (hu.comp measurable_fst) (h z).1 r,
    fun z r => clock_atomless_of_map_absolutelyContinuous (hu.comp measurable_snd) (h z).2 r⟩

/-- **The implication chain to `rayCoupling_regularity`.**  The pointwise
absolute continuity form supplies exactly the hypothesis pair consumed by the
regularity package of `FinslerIntrinsicRayCouplingMeasurable.lean`. -/
theorem rayCoupling_regularity_of_clockAbsolutelyContinuousAll {κ : Kernel Z (M × M)}
    [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (h : ClockAbsolutelyContinuousAll κ u) :
    (∀ A : Set (ℝ × ℝ), MeasurableSet A →
      Measurable fun z : Z => (rayCoupling (κ z) u A).toReal) ∧
    (∀ z, IsFiniteMeasure (rayCoupling (κ z) u)) ∧
    (∀ z r, rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = 0) ∧
    (∀ z r, rayCoupling (κ z) u {q : ℝ × ℝ | q.2 = r} = 0) ∧
    Measurable (fun p : Z × ℝ => rayFlux (rayCoupling (κ p.1) u) p.2) ∧
    ∀ z, Continuous fun r : ℝ => rayFlux (rayCoupling (κ z) u) r := by
  obtain ⟨h1, h2⟩ := clock_atomless_all_of_clockAbsolutelyContinuousAll hu.continuous.measurable h
  exact rayCoupling_regularity hu h1 h2

/-- **The paper segment test is Borel under pointwise absolute continuity.** -/
theorem measurableSet_paper_segmentTest_of_clockAbsolutelyContinuousAll
    {κ : Kernel Z (M × M)} [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (h : ClockAbsolutelyContinuousAll κ u) (q : ℕ → ℚ) (j : ℕ) :
    MeasurableSet {p : Z × ℝ |
      0 < segmentMin (fun r : ℝ => rayFlux (rayCoupling (κ p.1) u) r) p.2
        ((q j : ℚ) : ℝ)} := by
  obtain ⟨h1, h2⟩ := clock_atomless_all_of_clockAbsolutelyContinuousAll hu.continuous.measurable h
  exact measurableSet_paper_segmentTest_rayCoupling hu h1 h2 q j

end Chain

section Counterexample

/-- **The a.e. form does not give pointwise atomlessness.**  A Markov kernel
whose conditional plans are clock-atomless at almost every label may still carry
a clock atom at a null label.  Hence the pointwise hypothesis
`ClockAbsolutelyContinuousAll` is a genuine extra input, not a consequence of
the paper's a.e. absolutely continuous conditional kernels. -/
theorem exists_clockAbsolutelyContinuous_not_pointwise_atomless :
    ∃ (κ : Kernel ℝ (ℝ × ℝ)) (u : ℝ → ℝ),
      IsMarkovKernel κ ∧ ClockAbsolutelyContinuous κ u (volume : Measure ℝ) ∧
      ¬ ∀ z r : ℝ, (κ z) {p : ℝ × ℝ | u p.1 = r} = 0 := by
  let s : Set ℝ := Set.Ioo (0 : ℝ) 1
  let γ₀ : Measure (ℝ × ℝ) := (volume.restrict s).prod (volume.restrict s)
  have hvol : (volume : Measure ℝ) s = 1 := by
    rw [show s = Set.Ioo (0 : ℝ) 1 from rfl, Real.volume_Ioo]
    norm_num
  have hprob : IsProbabilityMeasure (volume.restrict (s : Set ℝ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hvol⟩
  have hprobγ : IsProbabilityMeasure γ₀ := by
    haveI := hprob
    exact Measure.prod.instIsProbabilityMeasure (volume.restrict s) (volume.restrict s)
  let κ : Kernel ℝ (ℝ × ℝ) :=
    ⟨fun z => if z = 0 then Measure.dirac ((0 : ℝ), (0 : ℝ)) else γ₀,
      Measurable.ite (measurableSet_singleton (0 : ℝ)) measurable_const measurable_const⟩
  have hκ0 : κ 0 = Measure.dirac ((0 : ℝ), (0 : ℝ)) := by
    change (if (0 : ℝ) = 0 then Measure.dirac ((0 : ℝ), (0 : ℝ)) else γ₀) = _
    rw [if_pos rfl]
  have hκne : ∀ z : ℝ, z ≠ 0 → κ z = γ₀ := by
    intro z hz
    change (if z = 0 then Measure.dirac ((0 : ℝ), (0 : ℝ)) else γ₀) = γ₀
    rw [if_neg hz]
  have hκmarkov : IsMarkovKernel κ := by
    refine ⟨fun z => ?_⟩
    by_cases hz : z = 0
    · rw [show κ z = Measure.dirac ((0 : ℝ), (0 : ℝ)) by rw [hz]; exact hκ0]
      infer_instance
    · rw [hκne z hz]
      exact hprobγ
  have hfst : γ₀.map (fun p : ℝ × ℝ => p.1) = volume.restrict s := by
    change Measure.map Prod.fst γ₀ = _
    rw [show γ₀ = (volume.restrict s).prod (volume.restrict s) from rfl,
      Measure.map_fst_prod, Measure.restrict_apply_univ, hvol, one_smul]
  have hsnd : γ₀.map (fun p : ℝ × ℝ => p.2) = volume.restrict s := by
    change Measure.map Prod.snd γ₀ = _
    rw [show γ₀ = (volume.restrict s).prod (volume.restrict s) from rfl,
      Measure.map_snd_prod, Measure.restrict_apply_univ, hvol, one_smul]
  have hac : ClockAbsolutelyContinuous κ (fun x : ℝ => x) (volume : Measure ℝ) := by
    have hne : ∀ᵐ z ∂(volume : Measure ℝ), z ≠ 0 :=
      MeasureTheory.ae_iff.mpr (by simp)
    filter_upwards [hne] with z hz
    rw [hκne z hz]
    constructor
    · rw [show (fun p : ℝ × ℝ => (fun x : ℝ => x) p.1) = fun p => p.1 from rfl, hfst]
      exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
    · rw [show (fun p : ℝ × ℝ => (fun x : ℝ => x) p.2) = fun p => p.2 from rfl, hsnd]
      exact Measure.absolutelyContinuous_of_le Measure.restrict_le_self
  refine ⟨κ, fun x => x, hκmarkov, hac, ?_⟩
  intro h
  have hbad : (κ 0) {p : ℝ × ℝ | (fun x : ℝ => x) p.1 = 0} = 0 := h 0 0
  rw [hκ0] at hbad
  have hmem : ((0 : ℝ), (0 : ℝ)) ∈ {p : ℝ × ℝ | (fun x : ℝ => x) p.1 = 0} := by simp
  rw [Measure.dirac_apply_of_mem hmem] at hbad
  exact one_ne_zero hbad

end Counterexample

section Geometric

open Manifold OTSelector.Geometry

set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : Geometry.ContinuousFinslerNorm E M}

/-- **Clock atomlessness of the conditional plans of the constructed Finsler
disintegration.**  For chartwise absolutely continuous probabilities on disjoint
compact carriers, the original Finsler disintegration produces a potential `u`
and labels `a` such that *every* optimal plan has a conditional coupling kernel
`κ` (Markov, representing the plan over the common label law) whose two
potential-clock marginals are absolutely continuous, hence atomless, at almost
every label, and whose conditional ray surplus is continuous in the ray
parameter at almost every label. -/
theorem exists_finsler_clock_atomless_conditional
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμchart : ∀ old : M,
      (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M,
      (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B) (hAB : Disjoint A B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B) :
    let _instClockAtomlessStatementMetric : MetricSpace M := F.metricSpace
    let _instClockAtomlessStatementProper : ProperSpace M :=
      F.properSpace_of_complete hcomplete
    let _instClockAtomlessStatementBorel : StandardBorelSpace M := inferInstance
    let _instClockAtomlessStatementNonempty : Nonempty M :=
      nonempty_of_isProbabilityMeasure μ
    ∃ (u : M → ℝ) (a : M → (ℚ → M)),
      LipschitzWith 1 u ∧ Measurable a ∧
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π →
        ∃ κ : Kernel (ℚ → M) (M × M),
          IsMarkovKernel κ ∧ κ ∘ₘ (μ.map a) = π ∧
          ClockAbsolutelyContinuous κ u (μ.map a) ∧
          (∀ᵐ z ∂(μ.map a),
            (∀ r : ℝ, (κ z) {p : M × M | u p.1 = r} = 0) ∧
            (∀ r : ℝ, (κ z) {p : M × M | u p.2 = r} = 0) ∧
            Continuous fun r : ℝ => rayFlux (rayCoupling (κ z) u) r) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instBorel : StandardBorelSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
  obtain ⟨u, a, hu, hN, hμN, hνN, ha, hinj, horder, hbalance, hface,
    hμI, hνI, hμjoint, hνjoint, hcond⟩ :=
    exists_finsler_scalar_volume_disintegration hF hcomplete m μ ν hμchart hνchart
      hA hB hAB hμ hν
  refine ⟨u, a, hu, ha, ?_⟩
  intro π hπ
  have hfac := (hface π).mp hπ
  let κ : Kernel (ℚ → M) (M × M) := Classical.choose hfac
  have hκspec := Classical.choose_spec hfac
  have hκmarkov : IsMarkovKernel κ := hκspec.1
  have hκcomp : κ ∘ₘ (μ.map a) = π := hκspec.2.1
  have hκcouple : ∀ᵐ z ∂(μ.map a), Vlasov.IsCoupling (κ z)
      (condDistrib id a μ z) (condDistrib id a ν z) :=
    hκspec.2.2.mono fun _ hz => hz.1
  have hκsupp := hκspec.2.2.mono fun _ hz => hz.2
  haveI : IsMarkovKernel κ := hκmarkov
  have hα : ∀ᵐ z ∂(μ.map a), (condDistrib id a μ z).map u ≪ volume :=
    hcond.mono fun z hz => hz.2.2.1
  have hβ : ∀ᵐ z ∂(μ.map a), (condDistrib id a ν z).map u ≪ volume :=
    hcond.mono fun z hz => hz.2.2.2
  have hac : ClockAbsolutelyContinuous κ u (μ.map a) :=
    clockAbsolutelyContinuous_of_isCoupling hu.continuous.measurable hκcouple hα hβ
  have hatom := eventually_clock_atomless_of_clockAbsolutelyContinuous
    (κ := κ) hu.continuous.measurable hac
  have hcont := eventually_continuous_rayFlux_of_clockAbsolutelyContinuous hu hac
  refine ⟨κ, hκmarkov, hκcomp, hac, ?_⟩
  filter_upwards [hatom, hcont] with z hz hzc
  exact ⟨hz.1, hz.2, hzc⟩

end Geometric

end OTSelector.Reconstruction
