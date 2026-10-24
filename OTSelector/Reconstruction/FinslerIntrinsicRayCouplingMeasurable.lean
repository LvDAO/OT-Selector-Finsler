import OTSelector.Transport.Calibration.ScalarRayCoupling
import OTSelector.Transport.ScalarForwardFluxRegularity
import OTSelector.Reconstruction.FinslerIntrinsicActiveSegmentMeasurable
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# Measurable coupling family and atomlessness from the geometric disintegration

This module derives, for the concrete scalar ray coupling
`rayCoupling (κ z) u = (κ z).map (fun p => (u p.1, u p.2))` of a conditional
transport plan `κ`, the hypotheses consumed by
`FinslerIntrinsicActiveSurplusRegularity.lean` (the regularity package for the
ray surplus `rayFlux`):

* (a) the family `z ↦ rayCoupling (κ z) u` has measurable real-valued total
  mass `z ↦ (rayCoupling (κ z) u A).toReal` on every measurable set `A`
  (`measurable_rayCoupling_coe_toReal`), because it is the `Kernel.map` of `κ`
  (`rayKernel`) and kernels have measurable coefficients;
* (b) every conditional scalar ray coupling is a finite (indeed probability)
  measure (`rayCoupling_isFiniteMeasure`);
* (c) atomlessness of the two scalar marginals transfers from atomlessness of
  the potential-clock marginals of `κ` (`rayCoupling_atom_first`,
  `rayCoupling_atom_second`, and the a.e. forms
  `eventually_rayCoupling_atom_first`, `eventually_rayCoupling_atom_second`).

We then prove:

* unconditional joint measurability of `(z,r) ↦ rayFlux (rayCoupling (κ z) u) r`
  from the kernel structure alone, without any atomlessness hypothesis
  (`measurable_rayFlux_kernel`), by writing the two marginal CDFs as
  parameterized kernel integrals (`Measurable.lintegral_kernel_prod_right`);
* the full regularity package `rayCoupling_regularity` collecting (a), (b),
  (c) and the joint measurability/continuity pair, and hence
* joint measurability and Borel measurability of the paper's segment test
  `segmentMin H_z(r) r_j` (`measurable_segmentMinRatFamily_rayCoupling`,
  `measurableSet_paper_segmentTest_rayCoupling`), by combining with
  `measurable_paper_segmentTest` from `FinslerIntrinsicActiveSegmentMeasurable`.

## Remaining gap

The paper's conditional-form hypotheses are a.e. statements in the whole-ray
label `z` (`∀ᵐ z ∂law`), while the segment-test measurability package of
`FinslerIntrinsicActiveSegmentMeasurable` needs the continuity of the surplus in
the ray parameter for _every_ label.  We prove the a.e. continuity statement
(`eventually_continuous_rayCoupling`) and the unconditional joint measurability;
the upgrade of the a.e. atomlessness to atomlessness at every label of a
chosen measurable section (needed to apply the paper segment test verbatim to
the canonical family) is not available from the a.e. hypotheses alone: an
exceptional null set of labels may carry atoms, so `rayFlux` may be
discontinuous there.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory Topology

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {M Z : Type*} [MeasurableSpace Z] [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-! ## The ray kernel of a conditional transport plan -/

/-- The kernel of conditional scalar ray couplings of a conditional transport
plan `κ` under the potential clock `u`. -/
def rayKernel (κ : Kernel Z (M × M)) (u : M → ℝ) : Kernel Z (ℝ × ℝ) :=
  κ.map (rayCouplingMap u)

theorem rayKernel_apply {κ : Kernel Z (M × M)} {u : M → ℝ} (hu : Measurable u) (z : Z) :
    rayKernel κ u z = rayCoupling (κ z) u := by
  rw [rayKernel, Kernel.map_apply κ (measurable_rayCouplingMap hu) z]
  rfl

theorem rayKernel_isMarkovKernel {κ : Kernel Z (M × M)} [IsMarkovKernel κ] {u : M → ℝ}
    (hu : Measurable u) : IsMarkovKernel (rayKernel κ u) :=
  Kernel.IsMarkovKernel.map κ (measurable_rayCouplingMap hu)

theorem rayCoupling_isProbabilityMeasure {κ : Kernel Z (M × M)} [IsMarkovKernel κ]
    {u : M → ℝ} (hu : Measurable u) (z : Z) : IsProbabilityMeasure (rayCoupling (κ z) u) := by
  haveI hprob : IsProbabilityMeasure (κ z) :=
    (inferInstance : IsMarkovKernel κ).isProbabilityMeasure z
  exact rayCoupling_isProbability (κ z) hu

theorem rayCoupling_isFiniteMeasure {κ : Kernel Z (M × M)} [IsMarkovKernel κ]
    {u : M → ℝ} (hu : Measurable u) (z : Z) : IsFiniteMeasure (rayCoupling (κ z) u) := by
  have hp := rayCoupling_isProbabilityMeasure (κ := κ) (u := u) hu z
  haveI := hp
  infer_instance

/-! ## (a) Measurable total mass of the coupling family -/

theorem measurable_rayCoupling_coe {κ : Kernel Z (M × M)} {u : M → ℝ} (hu : Measurable u)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    Measurable fun z : Z => rayCoupling (κ z) u A := by
  have h : Measurable fun z : Z => rayKernel κ u z A := Kernel.measurable_coe (rayKernel κ u) hA
  have heq : (fun z : Z => rayKernel κ u z A) = fun z => rayCoupling (κ z) u A := by
    funext z; rw [rayKernel_apply hu z]
  rw [heq] at h
  exact h

theorem measurable_rayCoupling_coe_toReal {κ : Kernel Z (M × M)} {u : M → ℝ} (hu : Measurable u)
    {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    Measurable fun z : Z => (rayCoupling (κ z) u A).toReal :=
  (measurable_rayCoupling_coe hu hA).ennreal_toReal

/-! ## (c) Atomlessness of the scalar marginals -/

theorem rayCoupling_atom_first {κ : Kernel Z (M × M)} {u : M → ℝ} (hu : Measurable u)
    (z : Z) (r : ℝ) :
    rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = (κ z) {p : M × M | u p.1 = r} := by
  have hmeas : MeasurableSet {q : ℝ × ℝ | q.1 = r} :=
    measurableSet_singleton r |>.preimage measurable_fst
  rw [rayCoupling, Measure.map_apply (measurable_rayCouplingMap hu) hmeas]
  rfl

theorem rayCoupling_atom_second {κ : Kernel Z (M × M)} {u : M → ℝ} (hu : Measurable u)
    (z : Z) (r : ℝ) :
    rayCoupling (κ z) u {q : ℝ × ℝ | q.2 = r} = (κ z) {p : M × M | u p.2 = r} := by
  have hmeas : MeasurableSet {q : ℝ × ℝ | q.2 = r} :=
    measurableSet_singleton r |>.preimage measurable_snd
  rw [rayCoupling, Measure.map_apply (measurable_rayCouplingMap hu) hmeas]
  rfl

theorem eventually_rayCoupling_atom_first {law : Measure Z} {κ : Kernel Z (M × M)}
    {u : M → ℝ} (hu : Measurable u)
    (h : ∀ᵐ z ∂law, ∀ r : ℝ, (κ z) {p : M × M | u p.1 = r} = 0) :
    ∀ᵐ z ∂law, ∀ r : ℝ, rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = 0 := by
  filter_upwards [h] with z hz r
  rw [rayCoupling_atom_first hu z r]
  exact hz r

theorem eventually_rayCoupling_atom_second {law : Measure Z} {κ : Kernel Z (M × M)}
    {u : M → ℝ} (hu : Measurable u)
    (h : ∀ᵐ z ∂law, ∀ r : ℝ, (κ z) {p : M × M | u p.2 = r} = 0) :
    ∀ᵐ z ∂law, ∀ r : ℝ, rayCoupling (κ z) u {q : ℝ × ℝ | q.2 = r} = 0 := by
  filter_upwards [h] with z hz r
  rw [rayCoupling_atom_second hu z r]
  exact hz r

/-! ## Continuity of the ray surplus per label -/

theorem rayCoupling_continuous_of_atomless {κ : Kernel Z (M × M)} [IsMarkovKernel κ]
    {u : M → ℝ} (hu : Measurable u) (z : Z)
    (h1 : ∀ r : ℝ, rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = 0)
    (h2 : ∀ r : ℝ, rayCoupling (κ z) u {q : ℝ × ℝ | q.2 = r} = 0) :
    Continuous fun r : ℝ => rayFlux (rayCoupling (κ z) u) r := by
  haveI := rayCoupling_isFiniteMeasure (κ := κ) hu z
  exact continuous_rayFlux _ h1 h2

theorem eventually_continuous_rayCoupling {law : Measure Z} {κ : Kernel Z (M × M)}
    [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (h1 : ∀ᵐ z ∂law, ∀ r : ℝ, (κ z) {p : M × M | u p.1 = r} = 0)
    (h2 : ∀ᵐ z ∂law, ∀ r : ℝ, (κ z) {p : M × M | u p.2 = r} = 0) :
    ∀ᵐ z ∂law, Continuous fun r : ℝ => rayFlux (rayCoupling (κ z) u) r := by
  have hu' : Measurable u := hu.continuous.measurable
  have h1' := eventually_rayCoupling_atom_first (law := law) hu' h1
  have h2' := eventually_rayCoupling_atom_second (law := law) hu' h2
  filter_upwards [h1', h2'] with z hz1 hz2
  exact rayCoupling_continuous_of_atomless hu' z hz1 hz2

/-! ## Unconditional joint measurability of the ray surplus -/

/-- **Measurability of a kernel CDF family.**  For an s-finite kernel `κ` and a
measurable function `v`, the parametrized cumulative mass
`(z, r) ↦ (κ z) {y | v y ≤ r}` is jointly measurable. -/
theorem measurable_kernel_cdf {Y : Type*} [MeasurableSpace Y] {κ : Kernel Z Y}
    [IsSFiniteKernel κ] {v : Y → ℝ} (hv : Measurable v) :
    Measurable fun p : Z × ℝ => (κ p.1) {y : Y | v y ≤ p.2} := by
  let ν : Kernel Z ℝ := κ.map v
  let ψ : Kernel (Z × ℝ) ℝ := Kernel.comap ν (fun p : Z × ℝ => p.1) measurable_fst
  have hν : ∀ z : Z, ν z = (κ z).map v := fun z => Kernel.map_apply κ hv z
  have hψ : ∀ p : Z × ℝ, ψ p = ν p.1 := fun p => Kernel.comap_apply ν measurable_fst p
  have hf : Measurable (fun q : (Z × ℝ) × ℝ => (if q.2 ≤ q.1.2 then (1 : ℝ≥0∞) else 0)) :=
    Measurable.ite (measurableSet_le (by fun_prop) (by fun_prop)) measurable_const measurable_const
  have huncurry : Function.uncurry (fun p : Z × ℝ => fun s : ℝ =>
      (if s ≤ p.2 then (1 : ℝ≥0∞) else 0))
      = fun q : (Z × ℝ) × ℝ => (if q.2 ≤ q.1.2 then (1 : ℝ≥0∞) else 0) := rfl
  have hlin : Measurable fun p : Z × ℝ =>
      ∫⁻ s, (if s ≤ p.2 then (1 : ℝ≥0∞) else 0) ∂ψ p :=
    Measurable.lintegral_kernel_prod_right (κ := ψ)
      (f := fun p : Z × ℝ => fun s : ℝ => (if s ≤ p.2 then (1 : ℝ≥0∞) else 0))
      (by rw [huncurry]; exact hf)
  have heq : (fun p : Z × ℝ => ∫⁻ s, (if s ≤ p.2 then (1 : ℝ≥0∞) else 0) ∂ψ p)
      = fun p : Z × ℝ => (κ p.1) {y : Y | v y ≤ p.2} := by
    funext p
    rw [hψ p, hν p.1]
    have hfs : Measurable fun s : ℝ => (if s ≤ p.2 then (1 : ℝ≥0∞) else 0) := by
      exact Measurable.ite (measurableSet_le measurable_id measurable_const)
        measurable_const measurable_const
    rw [lintegral_map (μ := κ p.1) (f := fun s : ℝ => (if s ≤ p.2 then (1 : ℝ≥0∞) else 0))
      hfs hv]
    have hind : (fun y : Y => (if v y ≤ p.2 then (1 : ℝ≥0∞) else 0))
        = {y : Y | v y ≤ p.2}.indicator 1 := by
      funext y
      by_cases hvy : v y ≤ p.2
      · simp [Set.indicator, hvy]
      · simp [Set.indicator, hvy]
    rw [hind, lintegral_indicator_one (measurableSet_le hv measurable_const)]
  rw [heq] at hlin
  exact hlin

/-- **Unconditional joint measurability of the ray surplus.**  For a Markov
kernel `κ` and a measurable potential clock `u`, the ray surplus
`(z, r) ↦ rayFlux (rayCoupling (κ z) u) r` is jointly Borel measurable, with no
atomlessness hypothesis. -/
theorem measurable_rayFlux_kernel {κ : Kernel Z (M × M)} [IsMarkovKernel κ] {u : M → ℝ}
    (hu : Measurable u) :
    Measurable fun p : Z × ℝ => rayFlux (rayCoupling (κ p.1) u) p.2 := by
  haveI : IsMarkovKernel (rayKernel κ u) := rayKernel_isMarkovKernel hu
  have h1 : Measurable fun p : Z × ℝ =>
      (rayKernel κ u p.1) {q : ℝ × ℝ | q.1 ≤ p.2} :=
    measurable_kernel_cdf (κ := rayKernel κ u) measurable_fst
  have h2 : Measurable fun p : Z × ℝ =>
      (rayKernel κ u p.1) {q : ℝ × ℝ | q.2 ≤ p.2} :=
    measurable_kernel_cdf (κ := rayKernel κ u) measurable_snd
  have h := h1.ennreal_toReal.sub h2.ennreal_toReal
  have h' : Measurable fun p : Z × ℝ =>
      ((rayKernel κ u p.1) {q : ℝ × ℝ | q.1 ≤ p.2}).toReal
        - ((rayKernel κ u p.1) {q : ℝ × ℝ | q.2 ≤ p.2}).toReal := h
  have heq : (fun p : Z × ℝ =>
      ((rayKernel κ u p.1) {q : ℝ × ℝ | q.1 ≤ p.2}).toReal
        - ((rayKernel κ u p.1) {q : ℝ × ℝ | q.2 ≤ p.2}).toReal)
      = fun p : Z × ℝ => rayFlux (rayCoupling (κ p.1) u) p.2 := by
    funext p
    rw [rayKernel_apply hu p.1]
    rfl
  rw [heq] at h'
  exact h'

/-! ## The regularity package and the paper segment test -/

theorem rayCoupling_regularity {κ : Kernel Z (M × M)} [IsMarkovKernel κ] {u : M → ℝ}
    (hu : LipschitzWith 1 u)
    (h1 : ∀ z r, (κ z) {p : M × M | u p.1 = r} = 0)
    (h2 : ∀ z r, (κ z) {p : M × M | u p.2 = r} = 0) :
    (∀ A : Set (ℝ × ℝ), MeasurableSet A →
      Measurable fun z : Z => (rayCoupling (κ z) u A).toReal) ∧
    (∀ z, IsFiniteMeasure (rayCoupling (κ z) u)) ∧
    (∀ z r, rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = 0) ∧
    (∀ z r, rayCoupling (κ z) u {q : ℝ × ℝ | q.2 = r} = 0) ∧
    Measurable (fun p : Z × ℝ => rayFlux (rayCoupling (κ p.1) u) p.2) ∧
    ∀ z, Continuous fun r : ℝ => rayFlux (rayCoupling (κ z) u) r := by
  have hu' : Measurable u := hu.continuous.measurable
  have hfam : ∀ A : Set (ℝ × ℝ), MeasurableSet A →
      Measurable fun z : Z => (rayCoupling (κ z) u A).toReal := fun A hA =>
    measurable_rayCoupling_coe_toReal hu' hA
  have hfin : ∀ z, IsFiniteMeasure (rayCoupling (κ z) u) := fun z =>
    rayCoupling_isFiniteMeasure hu' z
  have hatom1 : ∀ z r, rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = 0 := by
    intro z r; rw [rayCoupling_atom_first hu' z r]; exact h1 z r
  have hatom2 : ∀ z r, rayCoupling (κ z) u {q : ℝ × ℝ | q.2 = r} = 0 := by
    intro z r; rw [rayCoupling_atom_second hu' z r]; exact h2 z r
  have hmeas : Measurable fun p : Z × ℝ => rayFlux (rayCoupling (κ p.1) u) p.2 := 
    measurable_rayFlux_kernel hu'
  have hcont : ∀ z, Continuous fun r : ℝ => rayFlux (rayCoupling (κ z) u) r := fun z =>
    rayCoupling_continuous_of_atomless hu' z (hatom1 z) (hatom2 z)
  exact ⟨hfam, hfin, hatom1, hatom2, hmeas, hcont⟩

theorem measurable_segmentMinRatFamily_rayCoupling {κ : Kernel Z (M × M)} [IsMarkovKernel κ]
    {u : M → ℝ} (hu : Measurable u) (q : ℕ → ℚ) (j : ℕ) :
    Measurable (segmentMinRatFamily (fun z r => rayFlux (rayCoupling (κ z) u) r) q j) :=
  measurable_segmentMinRatFamily (measurable_rayFlux_kernel hu) q j

theorem measurableSet_segmentTestRat_rayCoupling {κ : Kernel Z (M × M)} [IsMarkovKernel κ]
    {u : M → ℝ} (hu : Measurable u) (q : ℕ → ℚ) (j : ℕ) :
    MeasurableSet {p : Z × ℝ |
      0 < segmentMinRatFamily (fun z r => rayFlux (rayCoupling (κ z) u) r) q j p} :=
  measurableSet_segmentTestRat (measurable_rayFlux_kernel hu) q j

theorem measurableSet_paper_segmentTest_rayCoupling {κ : Kernel Z (M × M)} [IsMarkovKernel κ]
    {u : M → ℝ} (hu : LipschitzWith 1 u)
    (h1 : ∀ z r, (κ z) {p : M × M | u p.1 = r} = 0)
    (h2 : ∀ z r, (κ z) {p : M × M | u p.2 = r} = 0)
    (q : ℕ → ℚ) (j : ℕ) :
    MeasurableSet {p : Z × ℝ |
      0 < segmentMin (fun r : ℝ => rayFlux (rayCoupling (κ p.1) u) r) p.2
        ((q j : ℚ) : ℝ)} := by
  obtain ⟨-, -, -, -, hmeas, hcont⟩ := rayCoupling_regularity hu h1 h2
  exact measurableSet_paper_segmentTest hmeas hcont q j

end OTSelector.Reconstruction
