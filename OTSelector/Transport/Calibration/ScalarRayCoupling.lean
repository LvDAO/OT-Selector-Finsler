import LeanPool.Vlasov.OT.Coupling
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.StrongLaw
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import OTSelector.Transport.ScalarForwardFlux
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerIntrinsicFinslerRayCoupling.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerIntrinsicFinslerRayCoupling`; the selected original proof blocks follow. -/
section

/-!
# Transport.Calibration.ScalarRayCoupling

* **Conditions:** A measurable potential calibrates an actual pair law; probability and atomlessness/support hypotheses are imposed exactly where flux and cover identities need them.
* **Objects:** Scalar pushforward couplings, forward support, cut flux and positive-flux interval covers, also conditional on whole-ray labels.
* **Proof detail:** Push both endpoints through their unchanged potential clocks, infer order from nonnegative distance, and use marginal subtraction plus the supplied atomlessness and support.

Mathematical sources:
- [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf): Section 235G, integration along an inverse-measure-preserving map.
- [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=19): Section 1.2, Theorem 1.2.1(iii)–(v), p. 11.
- [OT-Selector project authors, Project manuscript main.tex (local provenance)](/data/lyuwt/OT-Selector-smooth-length/main.tex): main.tex, proposition prop:ray-forward-criterion, lines 524–565, equation eq:ray-cut-flux at line 530; equation eq:intrinsic-active-cover at line 982.
- [D. H. Fremlin, Measure Theory, Volume 4, Chapter 45 (version 5 June 2009)](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18): 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula.

Source relation (derived): The scalar bookkeeping implements the manuscript flux/cover formulas. It does not construct the geometric ray parametrization or derive conditional atomlessness.
-/

/-!
# Finsler ray couplings per whole-ray label

This module constructs the per-whole-ray-label scalar coupling of the intrinsic
active ray data of the paper's structural invariance theorem (main.tex:958),
the data of prop:general-optimal-face (main.tex:422) and
prop:ray-forward-criterion (main.tex:524).

Given an optimal plan (or a conditional kernel supplied by the optimal-face
disintegration of OptimalFaceDisintegration.lean) whose transported pairs are
calibrated by a 1-Lipschitz optimal potential u, the ray coordinate of a pair
is its potential clock (u x, u y).  We construct

  rayCoupling gamma u = gamma.map (fun p => (u p.1, u p.2)),

and prove that it is a probability measure whenever gamma is, that it is
forward almost everywhere because every calibrated pair satisfies
u y - u x = dist x y >= 0, and that with an atomless first scalar marginal it
realizes the ray-cut flux identity eq:ray-cut-flux and the cover identity
eq:intrinsic-active-cover of FinslerIntrinsicActiveRayDataConstruction.lean.

The kernel forms (conditionalRayCoupling_forward / _flux / _cover) show that
for almost every whole-ray label of the optimal-face disintegration the scalar
ray coupling is forward and satisfies the per-label flux and cover identities.

Remaining gap: the actual geometric ray parametrization (transported minimal
calibrated arcs / complete geodesics and the identification of the potential
clock with the paper's arclength ray coordinate), the atomlessness of the
conditional scalar laws (absolute continuity of the conditional laws), and the
two-cover block matching of the active-block invariance remain the outstanding
inputs; this module constructs the per-label scalar couplings and their flux
from the calibrated optimal-face data.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {M Z : Type*} [MeasurableSpace Z] [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The ray-coordinate map of a transported pair: the pair of potential clocks. -/
def rayCouplingMap (u : M → ℝ) : M × M → ℝ × ℝ :=
  fun p ↦ (u p.1, u p.2)

theorem measurable_rayCouplingMap {u : M → ℝ} (hu : Measurable u) :
    Measurable (rayCouplingMap u) :=
  (hu.comp measurable_fst).prodMk (hu.comp measurable_snd)

/-- The scalar ray coupling of a physical plan in the potential clock. -/
def rayCoupling (γ : Measure (M × M)) (u : M → ℝ) : Measure (ℝ × ℝ) :=
  γ.map (rayCouplingMap u)

/-- The scalar ray coupling of a probability plan is a probability measure. -/
theorem rayCoupling_isProbability (γ : Measure (M × M)) [IsProbabilityMeasure γ]
    {u : M → ℝ} (hu : Measurable u) : IsProbabilityMeasure (rayCoupling γ u) :=
  Measure.isProbabilityMeasure_map (measurable_rayCouplingMap hu).aemeasurable

/-- Forwardness of the scalar ray coupling: calibrated transported pairs
increase the potential clock, so the scalar ray coupling is carried by the
forward set of prop:ray-forward-criterion. -/
theorem rayCoupling_forward (γ : Measure (M × M)) {u : M → ℝ} (hu : Measurable u)
    (hcal : ∀ᵐ p ∂γ, u p.2 - u p.1 = dist p.1 p.2) :
    rayCoupling γ u {q : ℝ × ℝ | ¬ q.1 ≤ q.2} = 0 := by
  have hset : MeasurableSet {q : ℝ × ℝ | ¬ q.1 ≤ q.2} := by
    have hEq : {q : ℝ × ℝ | ¬ q.1 ≤ q.2} = {q : ℝ × ℝ | q.2 < q.1} := by
      ext q
      simp only [Set.mem_ofPred_eq, not_le]
    rw [hEq]
    exact measurableSet_lt measurable_snd measurable_fst
  rw [rayCoupling, Measure.map_apply (measurable_rayCouplingMap hu) hset]
  have hfail : γ {p : M × M | ¬ (u p.2 - u p.1 = dist p.1 p.2)} = 0 :=
    MeasureTheory.ae_iff.mp hcal
  have hsub : rayCouplingMap u ⁻¹' {q : ℝ × ℝ | ¬ q.1 ≤ q.2} ⊆
      {p : M × M | ¬ (u p.2 - u p.1 = dist p.1 p.2)} := by
    intro p hp
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, rayCouplingMap] at hp ⊢
    intro hcon
    have hneg : u p.2 - u p.1 < 0 := by linarith [not_le.mp hp]
    linarith [hcon, dist_nonneg (x := p.1) (y := p.2)]
  exact measure_mono_null hsub hfail

/-- Ray-cut flux identity per whole-ray label (eq:ray-cut-flux): under an
atomless first scalar marginal, the surplus of the constructed ray coupling is
its strict crossing measure. -/
theorem rayCoupling_flux (γ : Measure (M × M)) [IsProbabilityMeasure γ]
    {u : M → ℝ} (hu : Measurable u)
    (hcal : ∀ᵐ p ∂γ, u p.2 - u p.1 = dist p.1 p.2)
    (hatom : ∀ r : ℝ, rayCoupling γ u {q : ℝ × ℝ | q.1 = r} = 0) (r : ℝ) :
    rayFlux (rayCoupling γ u) r =
      ((rayCoupling γ u) {q : ℝ × ℝ | q.1 < r ∧ r < q.2}).toReal := by
  haveI hp : IsProbabilityMeasure (rayCoupling γ u) := rayCoupling_isProbability γ hu
  haveI : IsFiniteMeasure (rayCoupling γ u) := ⟨by rw [measure_univ]; simp⟩
  exact rayFlux_eq_crossing (rayCoupling γ u) (rayCoupling_forward γ hu hcal) (hatom r)

/-- Cover identity per whole-ray label (eq:intrinsic-active-cover). -/
theorem rayCoupling_cover (γ : Measure (M × M)) [IsProbabilityMeasure γ]
    {u : M → ℝ} (hu : Measurable u)
    (hcal : ∀ᵐ p ∂γ, u p.2 - u p.1 = dist p.1 p.2)
    (hatom : ∀ r : ℝ, rayCoupling γ u {q : ℝ × ℝ | q.1 = r} = 0)
    (G : Set (ℝ × ℝ)) (hGnull : rayCoupling γ u Gᶜ = 0)
    (hsupp : ∀ p ∈ G, ∀ U : Set (ℝ × ℝ), IsOpen U → p ∈ U →
      0 < rayCoupling γ u U) :
    {r : ℝ | 0 < rayFlux (rayCoupling γ u) r} = ⋃ p ∈ G, Set.Ioo p.1 p.2 := by
  haveI hp : IsProbabilityMeasure (rayCoupling γ u) := rayCoupling_isProbability γ hu
  haveI : IsFiniteMeasure (rayCoupling γ u) := ⟨by rw [measure_univ]; simp⟩
  exact pos_rayFlux_eq_iUnion_intervals (rayCoupling γ u)
    (rayCoupling_forward γ hu hcal) hatom G hGnull hsupp

/-- Kernel form: for almost every whole-ray label of the optimal-face
disintegration, the conditional scalar ray coupling is forward. -/
theorem conditionalRayCoupling_forward {law : Measure Z} (κ : Kernel Z (M × M))
    [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (hcal : ∀ᵐ z ∂law, ∀ᵐ p ∂(κ z), u p.2 - u p.1 = dist p.1 p.2) :
    ∀ᵐ z ∂law, rayCoupling (κ z) u {q : ℝ × ℝ | ¬ q.1 ≤ q.2} = 0 := by
  filter_upwards [hcal] with z hz
  exact rayCoupling_forward (κ z) hu.continuous.measurable hz

/-- Kernel form: for almost every whole-ray label the conditional scalar ray
coupling satisfies the ray-cut flux identity at every tilt under atomlessness. -/
theorem conditionalRayCoupling_flux {law : Measure Z} (κ : Kernel Z (M × M))
    [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (hcal : ∀ᵐ z ∂law, ∀ᵐ p ∂(κ z), u p.2 - u p.1 = dist p.1 p.2)
    (hatom : ∀ᵐ z ∂law, ∀ r : ℝ, rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = 0) :
    ∀ᵐ z ∂law, ∀ r : ℝ, rayFlux (rayCoupling (κ z) u) r =
      ((rayCoupling (κ z) u) {q : ℝ × ℝ | q.1 < r ∧ r < q.2}).toReal := by
  filter_upwards [hcal, hatom] with z hz hza r
  exact rayCoupling_flux (κ z) hu.continuous.measurable hz hza r

/-- Kernel form: for almost every whole-ray label the positive-flux set is the
union of the crossing intervals over a full-measure supporting set of the
conditional scalar ray coupling (eq:intrinsic-active-cover). -/
theorem conditionalRayCoupling_cover {law : Measure Z} (κ : Kernel Z (M × M))
    [IsMarkovKernel κ] {u : M → ℝ} (hu : LipschitzWith 1 u)
    (hcal : ∀ᵐ z ∂law, ∀ᵐ p ∂(κ z), u p.2 - u p.1 = dist p.1 p.2)
    (hatom : ∀ᵐ z ∂law, ∀ r : ℝ, rayCoupling (κ z) u {q : ℝ × ℝ | q.1 = r} = 0)
    (G : Z → Set (ℝ × ℝ))
    (hGnull : ∀ᵐ z ∂law, rayCoupling (κ z) u (G z)ᶜ = 0)
    (hsupp : ∀ᵐ z ∂law, ∀ p ∈ G z, ∀ U : Set (ℝ × ℝ), IsOpen U → p ∈ U →
      0 < rayCoupling (κ z) u U) :
    ∀ᵐ z ∂law, {r : ℝ | 0 < rayFlux (rayCoupling (κ z) u) r}
      = ⋃ p ∈ G z, Set.Ioo p.1 p.2 := by
  filter_upwards [hcal, hatom, hGnull, hsupp] with z hz hza hGn hsp
  exact rayCoupling_cover (κ z) hu.continuous.measurable hz hza (G z) hGn hsp

end OTSelector.Reconstruction
end
end
