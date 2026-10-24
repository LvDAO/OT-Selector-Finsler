import OTSelector.Reconstruction.FinslerOriginalPopulationFocalValue

/-!
# Reducing the global focal-value equality to the rootwise equality and gluing

This module attacks the first theorem-level input of the population focal-value
chain P1, namely FocalValueEquality: the paper's global weighted value recovery
identity I_w = p_A (main.tex theorem general-focal-value-equality, equation
interleaved-weighted-value-equality), stated for the global weighted stationary
pressure at the probe family of the weighted stationary functional.

## The decomposition

The paper proves I_w = p_A by three separate steps, and the preceding module
already uses them in the direction FocalValueEquality implies P1:

* the rootwise focal-value equality I_w(z, v) = I_2(z, v) at every root, proved
  unconditionally in the uniformly elliptic regime by the repository theorem
  weightedStationaryPressure_eq_secondMoment_of_uniform_elliptic;
* the measured pressure formula p_A(t) = P_2(t), the limit of the legal finite
  pressures, which is the typed paper input MeasurablePressureLimit;
* the gluing identity I_w(t) = P_w(t), the global weighted stationary pressure
  written as the population atlas sum of the per-root weighted stationary
  pressures, which is the typed paper input PopulationFocalValueLimit (equivalently
  CampbellAveragedStationaryPressureIdentification).

This module proves the reverse direction: the global focal-value equality
FocalValueEquality follows from the gluing identity plus the measured pressure
limit plus the rootwise equality.  Consequently FocalValueEquality is NOT an
independent analytic input: given the measured pressure limit and the rootwise
equality, it is equivalent to the gluing identity P1, so the audit input P1
already implies the paper's global equality I_w = p_A.

The rootwise equality is used only almost everywhere in the population root: the
gluing lemma needs nothing but the a.e. equality of the per-root pressure
functions, because the atlas integral and the Campbell sum only see the root
almost everywhere.  This is the paper's a.e.-active-root convention.

## What is proved

* PerRootFocalValueEqualityAe: the rootwise equality almost everywhere at every
  root, a strictly weaker form of PerRootFocalValueEquality;
* perRootFocalValueEqualityAe_of_perRootFocalValueEquality and
  perRootFocalValueEqualityAe_of_uniform_elliptic: the pointwise and the
  uniformly elliptic rootwise equalities imply the a.e. form;
* campbellAveragedStationaryPressure_congr_of_ae: the exact gluing lemma, two
  Campbell averages of per-root weighted pressures agree as soon as the per-root
  functions agree almost everywhere in the root at every tilt;
* campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe:
  the gluing lemma in the form needed here, the Campbell average of the per-root
  weighted pressures is the measured second-moment population pressure;
* focalValueEquality_of_campbellAveragedStationaryPressureIdentification: the
  global equality I_w = p_A from the gluing identity, the measured pressure
  limit and the a.e. rootwise equality;
* campbellAveragedStationaryPressureIdentification_of_focalValueEquality: the
  converse, so the two global statements are equivalent given the other two
  steps;
* focalValueEquality_iff_campbellAveragedStationaryPressureIdentification and
  focalValueEquality_iff_populationFocalValueLimit: the exact equivalences;
* focalValueEquality_of_gluing_steps: the same from the pointwise rootwise
  equality, matching the interface of the preceding module;
* focalValueEquality_of_populationFocalValueLimit: in the fully general form,
  P1 plus the measured pressure limit plus the a.e. rootwise equality implies
  the global focal-value equality;
* focalValueEquality_of_populationFocalValueLimit_of_uniform_elliptic and its
  iff form: in the uniformly elliptic regime the rootwise step is proved by the
  repository, so the global equality follows from P1 and the measured pressure
  limit alone;
* PopulationFocalValueAtZero: the zero-tilt gluing identity, a strictly weaker
  typed input specifying the gluing only at zero tilt;
* weightedStationaryPressure_zero_eq_pA_zero_of_zeroTiltGluing: the zero-tilt
  form of the global focal-value equality from that weaker input;
* weightedStationaryPressure_zero_eq_pA_zero_of_uniform_elliptic: the zero-tilt
  focal value identity in the elliptic regime from P1 and the measured pressure
  limit.

The residual of the global focal-value equality is therefore exactly two typed
paper inputs: the population gluing identity P1 (the global weighted stationary
pressure is the atlas Campbell average of the per-root weighted pressures) and
the measured pressure limit p_A = P_2; the rootwise equality is not an input in
the elliptic regime.  Alternatively, if only the zero-tilt focal value is
wanted, the gluing identity is needed at tilt zero only, which is the strictly
weaker input PopulationFocalValueAtZero.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold Module OTSelector.Probability
open OTSelector.Geometry OTSelector.PointProcess OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M} {W : Type*} {G Cb : ℝ}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}

/-! ## The rootwise equality almost everywhere -/

/-- The rootwise focal-value equality almost everywhere: at every probe and root
the weighted and second-moment stationary pressures coincide at almost every
population root, for every tilt.  This is the paper's a.e.-active-root
convention and is strictly weaker than the pointwise
PerRootFocalValueEquality. -/
def PerRootFocalValueEqualityAe
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (j : ℕ),
    ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
      ∀ (v : ℝ),
        weightedStationaryPressure α β (coef φ j z) (probeFam φ j z) v =
          secondMomentStationaryPressure α β (coef φ j z) (probeFam φ j z) v

/-- The pointwise rootwise focal-value equality implies the a.e. form. -/
theorem perRootFocalValueEqualityAe_of_perRootFocalValueEquality
    (hRoot : PerRootFocalValueEquality α β coef probeFam) :
    PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam := by
  intro φ j
  exact Filter.Eventually.of_forall (fun z v => hRoot φ j z v)

/-- In the uniformly elliptic regime the a.e. rootwise focal-value equality is
unconditional: the repository proves the pointwise rootwise equality there. -/
theorem perRootFocalValueEqualityAe_of_uniform_elliptic
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C) :
    PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam :=
  perRootFocalValueEqualityAe_of_perRootFocalValueEquality
    (perRootFocalValueEquality_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound)

/-! ## The gluing lemma -/

/-- **The gluing lemma.**  Two Campbell averages of per-root weighted stationary
pressures agree as soon as the per-root pressure functions agree almost
everywhere in the root at every tilt.  No integrability hypothesis is needed:
the atlas integral only sees the root almost everywhere, and the Campbell sum
is termwise equal. -/
theorem campbellAveragedStationaryPressure_congr_of_ae
    (A A' : ℕ → Z → ℝ → ℝ → ℝ)
    (f f' : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hae : ∀ (j : ℕ),
      ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
        ∀ (v : ℝ),
          weightedStationaryPressure α β (A j z) (f j z) v =
            weightedStationaryPressure α β (A' j z) (f' j z) v)
    (q t : ℝ) :
    campbellAveragedStationaryPressure α β Seed a κ lambda A f q t =
      campbellAveragedStationaryPressure α β Seed a κ lambda A' f' q t := by
  rw [campbellAveragedStationaryPressure_def α β Seed a κ lambda A f q t,
    campbellAveragedStationaryPressure_def α β Seed a κ lambda A' f' q t]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards [hae j] with z hz
  rw [hz (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))]

/-- The gluing lemma in the form needed for the population identity: under the
a.e. rootwise focal-value equality the Campbell average of the per-root weighted
stationary pressures equals the measured second-moment population pressure.
This is the integration step of the paper: rootwise equality plus the atlas
integration gives the equality of the two population pressures. -/
theorem campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (φ : FinalProbeSpace A B) (t : ℝ) :
    campbellAveragedStationaryPressure α β Seed a κ lambda (coef φ) (probeFam φ) q t =
      populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t := by
  rw [campbellAveragedStationaryPressure_def α β Seed a κ lambda (coef φ) (probeFam φ) q t,
    populationSecondMomentPressure_apply Seed a κ lambda α β coef probeFam q φ t]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards [hRoot φ j] with z hz
  rw [hz (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))]

/-! ## The global focal-value equality from the gluing and the measured limit -/

/-- **The global focal-value equality from the population gluing identity.**
Given the gluing identity P1 (the global weighted stationary pressure is the
Campbell average of the per-root weighted stationary pressures), the measured
pressure limit p_A = P_2 and the a.e. rootwise focal-value equality, the paper's
global value recovery identity I_w = p_A holds for every probe and tilt. -/
theorem focalValueEquality_of_campbellAveragedStationaryPressureIdentification
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hGlue : CampbellAveragedStationaryPressureIdentification Seed a κ lambda
      Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    FocalValueEquality pA Ag fg α β := by
  intro φ t
  rw [hGlue φ t,
    campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe
      hRoot φ t,
    ← hLimit φ t]

/-- The converse of the preceding reduction: the global focal-value equality and
the measured pressure limit give the population gluing identity P1 (in its
Campbell form), provided the a.e. rootwise focal-value equality holds.  Hence
the two global inputs are interchangeable given the other two steps. -/
theorem campbellAveragedStationaryPressureIdentification_of_focalValueEquality
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    CampbellAveragedStationaryPressureIdentification Seed a κ lambda
      Ag fg α β coef probeFam q := by
  intro φ t
  rw [hFocal φ t, hLimit φ t]
  exact (campbellAveragedStationaryPressure_eq_populationSecondMomentPressure_of_perRootAe
    hRoot φ t).symm

/-- The global focal-value equality is equivalent to the population gluing
identity P1, given the measured pressure limit and the a.e. rootwise equality:
the two are two faces of one identity once the measured limit is known. -/
theorem focalValueEquality_iff_campbellAveragedStationaryPressureIdentification
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    FocalValueEquality pA Ag fg α β ↔
      CampbellAveragedStationaryPressureIdentification Seed a κ lambda
        Ag fg α β coef probeFam q :=
  ⟨fun hFocal =>
      campbellAveragedStationaryPressureIdentification_of_focalValueEquality
        pA Ag fg coef probeFam q hFocal hLimit hRoot,
    fun hGlue =>
      focalValueEquality_of_campbellAveragedStationaryPressureIdentification
        pA Ag fg coef probeFam q hGlue hLimit hRoot⟩

/-- The global focal-value equality is equivalent to the unfolded population
identity P1, given the measured pressure limit and the a.e. rootwise equality.
This is the exact reduction of the paper's value recovery theorem to the pair
of typed inputs P1 and the measured pressure limit. -/
theorem focalValueEquality_iff_populationFocalValueLimit
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    FocalValueEquality pA Ag fg α β ↔
      PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q := by
  rw [focalValueLimit_iff_campbellAveragedStationaryPressureIdentification
    (Seed := Seed) (a := a) (κ := κ) (lambda := lambda)
    Ag fg α β coef probeFam q]
  exact focalValueEquality_iff_campbellAveragedStationaryPressureIdentification
    pA Ag fg coef probeFam q hLimit hRoot

/-- The global focal-value equality from the pointwise rootwise equality, the
gluing identity and the measured pressure limit; this keeps the interface of the
preceding module, where the rootwise step is a pointwise equality. -/
theorem focalValueEquality_of_gluing_steps
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hGlue : CampbellAveragedStationaryPressureIdentification Seed a κ lambda
      Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEquality α β coef probeFam) :
    FocalValueEquality pA Ag fg α β :=
  focalValueEquality_of_campbellAveragedStationaryPressureIdentification
    pA Ag fg coef probeFam q hGlue hLimit
    (perRootFocalValueEqualityAe_of_perRootFocalValueEquality hRoot)

/-- **The global focal-value equality from the single population identity P1**
plus the measured pressure limit, with the rootwise equality in a.e. form: the
paper's value recovery I_w = p_A is not an independent input. -/
theorem focalValueEquality_of_populationFocalValueLimit
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    FocalValueEquality pA Ag fg α β :=
  focalValueEquality_of_campbellAveragedStationaryPressureIdentification
    pA Ag fg coef probeFam q
    (campbellAveragedStationaryPressureIdentification_of_focalValueLimit
      Seed a κ lambda Ag fg α β coef probeFam q hP1)
    hLimit hRoot

/-! ## The elliptic regime: only the two global paper inputs remain -/

/-- In the uniformly elliptic regime the rootwise step is proved by the
repository, so the global focal-value equality follows from P1 and the measured
pressure limit alone: two typed paper inputs, no rootwise input. -/
theorem focalValueEquality_of_populationFocalValueLimit_of_uniform_elliptic
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    FocalValueEquality pA Ag fg α β :=
  focalValueEquality_of_populationFocalValueLimit pA Ag fg coef probeFam q hP1 hLimit
    (perRootFocalValueEqualityAe_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound)

/-- The global focal-value equality is equivalent to P1 in the uniformly
elliptic regime, given the measured pressure limit. -/
theorem focalValueEquality_iff_populationFocalValueLimit_of_uniform_elliptic
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    FocalValueEquality pA Ag fg α β ↔
      PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  focalValueEquality_iff_populationFocalValueLimit pA Ag fg coef probeFam q hLimit
    (perRootFocalValueEqualityAe_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound)

/-! ## The zero-tilt focal value -/

/-- The zero-tilt gluing identity: the global weighted stationary pressure at
zero tilt equals the atlas Campbell average of the per-root weighted pressures at
zero tilt.  This is a strictly weaker typed input than the full population
identity P1, which is required at every tilt. -/
def PopulationFocalValueAtZero
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B),
    weightedStationaryPressure α β (Ag φ) (fg φ) 0 =
      ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          weightedStationaryPressure α β (coef φ j z) (probeFam φ j z) 0 ∂lambda

/-- The full population gluing identity P1 implies its zero-tilt form. -/
theorem populationFocalValueAtZero_of_campbellAveragedStationaryPressureIdentification
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hGlue : CampbellAveragedStationaryPressureIdentification Seed a κ lambda
      Ag fg α β coef probeFam q) :
    PopulationFocalValueAtZero Seed a κ lambda Ag fg α β coef probeFam q := by
  intro φ
  rw [hGlue φ 0, campbellAveragedStationaryPressure_def α β Seed a κ lambda
    (coef φ) (probeFam φ) q 0]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards with z
  rw [zero_mul]

/-- The unfolded population identity P1 implies the zero-tilt gluing identity. -/
theorem populationFocalValueAtZero_of_populationFocalValueLimit
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q) :
    PopulationFocalValueAtZero Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueAtZero_of_campbellAveragedStationaryPressureIdentification
    Ag fg coef probeFam q
    (campbellAveragedStationaryPressureIdentification_of_focalValueLimit
      Seed a κ lambda Ag fg α β coef probeFam q hP1)

/-- **The zero-tilt focal-value equality from the zero-tilt gluing identity.**
The equality of the global weighted stationary pressure at zero tilt with the
legal pressure p_A at zero tilt needs the gluing identity only at tilt zero,
together with the measured pressure limit and the a.e. rootwise equality. -/
theorem weightedStationaryPressure_zero_eq_pA_zero_of_zeroTiltGluing
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hGlue0 : PopulationFocalValueAtZero Seed a κ lambda Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    ∀ (φ : FinalProbeSpace A B),
      weightedStationaryPressure α β (Ag φ) (fg φ) 0 = pA φ 0 := by
  intro φ
  rw [hGlue0 φ, hLimit φ 0,
    populationSecondMomentPressure_apply Seed a κ lambda α β coef probeFam q φ 0]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards [hRoot φ j] with z hz
  rw [hz 0, zero_mul]

/-- The zero-tilt focal-value equality in the uniformly elliptic regime from the
zero-tilt gluing identity and the measured pressure limit. -/
theorem weightedStationaryPressure_zero_eq_pA_zero_of_zeroTiltGluing_of_uniform_elliptic
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (hGlue0 : PopulationFocalValueAtZero Seed a κ lambda Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    ∀ (φ : FinalProbeSpace A B),
      weightedStationaryPressure α β (Ag φ) (fg φ) 0 = pA φ 0 :=
  weightedStationaryPressure_zero_eq_pA_zero_of_zeroTiltGluing pA Ag fg coef probeFam q
    hGlue0 hLimit
    (perRootFocalValueEqualityAe_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound)

/-- The zero-tilt focal-value equality in the uniformly elliptic regime from the
full population identity P1 and the measured pressure limit. -/
theorem weightedStationaryPressure_zero_eq_pA_zero_of_uniform_elliptic
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    ∀ (φ : FinalProbeSpace A B),
      weightedStationaryPressure α β (Ag φ) (fg φ) 0 = pA φ 0 :=
  fun φ =>
    focalValueEquality_of_populationFocalValueLimit_of_uniform_elliptic
      pA Ag fg coef probeFam q c C hc hA_meas hA_low hA_bound hP1 hLimit φ 0

end OTSelector.Reconstruction