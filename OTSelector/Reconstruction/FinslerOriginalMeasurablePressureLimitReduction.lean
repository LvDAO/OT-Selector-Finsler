import OTSelector.Reconstruction.FinslerOriginalFocalValueEqualityReduction

/-!
# Reduction of the measured pressure limit to a single convergence statement

This module attacks the second remaining theorem-level input of the population
focal-value chain P1, namely MeasurablePressureLimit of
FinslerOriginalPopulationFocalValue: for every probe and tilt, the legal finite
pressure limit pA equals the measured population second-moment pressure.

## 1. The exact type

MeasurablePressureLimit Seed a kappa lambda pA alpha beta coef probeFam q is,
by definition,

  forall (probe phi) (tilt t),
    pA phi t = sum over j of the integral over the population root piece j of
      theta_j(z) to the power (-2 over q) times
        secondMomentStationaryPressure alpha beta (coef phi j z) (probeFam phi j z)
          (t times theta_j(z) to the power (2 over q))

i.e. the sum of the per-root frozen second-moment pressures at the scaled tilt,
integrated against the population root law, with the measured-atlas change of
measure.  The function pA is the thermodynamic limit of the legal
maximum-cardinality finite pressure: it is a parameter of the chain, not defined
in the tree (the paper defines it as the finite pressure limit).

## 2. The repository marked-pressure lane does not close the identity

The repository proves existence of the limit, not its identification with the
atlas second-moment sum:

* markedScalePressure (OTSelector/Probability/MarkedPressureLimit.lean) and
  markedPressure (OTSelector/Probability/MarkedPoissonCube.lean) are the
  scale-normalized and finite-intensity marked pressures;
* exists_markedScalePressure_limit
  (OTSelector/Probability/MarkedPressureLimitBlock.lean) proves that for q > 4
  the marked scale pressure converges to a concave G-Lipschitz function;
* exists_legalMarkedScalePressure_limit_of_scalarBins
  (OTSelector/Reconstruction/MarkedStationaryValueLegalPressureLimit.lean)
  proves the same for the actual original legal maximum-cardinality pressure;
* markedPressureRepresentation_of_windowReadout
  (OTSelector/Reconstruction/FinslerOriginalMarkedPressureRepresentation.lean)
  identifies the limit with a Palm integral of a local readout, conditional on
  the readout identification; FinslerOriginalPalmPressureIdentification.lean
  reduces the Palm hypothesis to exactly that representation plus a pointwise
  comparison and records both as the remaining analytic inputs.

Nothing in the lane identifies the limit with secondMomentStationaryPressure, so
the measured pressure formula is not closed by the repository.  Consequently
this module proves the sharp reduction instead.

## 3. The reduction

Let pressure be the finite-scale measured pressure family (in the actual lane
the legal marked scale pressure at scale R).  We prove:

* FinitePressureLimitAt pressure pA: the finite pressures converge to pA.  In
  the actual lane this is the construction of pA from the thermodynamic limit,
  supplied by the existence theorems above, not analytic content;
* AtlasMeasuredPressureLimit pressure: the single convergence statement that the
  finite-scale pressures converge to the measured atlas second-moment pressure;
* measurablePressureLimit_iff_atlasMeasuredPressureLimit: given the lane
  identification FinitePressureLimitAt pressure pA, the P1 input
  MeasurablePressureLimit is EQUIVALENT to that single convergence statement
  (uniqueness of limits in the real line);
* atlasMeasuredPressureLimit_iff_eventually_bounds: the sharpest scalar form of
  the statement, two one-sided eventual bounds with arbitrary comparison level
  (the order characterization of convergence at top).  This is the form the
  paper's sandwich proof produces: an eventual lower bound and an eventual upper
  bound with the comparison level ranging over all reals;
* measurablePressureLimit_iff_eventually_bounds: the composition, so the P1
  input is exactly the two-sided eventual sandwich of the finite pressures
  against the atlas second-moment pressure;
* weightedStationaryPressure_eq_populationSecondMomentPressure_of_gluing_of_rootwiseAe
  and measurablePressureLimit_iff_focalValueEquality_of_gluing_and_rootwiseAe:
  given the population gluing identity P1 and the almost-everywhere rootwise
  focal-value equality, the measured pressure limit is equivalent to the paper's
  global focal-value equality I_w = pA.  So the two global inputs of the P1
  chain are not independent: given the gluing and the rootwise step, each is
  equivalent to the other;
* the uniformly elliptic corollary, where the rootwise step is proved by the
  repository through perRootFocalValueEquality_of_uniform_elliptic.

The rootwise almost-everywhere predicate and the gluing integral step are
recorded locally here, with distinct names, so that this module depends only on
the already built population focal-value module; they are the a.e. form of
PerRootFocalValueEquality and of
populationSecondMomentPressure_eq_campbellAveraged_of_perRootFocalValueEquality.

## Exact residual

The measured pressure formula reduces to the single convergence statement

  forall phi t,
    Tendsto (fun R => pressure phi R t) atTop (nhds (populationSecondMomentPressure phi t)),

equivalently: for every probe, tilt and comparison level b, the finite pressures
are eventually above b when b is below the atlas pressure and eventually below b
when b is above it.  In the actual lane pressure is the legal marked scale
pressure and FinitePressureLimitAt is supplied by the thermodynamic limit
existence theorem of the repository, so no lane identification is left open.

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

/-! ## The exact type -/

/-- The exact measured form of the P1 second input: the legal finite pressure
limit pA equals the atlas sum of the per-root frozen second-moment stationary
pressures at the scaled tilt.  This is the defining unfolding of
MeasurablePressureLimit together with the definition of the measured population
pressure. -/
theorem measurablePressureLimit_iff_atlasForm
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q ↔
      ∀ (φ : FinalProbeSpace A B) (t : ℝ),
        pA φ t =
          ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
            populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
              secondMomentStationaryPressure α β (coef φ j z) (probeFam φ j z)
                (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ∂lambda := by
  unfold MeasurablePressureLimit populationSecondMomentPressure
  rfl

/-! ## The lane identification and the single convergence statement -/

/-- The measured finite-scale pressure family converges to pA.  In the actual
lane the finite-scale pressure is the legal marked scale pressure and this is
the construction of pA from the thermodynamic limit, not analytic content. -/
def FinitePressureLimitAt
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (pA : FinalProbeSpace A B → ℝ → ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    Tendsto (fun R : ℝ => pressure φ R t) atTop (𝓝 (pA φ t))

/-- **The single convergence statement.**  The measured finite-scale pressures
converge to the measured atlas second-moment pressure at every probe and tilt.
This is the paper's high-dimensional measurable pressure formula in limit form,
and the only remaining convergence content of the P1 second input. -/
def AtlasMeasuredPressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    Tendsto (fun R : ℝ => pressure φ R t) atTop
      (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t))

/-- The single convergence statement closes the P1 input, given that the lane
finite pressures converge to pA: uniqueness of limits in the real line. -/
theorem measurablePressureLimit_of_finitePressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA)
    (hAtlas : AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q :=
  fun φ t => tendsto_nhds_unique (hPA φ t) (hAtlas φ t)

/-- Conversely, the P1 input and the lane identification give the single
convergence statement. -/
theorem atlasMeasuredPressureLimit_of_measurablePressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q := by
  intro φ t
  have h := hPA φ t
  rw [hLimit φ t] at h
  exact h

/-- **The reduction.**  Given the lane identification of pA as the limit of the
measured finite-scale pressures, the P1 second input MeasurablePressureLimit is
EQUIVALENT to the single convergence statement that the finite pressure family
converges to the measured atlas second-moment pressure.  No other analytic
content remains in the measured pressure formula. -/
theorem measurablePressureLimit_iff_atlasMeasuredPressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q ↔
      AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q :=
  ⟨atlasMeasuredPressureLimit_of_measurablePressureLimit Seed a κ lambda pA α β
      pressure coef probeFam q hPA,
    measurablePressureLimit_of_finitePressureLimit Seed a κ lambda pA α β
      pressure coef probeFam q hPA⟩

/-! ## The sharpest scalar form: the two-sided eventual sandwich -/

/-- **The sharpest scalar form of the single convergence statement.**  The
finite pressures converge to the atlas second-moment pressure exactly when, for
every probe, tilt and comparison level b, they are eventually above b when b lies
below the atlas pressure and eventually below b when b lies above it.  This is
the order-theoretic characterization of convergence and the exact form of the
paper's sandwich: an eventual lower bound and an eventual upper bound with the
comparison levels ranging over all reals, rather than a fixed epsilon slack. -/
theorem atlasMeasuredPressureLimit_iff_eventually_bounds
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q ↔
      ((∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          b < populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t →
            ∀ᶠ R in atTop, b < pressure φ R t) ∧
        (∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t < b →
            ∀ᶠ R in atTop, pressure φ R t < b)) := by
  constructor
  · intro h
    constructor
    · intro φ t b hb
      have hh := tendsto_order.1 (h φ t)
      exact hh.1 b hb
    · intro φ t b hb
      have hh := tendsto_order.1 (h φ t)
      exact hh.2 b hb
  · rintro ⟨hlo, hhi⟩ φ t
    exact tendsto_order.2 ⟨fun b hb => hlo φ t b hb, fun b hb => hhi φ t b hb⟩

/-- The P1 second input in the sharpest scalar form: given the lane
identification, it is equivalent to the two-sided eventual sandwich of the
finite pressures against the atlas second-moment pressure. -/
theorem measurablePressureLimit_iff_eventually_bounds
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q ↔
      ((∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          b < populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t →
            ∀ᶠ R in atTop, b < pressure φ R t) ∧
        (∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
          populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t < b →
            ∀ᶠ R in atTop, pressure φ R t < b)) :=
  (measurablePressureLimit_iff_atlasMeasuredPressureLimit Seed a κ lambda pA α β
    pressure coef probeFam q hPA).trans
    (atlasMeasuredPressureLimit_iff_eventually_bounds Seed a κ lambda α β
      pressure coef probeFam q)

/-! ## The rootwise a.e. equality and the gluing step, recorded locally -/

/-- The rootwise focal-value equality almost everywhere: at every probe and root
the weighted and second-moment stationary pressures coincide at almost every
population root, for every tilt.  This is the a.e. form of
PerRootFocalValueEquality and is strictly weaker than it. -/
def RootwiseAeFocalValueEquality
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

/-- The pointwise rootwise focal-value equality implies the almost-everywhere
form. -/
theorem rootwiseAeFocalValueEquality_of_perRootFocalValueEquality
    (hRoot : PerRootFocalValueEquality α β coef probeFam) :
    RootwiseAeFocalValueEquality Seed a κ lambda α β coef probeFam :=
  perRootFocalValueEqualityAe_of_perRootFocalValueEquality hRoot

/-- In the uniformly elliptic regime the almost-everywhere rootwise focal-value
equality is unconditional, by the repository rootwise equality theorem. -/
theorem rootwiseAeFocalValueEquality_of_uniform_elliptic
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
    RootwiseAeFocalValueEquality Seed a κ lambda α β coef probeFam :=
  rootwiseAeFocalValueEquality_of_perRootFocalValueEquality
    (perRootFocalValueEquality_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound)

/-- The gluing integral step in its almost-everywhere form: under the rootwise
a.e. focal-value equality the measured population pressure equals the
Campbell-averaged stationary pressure.  Only the a.e. root equality is used, by
integral and sum congruence. -/
theorem populationSecondMomentPressure_eq_campbellAveraged_of_rootwiseAe
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hRoot : RootwiseAeFocalValueEquality Seed a κ lambda α β coef probeFam)
    (φ : FinalProbeSpace A B) (t : ℝ) :
    populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t =
      campbellAveragedStationaryPressure α β Seed a κ lambda
        (coef φ) (probeFam φ) q t := by
  rw [populationSecondMomentPressure_apply Seed a κ lambda α β coef probeFam q φ t,
    campbellAveragedStationaryPressure_def α β Seed a κ lambda
      (coef φ) (probeFam φ) q t]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards [hRoot φ j] with z hz
  rw [hz (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))]

/-! ## Relation to the neighbouring global input -/

/-- Given the population gluing identity P1 and the almost-everywhere rootwise
focal-value equality, the weighted stationary pressure equals the measured
population second-moment pressure at every probe and tilt. -/
theorem weightedStationaryPressure_eq_populationSecondMomentPressure_of_gluing_of_rootwiseAe
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hRoot : RootwiseAeFocalValueEquality Seed a κ lambda α β coef probeFam) :
    ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      weightedStationaryPressure α β (Ag φ) (fg φ) t =
        populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t := by
  intro φ t
  rw [hP1 φ t]
  exact (populationSecondMomentPressure_eq_campbellAveraged_of_rootwiseAe
    Seed a κ lambda α β coef probeFam q hRoot φ t).symm

/-- **The measured pressure limit is equivalent to the global focal-value
equality**, given the population gluing identity and the a.e. rootwise equality:
both are the same chain I_w = p_A = P_2 read in one direction or the other.  So
P1's two global inputs are not independent. -/
theorem measurablePressureLimit_iff_focalValueEquality_of_gluing_and_rootwiseAe
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (α β : Measure OTSelector.UnitMark)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hRoot : RootwiseAeFocalValueEquality Seed a κ lambda α β coef probeFam) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q ↔
      FocalValueEquality pA Ag fg α β := by
  constructor
  · intro hLimit φ t
    rw [hLimit φ t]
    exact weightedStationaryPressure_eq_populationSecondMomentPressure_of_gluing_of_rootwiseAe
      Seed a κ lambda α β Ag fg coef probeFam q hP1 hRoot φ t
  · intro hFocal φ t
    exact (hFocal φ t).symm.trans
      (weightedStationaryPressure_eq_populationSecondMomentPressure_of_gluing_of_rootwiseAe
        Seed a κ lambda α β Ag fg coef probeFam q hP1 hRoot φ t)

/-- The single convergence statement is equivalent to the global focal-value
equality, given the lane identification, the population gluing identity and the
a.e. rootwise equality. -/
theorem atlasMeasuredPressureLimit_iff_focalValueEquality_of_gluing_and_rootwiseAe
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q)
    (hRoot : RootwiseAeFocalValueEquality Seed a κ lambda α β coef probeFam) :
    AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q ↔
      FocalValueEquality pA Ag fg α β :=
  (measurablePressureLimit_iff_atlasMeasuredPressureLimit Seed a κ lambda pA α β
    pressure coef probeFam q hPA).symm.trans
    (measurablePressureLimit_iff_focalValueEquality_of_gluing_and_rootwiseAe
      Seed a κ lambda pA Ag fg coef probeFam q α β hP1 hRoot)

/-- In the uniformly elliptic regime the rootwise step is proved by the
repository, so the measured pressure limit is equivalent to the global
focal-value equality given only the population gluing identity P1. -/
theorem measurablePressureLimit_iff_focalValueEquality_of_gluing_of_uniform_elliptic
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (α β : Measure OTSelector.UnitMark)
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (hP1 : PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q ↔
      FocalValueEquality pA Ag fg α β := by
  have hRoot : RootwiseAeFocalValueEquality Seed a κ lambda α β coef probeFam :=
    rootwiseAeFocalValueEquality_of_uniform_elliptic coef probeFam c C hc
      hA_meas hA_low hA_bound
  exact measurablePressureLimit_iff_focalValueEquality_of_gluing_and_rootwiseAe
    Seed a κ lambda pA Ag fg coef probeFam q α β hP1 hRoot

end OTSelector.Reconstruction