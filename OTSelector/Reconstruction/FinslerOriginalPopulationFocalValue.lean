import OTSelector.Reconstruction.FinslerOriginalFocalValueLimit
import OTSelector.Reconstruction.FinslerOriginalLegalPressureValueEquality

/-!
# Population focal-value equality: the paper step decomposition

This module decomposes the population focal-value equality (P1) of the
preceding module into the three steps of the paper, each stated as a typed
Lean proposition, proves every step that follows from the repository, and
proves the composition P1 from the remaining paper-level inputs.

## The chain in the paper

Let pA be the legal maximum-cardinality finite pressure limit readout.  The
paper proves first (main.tex theorem general-focal-value-equality, equation
interleaved-weighted-value-equality, approximately lines 11029 to 11052)

  I_w(t) = I_2(t) = p_A(t),

as an equality of values only, on the original independent marked Poisson
inputs.  Second (equation general-finsler-pressure-limit, approximately lines
11565 to 11582, together with proposition highd-measurable-pressure and
equation highd-measurable-pressure, approximately lines 5442 to 5460) the
finite pressure limit has the measured population form

  p_A(t) = P_psi(t),

where P_psi is the integral over the atlas of theta to the minus two over q
times the frozen unit-intensity pressure at the scaled tilt.  Third (equation
general-gluing-integrated-pressures, approximately lines 11382 to 11399) the
per-root frozen pressures are the stationary pressures of the population
classes, and the rootwise value equality I_w = I_2 of theorem
general-focal-value-equality (rootwise form: equation
general-gluing-relaxation-condition) replaces each per-root second-moment
pressure by the weighted stationary pressure.  This yields the
Campbell-averaged stationary pressure, namely the right-hand side of
campbellAveragedStationaryPressure_def.

## What is proved here

* PerRootFocalValueEquality: the rootwise form of I_w = I_2, the first
  inequality of the displayed chain eq:general-gluing-uniform-pressure-bounds
  plus equality.  The order I_w <= I_2 follows from the repository by class
  monotonicity (weightedStationaryPressure_le_secondMoment_root); the equality
  is equivalent to the paper's rootwise legal screening proposition
  (perRootFocalValueEquality_iff_screening, composing the repository
  value-identification equivalence sInf_image_eq_iff_screening), and it holds
  unconditionally in the uniformly elliptic regime
  (perRootFocalValueEquality_of_uniform_elliptic, composing
  weightedStationaryPressure_eq_secondMoment_of_uniform_elliptic).  The
  quantitative budget form secondMomentStationaryPressure_le_weighted_add_of_budget
  records the exact residual: a uniform rootwise screening budget B bounds the
  value gap I_2 - I_w by B.
* populationSecondMomentPressure: the paper's measured population pressure
  P_2, the atlas integral of the frozen second-moment pressures at the scaled
  tilt (equation general-gluing-integrated-pressures).
* populationSecondMomentPressure_eq_campbellAveraged_of_perRootFocalValueEquality:
  the gluing integral equality.  Under the rootwise value equality the
  measured population pressure is the Campbell-averaged stationary pressure;
  the integral transfer is proved here and only the definitional unfolding of
  the Campbell average is used.
* FocalValueEquality: paper step one, the global equality I_w = p_A, typed as
  a Lean theorem-shaped input with the exact quantifiers.
* MeasurablePressureLimit: paper step two, the measured formula p_A = P_2,
  typed as a Lean theorem-shaped input with the exact quantifiers.
* weightedStationaryPressure_eq_populationSecondMomentPressure: the
  composition I_w = p_A = P_2 of the two theorem-level steps.
* populationFocalValueLimit_of_steps and
  campbellAveragedStationaryPressureIdentification_of_steps: P1 from the
  three steps, so P1 is reduced to the paper's own lemma-level claims.
* populationFocalValueLimit_of_steps_of_uniform_elliptic: in the uniformly
  elliptic regime only the two global theorem-level paper steps remain.

## Remaining paper-level inputs

The two defs FocalValueEquality and MeasurablePressureLimit are the only
analytic inputs of the global lane.  Their paper proofs are the argument
skeleton recorded in the docstrings of the defs: finite classes, strict legal
blocks and the finite pressure of Theorem degenerate-finite-pressure give pA;
legal screening of Proposition general-finite-path-screening gives the reverse
value inequality I_2 <= I_w; block subadditivity and the thermodynamic limit
give convergence of the finite pressures, and clipping with the cell
decomposition of Proposition highd-measurable-pressure gives the measured
formula for the limit.  The rootwise step is reduced here to the paper's
screening proposition and closed unconditionally in the elliptic regime.

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

/-! ## Step one: the rootwise focal-value equality -/

/-- The paper's rootwise focal-value equality (main.tex equation
general-gluing-relaxation-condition and theorem general-focal-value-equality):
at every population root, every atlas probe and every tilt the weighted
stationary pressure equals the second-moment stationary pressure.  This is the
rootwise form of the equality I_w = I_2. -/
def PerRootFocalValueEquality
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (v : ℝ),
    weightedStationaryPressure α β (coef φ j z) (probeFam φ j z) v =
      secondMomentStationaryPressure α β (coef φ j z) (probeFam φ j z) v

/-- The paper's rootwise screening approximation in abstract value-functional
form (main.tex proposition general-finite-path-screening): at every root and
tilt, every finite weighted kinetic stationary matching is approached in value
from above, within every positive tolerance, by a finite-second-moment
stationary matching. -/
def PerRootScreeningApproximates
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (v : ℝ),
    ScreeningApproximates
      (fun Q : StationaryForwardMatching α β =>
        palmKinetic (coef φ j z) Q + v * palmProbe (probeFam φ j z) Q)
      (weightedClass α β (coef φ j z)) (secondMomentClass α β)

/-- A uniform value budget for the screening approximation: every member of the
larger class is matched in value from above by a member of the smaller class
within the budget B. -/
def ScreeningBudget {W : Type*} (V : W → ℝ) (Cw C2 : Set W) (budget : ℝ) : Prop :=
  ∀ Q ∈ Cw, ∃ Q' ∈ C2, V Q' ≤ V Q + budget

/-- The quantitative form of legal screening: a uniform budget B bounds the
value gap of every finite weighted kinetic matching by a finite-second-moment
matching, at every root and tilt. -/
def PerRootScreeningBudget
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ) (budget : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (v : ℝ),
    ScreeningBudget
      (fun Q : StationaryForwardMatching α β =>
        palmKinetic (coef φ j z) Q + v * palmProbe (probeFam φ j z) Q)
      (weightedClass α β (coef φ j z)) (secondMomentClass α β) budget

/-- The value set of the weighted stationary class at one root and tilt is
bounded below: nonnegative kinetic energy and a bounded probe give the
deterministic bound minus abs v times G. -/
theorem bddBelow_weightedValue
    {A : ℝ → ℝ → ℝ} {f : MarkedCloudPoint → MarkedCloudPoint → ℝ} {G v : ℝ}
    (hA_nonneg : ∀ x y, 0 ≤ A x y)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G) :
    BddBelow ((fun Q : StationaryForwardMatching α β =>
      palmKinetic A Q + v * palmProbe f Q) '' weightedClass α β A) :=
  bddBelow_stationaryValue (K := palmKinetic A) (P := palmProbe f)
    (admissible := weightedClass α β A) (G := G) (v := v)
    (fun Q _ => palmKinetic_nonneg hA_nonneg Q)
    (fun Q _ => abs_palmProbe_le hf hfG Q)

/-- The paper's displayed first inequality of the pressure chain, rootwise:
the weighted stationary pressure is at most the second-moment stationary
pressure.  This is unconditional (class monotonicity), the reverse inequality
is the paper's screening content. -/
theorem weightedStationaryPressure_le_secondMoment_root
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {C : FinalProbeSpace A B → ℝ}
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C φ)
    (hf : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (probeFam φ j z) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : MarkedCloudPoint),
      |(probeFam φ j z) x y| ≤ G)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2) :
    ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (v : ℝ),
      weightedStationaryPressure α β (coef φ j z) (probeFam φ j z) v ≤
        secondMomentStationaryPressure α β (coef φ j z) (probeFam φ j z) v := by
  intro φ j z v
  have hsub : secondMomentClass α β ⊆ weightedClass α β (coef φ j z) :=
    fun Q hQ => finiteSecondMoment_subset_finiteWeightedKinetic
      (hA_meas φ j z) (hA_nonneg φ j z) (hA_bound φ j z) hQ
  have hbdd := bddBelow_weightedValue (α := α) (β := β) (A := coef φ j z) (f := probeFam φ j z) (v := v)
    (hA_nonneg := hA_nonneg φ j z) (hf := hf φ j z) (hfG := hfG φ j z)
  have hle := stationaryValue_mono_class
    (K := palmKinetic (coef φ j z)) (P := palmProbe (probeFam φ j z))
    (admissible₁ := weightedClass α β (coef φ j z))
    (admissible₂ := secondMomentClass α β)
    hsub ⟨competitor2, hcompetitor2⟩ hbdd
  simpa only [weightedStationaryPressure, secondMomentStationaryPressure] using hle

/-- The rootwise focal-value equality is exactly the paper's rootwise legal
screening approximation.  This composes the repository value-identification
equivalence sInf_image_eq_iff_screening at each root: no extra analytic content
is hidden in the rootwise step. -/
theorem perRootFocalValueEquality_iff_screening
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {C : FinalProbeSpace A B → ℝ}
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C φ)
    (hf : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (probeFam φ j z) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : MarkedCloudPoint),
      |(probeFam φ j z) x y| ≤ G)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2) :
    PerRootFocalValueEquality α β coef probeFam ↔
      PerRootScreeningApproximates α β coef probeFam := by
  constructor
  · intro h φ j z v
    have hsub : secondMomentClass α β ⊆ weightedClass α β (coef φ j z) :=
      fun Q hQ => finiteSecondMoment_subset_finiteWeightedKinetic
        (hA_meas φ j z) (hA_nonneg φ j z) (hA_bound φ j z) hQ
    have hbdd := bddBelow_weightedValue (α := α) (β := β) (A := coef φ j z) (f := probeFam φ j z) (v := v)
      (hA_nonneg := hA_nonneg φ j z) (hf := hf φ j z) (hfG := hfG φ j z)
    have heq : sInf ((fun Q : StationaryForwardMatching α β =>
          palmKinetic (coef φ j z) Q + v * palmProbe (probeFam φ j z) Q) ''
          weightedClass α β (coef φ j z)) =
        sInf ((fun Q : StationaryForwardMatching α β =>
          palmKinetic (coef φ j z) Q + v * palmProbe (probeFam φ j z) Q) ''
          secondMomentClass α β) := by
      simpa only [weightedStationaryPressure, secondMomentStationaryPressure,
        stationaryValue] using h φ j z v
    exact (sInf_image_eq_iff_screening
      (fun Q : StationaryForwardMatching α β =>
        palmKinetic (coef φ j z) Q + v * palmProbe (probeFam φ j z) Q)
      (weightedClass α β (coef φ j z)) (secondMomentClass α β) hsub
      ⟨competitor2, hcompetitor2⟩ hbdd).mp heq
  · intro h φ j z v
    have hsub : secondMomentClass α β ⊆ weightedClass α β (coef φ j z) :=
      fun Q hQ => finiteSecondMoment_subset_finiteWeightedKinetic
        (hA_meas φ j z) (hA_nonneg φ j z) (hA_bound φ j z) hQ
    have hbdd := bddBelow_weightedValue (α := α) (β := β) (A := coef φ j z) (f := probeFam φ j z) (v := v)
      (hA_nonneg := hA_nonneg φ j z) (hf := hf φ j z) (hfG := hfG φ j z)
    have heq := (sInf_image_eq_iff_screening
      (fun Q : StationaryForwardMatching α β =>
        palmKinetic (coef φ j z) Q + v * palmProbe (probeFam φ j z) Q)
      (weightedClass α β (coef φ j z)) (secondMomentClass α β) hsub
      ⟨competitor2, hcompetitor2⟩ hbdd).mpr (h φ j z v)
    simpa only [weightedStationaryPressure, secondMomentStationaryPressure,
      stationaryValue] using heq

/-- Every positive screening budget is available as soon as the paper's
screening approximation holds at each root. -/
theorem perRootScreeningBudget_of_perRootScreeningApproximates
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {budget : ℝ} (hbudget_pos : 0 < budget)
    (h : PerRootScreeningApproximates α β coef probeFam) :
    PerRootScreeningBudget α β coef probeFam budget := by
  intro φ j z v Q hQ
  obtain ⟨Q', hQ', hlt⟩ := h φ j z v Q hQ budget hbudget_pos
  exact ⟨Q', hQ', le_of_lt hlt⟩

/-- The quantitative screening content: a uniform rootwise budget B bounds the
gap I_2 - I_w by B.  This is the exact value-gap form of the paper's screening
proposition; with B arbitrarily small it recovers the rootwise equality. -/
theorem secondMomentStationaryPressure_le_weighted_add_of_budget
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {C : FinalProbeSpace A B → ℝ}
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_nonneg : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      0 ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C φ)
    (hf : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (probeFam φ j z) p.1 p.2))
    (hfG : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : MarkedCloudPoint),
      |(probeFam φ j z) x y| ≤ G)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    {budget : ℝ} (hbudget : PerRootScreeningBudget α β coef probeFam budget) :
    ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (v : ℝ),
      secondMomentStationaryPressure α β (coef φ j z) (probeFam φ j z) v ≤
        weightedStationaryPressure α β (coef φ j z) (probeFam φ j z) v + budget := by
  intro φ j z v
  have hsub : secondMomentClass α β ⊆ weightedClass α β (coef φ j z) :=
    fun Q hQ => finiteSecondMoment_subset_finiteWeightedKinetic
      (hA_meas φ j z) (hA_nonneg φ j z) (hA_bound φ j z) hQ
  have hbdd := bddBelow_weightedValue (α := α) (β := β) (A := coef φ j z) (f := probeFam φ j z) (v := v)
    (hA_nonneg := hA_nonneg φ j z) (hf := hf φ j z) (hfG := hfG φ j z)
  have hle := sInf_image_le_add_of_screening_le
    (fun Q : StationaryForwardMatching α β =>
      palmKinetic (coef φ j z) Q + v * palmProbe (probeFam φ j z) Q)
    (weightedClass α β (coef φ j z)) (secondMomentClass α β) hsub
    ⟨competitor2, hcompetitor2⟩ hbdd (hbudget φ j z v)
  simpa only [weightedStationaryPressure, secondMomentStationaryPressure,
    stationaryValue] using hle

/-- In the uniformly elliptic regime the rootwise focal-value equality holds
unconditionally: the two stationary classes coincide, so the rootwise step of
the paper is not a separate analytic input there.  This composes the
repository identification weightedStationaryPressure_eq_secondMoment_of_uniform_elliptic. -/
theorem perRootFocalValueEquality_of_uniform_elliptic
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
    PerRootFocalValueEquality α β coef probeFam :=
  fun φ j z v =>
    weightedStationaryPressure_eq_secondMoment_of_uniform_elliptic
      (hA_meas φ j z) hc (hA_low φ j z) (hA_bound φ j z) (probeFam φ j z) v

/-! ## Step three: the gluing integral equality -/

/-- The paper's measured population pressure P_2 (main.tex equation
general-gluing-integrated-pressures and equation highd-measurable-pressure): the
sum over the population atlas pieces of theta to the minus two over q times the
frozen second-moment stationary pressure at the scaled tilt.  This is the
measured pressure formula with the per-root frozen pressure taken in the finite
legal class. -/
noncomputable def populationSecondMomentPressure
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : FinalProbeSpace A B → ℝ → ℝ :=
  fun φ t =>
    ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
        secondMomentStationaryPressure α β (coef φ j z) (probeFam φ j z)
          (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ∂lambda

/-- The defining measured form of the population second-moment pressure. -/
theorem populationSecondMomentPressure_apply
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (φ : FinalProbeSpace A B) (t : ℝ) :
    populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t =
      ∑' j, ∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
          secondMomentStationaryPressure α β (coef φ j z) (probeFam φ j z)
            (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) ∂lambda := rfl

/-- The gluing integral equality: under the rootwise focal-value equality the
measured population pressure is the Campbell-averaged stationary pressure.
Each per-root second-moment pressure in the atlas integral is replaced by the
weighted stationary pressure; the integral transfer is proved here and only
the definitional unfolding of the Campbell average is used.  This is where
equation general-gluing-integrated-pressures meets the rootwise value
equality. -/
theorem populationSecondMomentPressure_eq_campbellAveraged_of_perRootFocalValueEquality
    (hRoot : PerRootFocalValueEquality α β coef probeFam)
    (φ : FinalProbeSpace A B) (t : ℝ) :
    populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t =
      campbellAveragedStationaryPressure α β Seed a κ lambda
        (coef φ) (probeFam φ) q t := by
  rw [campbellAveragedStationaryPressure_def α β Seed a κ lambda
    (coef φ) (probeFam φ) q t]
  unfold populationSecondMomentPressure
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards with z
  rw [hRoot φ j z (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q))]

/-- The gluing integral equality in the uniformly elliptic regime, composing
the elliptic rootwise identification with the integral transfer. -/
theorem populationSecondMomentPressure_eq_campbellAveraged_of_uniform_elliptic
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (φ : FinalProbeSpace A B) (t : ℝ) :
    populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t =
      campbellAveragedStationaryPressure α β Seed a κ lambda
        (coef φ) (probeFam φ) q t :=
  populationSecondMomentPressure_eq_campbellAveraged_of_perRootFocalValueEquality
    (perRootFocalValueEquality_of_uniform_elliptic coef probeFam c C hc hA_meas hA_low hA_bound)
    φ t

/-! ## The paper's theorem-level steps, as typed inputs -/

/-- Paper step one (main.tex theorem general-focal-value-equality and equation
interleaved-weighted-value-equality): the weighted stationary pressure of the
original marked Poisson input equals the legal maximum-cardinality finite
pressure limit pA at every probe and tilt.  The finite pressure pA is the limit
of the legal finite pressures of Theorem degenerate-finite-pressure; its
existence is supplied by the repository legal pressure limit theorem, and the
identification of that limit with the stationary pressure is the paper's
content.

Proof skeleton in the paper: finite strict blocks of the compact conditional
supports give finitely many complete bipartite legal class rectangles; the
legal finite pressure pA is obtained from the finite legal graph data; legal
screening (proposition general-finite-path-screening: reserve density rho
tending to zero, density dilation, whole-path traffic and the Neumann and
Benamou-Brenier transport of the residual ports) builds for every finite
weighted kinetic matching a finite-second-moment competitor with value within
an arbitrary tolerance, so I_2 <= I_w; the reverse order I_w <= I_2 is class
monotonicity, unconditional; hence I_w = I_2; the finite pressure limit
theorem then gives I_2 = pA.  The conclusion is an equality of values only and
does not assert that a weighted minimizer has finite unweighted second moment. -/
def FocalValueEquality
    {A B : Set M}
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (α β : Measure OTSelector.UnitMark) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    weightedStationaryPressure α β (Ag φ) (fg φ) t = pA φ t

/-- Paper step two (main.tex equation general-finsler-pressure-limit together
with proposition highd-measurable-pressure and equation
highd-measurable-pressure): the legal finite pressure limit pA equals the
measured population pressure, namely the atlas sum of theta to the minus two
over q times the frozen per-root second-moment pressure at the scaled tilt.

Proof skeleton in the paper: the finite pressures V_n(t) satisfy a block
subadditivity and a thermodynamic limit; the probability lower bound and the
deterministic bound V_n >= -abs t times the probe norm squeeze the negative
parts, the expectation upper bound squeezes the positive parts, giving
V_n(t) -> P_2(t) in probability and in L^1; clipping removes the residual
energy tail; the high-dimensional measurable pressure proposition integrates
the frozen unit-intensity pressures over the population cells, which is exactly
the measured atlas sum.  Nothing here identifies pA with a stationary
pressure; that is step one. -/
def MeasurablePressureLimit
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ),
    pA φ t = populationSecondMomentPressure Seed a κ lambda
      α β coef probeFam q φ t

/-- Composition of the two theorem-level global steps: the weighted stationary
pressure equals the measured population pressure.  This is the paper's chain
I_w = pA = P_2, with the limit theorem supplied as the typed step and no
analytic work hidden in the composition. -/
theorem weightedStationaryPressure_eq_populationSecondMomentPressure
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      weightedStationaryPressure α β (Ag φ) (fg φ) t =
        populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t := by
  intro φ t
  rw [hFocal φ t, hLimit φ t]

/-! ## The composition: P1 from the paper steps -/

/-- The population focal-value equality P1 from the paper's three steps: the
global focal-value equality I_w = pA, the measured pressure-limit formula
pA = P_2, and the rootwise focal-value equality I_w = I_2 which turns P_2 into
the Campbell-averaged stationary pressure P_w.  No analytic content remains in
the composition: it is the chain I_w = pA = P_2, followed by the gluing
integral equality. -/
theorem populationFocalValueLimit_of_steps
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEquality α β coef probeFam) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q := by
  intro φ t
  rw [hFocal φ t, hLimit φ t,
    ← campbellAveragedStationaryPressure_def α β Seed a κ lambda
      (coef φ) (probeFam φ) q t]
  exact populationSecondMomentPressure_eq_campbellAveraged_of_perRootFocalValueEquality
    hRoot φ t

/-- P1 in the propositional form of the preceding module, from the paper's
three steps. -/
theorem campbellAveragedStationaryPressureIdentification_of_steps
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q)
    (hRoot : PerRootFocalValueEquality α β coef probeFam) :
    CampbellAveragedStationaryPressureIdentification Seed a κ lambda
      Ag fg α β coef probeFam q := by
  intro φ t
  rw [hFocal φ t, hLimit φ t]
  exact populationSecondMomentPressure_eq_campbellAveraged_of_perRootFocalValueEquality
    hRoot φ t

/-- In the uniformly elliptic regime the rootwise step is closed by the
repository, so P1 follows from the two global theorem-level paper steps
alone. -/
theorem populationFocalValueLimit_of_steps_of_uniform_elliptic
    (c C : ℝ) (hc : 0 < c)
    (hA_meas : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z),
      Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
        (coef φ j z) p.1.1 p.2.1))
    (hA_low : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      c ≤ (coef φ j z) x y)
    (hA_bound : ∀ (φ : FinalProbeSpace A B) (j : ℕ) (z : Z) (x y : ℝ),
      (coef φ j z) x y ≤ C)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hLimit : MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_steps pA Ag fg coef probeFam q hFocal hLimit
    (perRootFocalValueEquality_of_uniform_elliptic coef probeFam c C hc hA_meas hA_low hA_bound)

end OTSelector.Reconstruction