import OTSelector.Reconstruction.FinslerOriginalReadoutGlue

/-!
# Frozen Campbell readout: reduction to the paper identities

The consumer conjunct hvalue of the actual lane is FrozenCampbellReadout: the
Campbell averaged frozen cost of the frozen cost function equals the weighted
stationary pressure Iw of the probe-indexed datum, at every probe and tilt.

## What is proved here

1. **The Campbell integration is affine in the frozen cost.**  For fixed probe
   and tilt, the Campbell average of a pointwise affine frozen cost
   z |-> g0 z + t g1 z is the corresponding affine combination of the two
   component Campbell averages.  This is the paper's Campbell-formula
   integration step at the atlas level; it needs only integrability on each
   root piece and summability of the two component piece sequences.

2. **The exact frozen intensity case.**  Build the canonical frozen datum whose
   weighted class is a single matching whose kinetic and probe readouts are the
   two component Campbell averages.  Its weighted stationary pressure is
   exactly the affine function K + t P, so by (1) the frozen Campbell readout
   equals the Campbell average of the frozen cost for every probe and tilt.
   This is the case of the paper identity in which the frozen cost is a
   mark-only function integrated against the frozen weighted population
   measure: the stationary value of the frozen matching is its Campbell
   average.  The datum is non-vacuous; its two competitors are the unique
   element of the one-point matching type.

3. **The integration transfer.**  If the weighted stationary pressure of the
   frozen model equals the frozen cost almost everywhere on each root piece,
   then the Campbell averaged stationary pressure equals the Campbell averaged
   frozen cost.  No integrability or summability hypothesis is needed here,
   because the equality holds almost everywhere on the restricted root
   measures.

4. **Reduction of F15 to two paper identities.**  FrozenCampbellReadout
   follows from the population stationary readout identification (the abstract
   stationary pressure of the datum equals the Campbell averaged per-root
   frozen stationary pressure) together with the per-root frozen stationary
   readout identification (the weighted stationary pressure of the frozen model
   at scaled tilt equals the frozen cost).  Both named identities have exact
   types below; they are the paper's focal value equality and pressure limit
   (main.tex thm:general-focal-value-equality, general-gluing-conditional-readout,
   eq:general-finsler-pressure-limit) and the frozen value identification of
   the limiting rooted scene (main.tex prop:highd-measurable-pressure).

The shift cancels outside this readout, so nothing here depends on the probe
shift convention.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Filter
open OTSelector.Geometry OTSelector.PointProcess
open OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {A B : Set M} {W : Type*} {G Cb : ℝ}
  {Seed : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (Seed j).seed.covector.ker} {lambda : Measure Z}

/-! ## 1. The Campbell integration is affine in the frozen cost -/

/-- The Campbell averaged frozen cost is affine in the frozen cost: for a
pointwise affine frozen cost the average is the affine combination of the two
component averages.  Integrability on the root pieces and summability of the
component sequences are the only measure-theoretic inputs. -/
theorem campbellAveragedFrozenCost_affine (q t : ℝ)
    (g0 g1 : Z → ℝ)
    (hint0 : ∀ j, IntegrableOn
      (fun z => populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g0 z)
      (populationSeedRootPiece Seed a κ lambda j) lambda)
    (hint1 : ∀ j, IntegrableOn
      (fun z => populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g1 z)
      (populationSeedRootPiece Seed a κ lambda j) lambda)
    (hsum0 : Summable (fun j => ∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g0 z ∂lambda))
    (hsum1 : Summable (fun j => ∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g1 z ∂lambda)) :
    campbellAveragedFrozenCost Seed a κ lambda (fun z => g0 z + t * g1 z) q =
      campbellAveragedFrozenCost Seed a κ lambda g0 q +
        t * campbellAveragedFrozenCost Seed a κ lambda g1 q := by
  simp only [campbellAveragedFrozenCost_def]
  have hpiece : ∀ j,
      (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * (g0 z + t * g1 z)
          ∂lambda) =
      (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g0 z ∂lambda) +
      t * (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g1 z ∂lambda) := by
    intro j
    have hfun :
        (fun z => populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) *
            (g0 z + t * g1 z)) =
        fun z => populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g0 z +
          t * (populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g1 z) := by
      funext z
      ring
    rw [hfun]
    rw [integral_add (hint0 j) (hint1 j |>.const_mul t)]
    rw [integral_const_mul]
  have hsum1t : Summable (fun j => t * ∫ z in populationSeedRootPiece Seed a κ lambda j,
      populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g1 z ∂lambda) :=
    hsum1.mul_left t
  have hsumt : Summable (fun j =>
      (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g0 z ∂lambda) +
      t * (∫ z in populationSeedRootPiece Seed a κ lambda j,
        populationAtlasTheta Seed a κ lambda j z ^ (-2 / q) * g1 z ∂lambda)) :=
    hsum0.add hsum1t
  simp only [hpiece]
  rw [hsum0.tsum_add hsum1t, tsum_mul_left]

/-! ## 2. The exact frozen intensity case -/

/-- The canonical frozen datum: the weighted class is the single frozen
matching, whose kinetic readout is the Campbell average of the kinetic
component g0 and whose probe readout is the Campbell average of the probe
component g1. -/
noncomputable def frozenCampbellDatum
    (g0 g1 : FinalProbeSpace A B → Z → ℝ) (q G Cb : ℝ)
    (hK0 : ∀ φ, 0 ≤ campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q)
    (hP : ∀ φ, |campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q| ≤ G)
    (hCb : ∀ φ, campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q ≤ Cb) :
    FinalProbeSpace A B → StationaryPressureDatum PUnit G Cb :=
  fun φ =>
    { K := fun _ => campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q
      P := fun _ => campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q
      Cw := Set.univ
      C2 := Set.univ
      C2_subset_Cw := Set.subset_univ _
      kinetic_nonneg := fun _ _ => hK0 φ
      probe_bound := fun _ _ => hP φ
      competitor := PUnit.unit
      competitor_mem := Set.mem_univ _
      kinetic_competitor_le := hCb φ
      competitor2 := PUnit.unit
      competitor2_mem := Set.mem_univ _
      kinetic_competitor2_le := hCb φ }

/-- The weighted stationary pressure of the canonical frozen datum is affine in
the tilt, with the two component Campbell averages as coefficients. -/
theorem frozenCampbellDatum_Iw
    (g0 g1 : FinalProbeSpace A B → Z → ℝ) (q G Cb : ℝ)
    (hK0 : ∀ φ, 0 ≤ campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q)
    (hP : ∀ φ, |campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q| ≤ G)
    (hCb : ∀ φ, campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q ≤ Cb)
    (φ : FinalProbeSpace A B) (t : ℝ) :
    (frozenCampbellDatum (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) g0 g1 q G Cb hK0 hP hCb φ).Iw t =
      campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q +
        t * campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q := by
  unfold StationaryPressureDatum.Iw
  show sInf ((fun _ : PUnit =>
      campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q +
        t * campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q) '' Set.univ) =
    campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q +
      t * campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q
  rw [Set.univ_nonempty.image_const]
  exact csInf_singleton _

/-- **Exact frozen intensity case of FrozenCampbellReadout.**  If the frozen
cost is the pointwise affine mark-only function z |-> g0 z + t g1 z, and the
datum is the canonical frozen datum of the two component Campbell averages,
then the frozen Campbell readout identification holds: the Campbell average of
the frozen cost is the weighted stationary pressure of the frozen matching. -/
theorem frozenCampbellReadout_frozenCampbellDatum
    (g : FinalProbeSpace A B → ℝ → Z → ℝ)
    (g0 g1 : FinalProbeSpace A B → Z → ℝ) (q G Cb : ℝ)
    (hfac : ∀ (φ : FinalProbeSpace A B) (t : ℝ) (z : Z),
      g φ t z = g0 φ z + t * g1 φ z)
    (hlin : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      campbellAveragedFrozenCost Seed a κ lambda
          (fun z => g0 φ z + t * g1 φ z) q =
        campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q +
          t * campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q)
    (hK0 : ∀ φ, 0 ≤ campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q)
    (hP : ∀ φ, |campbellAveragedFrozenCost Seed a κ lambda (g1 φ) q| ≤ G)
    (hCb : ∀ φ, campbellAveragedFrozenCost Seed a κ lambda (g0 φ) q ≤ Cb) :
    FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) g q
      (frozenCampbellDatum (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) g0 g1 q G Cb hK0 hP hCb) := by
  intro φ t
  rw [frozenCampbellDatum_Iw]
  have hgt : g φ t = fun z => g0 φ z + t * g1 φ z := funext (hfac φ t)
  rw [hgt, hlin φ t]

/-! ## 3. The integration transfer -/

/-- If the weighted stationary pressure of the frozen model equals the frozen
cost almost everywhere on every root piece, then the Campbell averaged
stationary pressure equals the Campbell averaged frozen cost.  This is the
Campbell-formula integration step, with no integrability hypothesis needed
because the equality is almost sure on the restricted root measures. -/
theorem campbellAveragedStationaryPressure_eq_campbellAveragedFrozenCost_of_ae
    (α β : Measure UnitMark)
    (coef : ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (g : Z → ℝ) {q t : ℝ}
    (hpt : ∀ j, ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
      weightedStationaryPressure α β (coef j z) (probeFam j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) = g z) :
    campbellAveragedStationaryPressure α β Seed a κ lambda coef probeFam q t =
      campbellAveragedFrozenCost Seed a κ lambda g q := by
  rw [campbellAveragedStationaryPressure_def, campbellAveragedFrozenCost_def]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards [hpt j] with z hz
  rw [hz]

/-! ## 4. Reduction of FrozenCampbellReadout to the two paper identities -/

/-- **(N1) The population stationary readout identification.**  The abstract
weighted stationary pressure of the probe-indexed datum equals the Campbell
averaged per-root frozen stationary pressure.  This is the population-level
pressure identification of the paper: weighted value recovery together with
the pressure limit and the measurable frozen pressure formula. -/
def AtlasStationaryPressureIdentification
    (α β : Measure UnitMark)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ), (datum φ).Iw t =
    campbellAveragedStationaryPressure α β Seed a κ lambda (coef φ) (probeFam φ) q t

/-- **(N2) The per-root frozen stationary readout identification.**  At every
root and almost every intensity, the weighted stationary pressure of the frozen
model at the scaled tilt equals the frozen cost.  This is the frozen value
identification of the limiting rooted scene, i.e. Campbell's formula applied to
the frozen intensity-theta(z) model. -/
def FrozenStationaryPressureIdentification
    (g : FinalProbeSpace A B → ℝ → Z → ℝ)
    (α β : Measure UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) : Prop :=
  ∀ (φ : FinalProbeSpace A B) (t : ℝ) (j : ℕ),
    ∀ᵐ z ∂(lambda.restrict (populationSeedRootPiece Seed a κ lambda j)),
      weightedStationaryPressure α β ((coef φ) j z) ((probeFam φ) j z)
        (t * populationAtlasTheta Seed a κ lambda j z ^ (2 / q)) = g φ t z

/-- **Reduction of FrozenCampbellReadout.**  The frozen Campbell readout follows
from the population stationary readout identification (N1) and the per-root
frozen stationary readout identification (N2), the integration transfer being
proved above. -/
theorem frozenCampbellReadout_of_identifications
    (g : FinalProbeSpace A B → ℝ → Z → ℝ) (q : ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (α β : Measure UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (hAtlas : AtlasStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) α β datum coef probeFam q)
    (hFrozen : FrozenStationaryPressureIdentification (Seed := Seed) (a := a)
      (κ := κ) (lambda := lambda) g α β coef probeFam q) :
    FrozenCampbellReadout (Seed := Seed) (a := a) (κ := κ) (lambda := lambda) g q datum := by
  intro φ t
  rw [hAtlas φ t]
  exact (campbellAveragedStationaryPressure_eq_campbellAveragedFrozenCost_of_ae
    α β (coef φ) (probeFam φ) (g φ t) (hFrozen φ t)).symm

end OTSelector.Reconstruction