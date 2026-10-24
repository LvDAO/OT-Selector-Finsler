import OTSelector.Reconstruction.FinslerOriginalAtlasStationaryIdentificationFromPressureLimit

/-!
# The two-sided sandwich form of the measured pressure limit

The single remaining analytic input of the population focal-value chain P1 is
MeasurablePressureLimit of FinslerOriginalPopulationFocalValue: the legal
finite-scale pressure limit pA equals the measured population second-moment
pressure, i.e. the atlas sum of the frozen per-root second-moment pressures at
the scaled tilt.  FinslerOriginalAtlasStationaryIdentificationFromPressureLimit
proved that this input is equivalent to the population stationary readout
identification N1, and reduced both to the two-sided eventual sandwich of the
finite-scale pressures against the measured atlas pressure.

This module isolates that sandwich as a single named object and proves the
limit-transfer and squeeze statements that turn it into the paper's theorem:

* PressureLimitSandwich p2 pressure: the sharpest scalar form of the measured
  pressure formula, two one-sided eventual bounds against p2 at every
  comparison level;
* atlasMeasuredPressureLimit_iff_pressureLimitSandwich and
  measurablePressureLimit_iff_pressureLimitSandwich: the P1 input is exactly
  this sandwich (the latter given the lane identification of pA as the finite
  pressure limit, FinitePressureLimitAt);
* atlasStationaryPressureIdentification_iff_pressureLimitSandwich: N1 is
  exactly this sandwich;
* pressureLimitSandwich_of_squeeze: the sandwich follows by the squeeze
  theorem from any pair of envelope families which converge to the measured
  atlas pressure and eventually bracket the finite pressures.  This is the
  paper's sandwich argument, reduced to the pointwise bracket and the two
  convergence statements;
* measurablePressureLimit_of_squeeze and
  populationFocalValueLimit_of_squeeze: the P1 input and P1 itself from the
  squeeze data;
* exists_finitePressureLimitAt_of_forall_exists_limit and
  finitePressureLimitAt_unique: the repository finite pressure limit theorem
  (block subadditivity: exists_tendsto_of_block_subadditive_of_tiltError and
  exists_legalMarkedScalePressure_limit_of_scalarBins) supplies existence of the
  limit for every probe and tilt, hence FinitePressureLimitAt for the family,
  and the limit is unique.

The repository deterministic bounds on the legal marked pressure (the scale
bound and the lower bound of MarkedStationaryValueLegalPressureBound) are not
used: they are crude growing bounds and do not pin the value of the limit.  The
value identity itself, the paper's high-dimensional measured pressure formula,
is exactly what the squeeze input records and is not proved here.

No sorry, admit or added axiom occurs.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Topology Manifold
open OTSelector.Geometry OTSelector.PointProcess OTSelector.Probability
open OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology ContDiff ENNReal NNReal BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {A B : Set M}

/-! ## The sharpest typed limit statement -/

/-- The two-sided eventual sandwich of a finite-scale pressure family against a
target tilt function p2.  This is the order-theoretic form of convergence to p2
and the exact shape of the paper's sandwich proof: for every comparison level b
below p2 the finite pressures are eventually above b, and for every level above
p2 they are eventually below b. -/
def PressureLimitSandwich
    (p2 : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ) : Prop :=
  ((∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
      b < p2 φ t → ∀ᶠ R in atTop, b < pressure φ R t) ∧
    (∀ (φ : FinalProbeSpace A B) (t : ℝ) (b : ℝ),
      p2 φ t < b → ∀ᶠ R in atTop, pressure φ R t < b))

/-- **The measured pressure limit is exactly the named sandwich.** -/
theorem atlasMeasuredPressureLimit_iff_pressureLimitSandwich
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) :
    AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q ↔
      PressureLimitSandwich
        (fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef
          probeFam q φ t) pressure :=
  atlasMeasuredPressureLimit_iff_eventually_bounds Seed a κ lambda α β pressure
    coef probeFam q

/-- **The P1 pressure limit input is exactly the named sandwich**, given the
lane identification of pA as the limit of the finite-scale pressures. -/
theorem measurablePressureLimit_iff_pressureLimitSandwich
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q ↔
      PressureLimitSandwich
        (fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef
          probeFam q φ t) pressure :=
  ((measurablePressureLimit_iff_eventually_bounds Seed a κ lambda pA α β pressure
    coef probeFam q hPA).trans
    (atlasMeasuredPressureLimit_iff_eventually_bounds Seed a κ lambda α β pressure
      coef probeFam q).symm).trans
    (atlasMeasuredPressureLimit_iff_pressureLimitSandwich Seed a κ lambda α β
      pressure coef probeFam q)

/-- **N1 is exactly the named sandwich**, given the datum readout link, the
focal-value equality and the a.e. rootwise gluing. -/
theorem atlasStationaryPressureIdentification_iff_pressureLimitSandwich
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hPA : FinitePressureLimitAt pressure pA) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
        (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q ↔
      PressureLimitSandwich
        (fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef
          probeFam q φ t) pressure :=
  atlasStationaryPressureIdentification_iff_eventually_bounds Seed a κ lambda pA
    pressure α β Ag fg coef probeFam q datum hDatum hFocal hRoot hPA

/-! ## The squeeze: the sandwich from envelope families -/

/-- **The squeeze lemma for the measured pressure limit.**  If two envelope
families bracket the finite-scale pressures eventually at every probe and tilt,
and both converge to the measured atlas second-moment pressure, then the
two-sided sandwich holds.  This is the paper's sandwich argument reduced to the
pointwise bracket and the two convergence statements. -/
theorem pressureLimitSandwich_of_squeeze
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (pressure lower upper : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (hlow : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => lower φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hupp : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => upper φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hsq : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      ∀ᶠ R in atTop, lower φ R t ≤ pressure φ R t ∧ pressure φ R t ≤ upper φ R t) :
    PressureLimitSandwich
      (fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef
        probeFam q φ t) pressure := by
  constructor
  · intro φ t b hb
    have h1 : ∀ᶠ R : ℝ in atTop, b < lower φ R t :=
      (tendsto_order.1 (hlow φ t)).1 b hb
    filter_upwards [h1, hsq φ t] with R hR hsqR
    exact lt_of_lt_of_le hR hsqR.1
  · intro φ t b hb
    have h2 : ∀ᶠ R : ℝ in atTop, upper φ R t < b :=
      (tendsto_order.1 (hupp φ t)).2 b hb
    filter_upwards [h2, hsq φ t] with R hR hsqR
    exact lt_of_le_of_lt hsqR.2 hR

/-- **The measured pressure limit from the squeeze data.** -/
theorem atlasMeasuredPressureLimit_of_squeeze
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (α β : Measure OTSelector.UnitMark)
    (pressure lower upper : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hlow : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => lower φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hupp : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => upper φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hsq : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      ∀ᶠ R in atTop, lower φ R t ≤ pressure φ R t ∧ pressure φ R t ≤ upper φ R t) :
    AtlasMeasuredPressureLimit Seed a κ lambda α β pressure coef probeFam q :=
  (atlasMeasuredPressureLimit_iff_pressureLimitSandwich Seed a κ lambda α β
    pressure coef probeFam q).mpr
    (pressureLimitSandwich_of_squeeze Seed a κ lambda α β coef probeFam q pressure
      lower upper hlow hupp hsq)

/-- **The P1 pressure limit input from the squeeze data**, given the lane
identification of pA as the finite pressure limit. -/
theorem measurablePressureLimit_of_squeeze
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure lower upper : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA)
    (hlow : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => lower φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hupp : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => upper φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hsq : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      ∀ᶠ R in atTop, lower φ R t ≤ pressure φ R t ∧ pressure φ R t ≤ upper φ R t) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q :=
  (measurablePressureLimit_iff_pressureLimitSandwich Seed a κ lambda pA pressure
    α β coef probeFam q hPA).mpr
    (pressureLimitSandwich_of_squeeze Seed a κ lambda α β coef probeFam q pressure
      lower upper hlow hupp hsq)

/-- **The P1 pressure limit input from the repository limit theorem and the
squeeze data.**  The repository finite pressure limit theorem yields, for every
probe and tilt, the limit of the finite-scale pressures; that is exactly the
FinitePressureLimitAt hypothesis. -/
theorem measurablePressureLimit_of_tendsto_of_squeeze
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure lower upper : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hpA : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => pressure φ R t) atTop (𝓝 (pA φ t)))
    (hlow : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => lower φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hupp : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => upper φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hsq : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      ∀ᶠ R in atTop, lower φ R t ≤ pressure φ R t ∧ pressure φ R t ≤ upper φ R t) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q :=
  measurablePressureLimit_of_squeeze Seed a κ lambda pA pressure lower upper α β
    coef probeFam q hpA hlow hupp hsq

/-! ## The repository limit theorem supplies the lane identification -/

/-- **Existence of the finite pressure limit for a family**, as supplied by the
repository limit theorem: if every probe and tilt has a limit, the family has a
FinitePressureLimitAt lane identification. -/
theorem exists_finitePressureLimitAt_of_forall_exists_limit
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (h : ∀ (φ : FinalProbeSpace A B) (t : ℝ), ∃ a : ℝ,
      Tendsto (fun R : ℝ => pressure φ R t) atTop (𝓝 a)) :
    ∃ pA : FinalProbeSpace A B → ℝ → ℝ, FinitePressureLimitAt pressure pA := by
  classical
  exact ⟨fun φ t => Classical.choose (h φ t),
    fun φ t => Classical.choose_spec (h φ t)⟩

/-- The lane identification pA is unique: the finite pressure limit determines
it. -/
theorem finitePressureLimitAt_unique
    {pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ}
    {pA pA' : FinalProbeSpace A B → ℝ → ℝ}
    (h : FinitePressureLimitAt pressure pA)
    (h' : FinitePressureLimitAt pressure pA') : pA = pA' := by
  funext φ t
  exact tendsto_nhds_unique (h φ t) (h' φ t)

/-! ## N1 and P1 from the squeeze -/

/-- **N1 from the squeeze data.**  Given the datum readout link, the
focal-value equality, the a.e. rootwise gluing, the lane identification and the
envelope squeeze, the population stationary readout identification holds. -/
theorem atlasStationaryPressureIdentification_of_squeeze
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure lower upper : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) {W : Type*} {G Cb : ℝ}
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (hDatum : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      (datum φ).Iw t = weightedStationaryPressure α β (Ag φ) (fg φ) t)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hPA : FinitePressureLimitAt pressure pA)
    (hlow : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => lower φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hupp : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => upper φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hsq : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      ∀ᶠ R in atTop, lower φ R t ≤ pressure φ R t ∧ pressure φ R t ≤ upper φ R t) :
    AtlasStationaryPressureIdentification (Seed := Seed) (a := a) (κ := κ)
      (lambda := lambda) (W := W) (G := G) (Cb := Cb) α β datum coef probeFam q :=
  (atlasStationaryPressureIdentification_iff_measurablePressureLimit_of_datum
    Seed a κ lambda pA α β Ag fg coef probeFam q datum hDatum hFocal
    hRoot).mpr
    (measurablePressureLimit_of_squeeze Seed a κ lambda pA pressure lower upper
      α β coef probeFam q hPA hlow hupp hsq)

/-- **P1 from the squeeze data with minimal binders.** -/
theorem populationFocalValueLimit_of_squeeze
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure lower upper : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hPA : FinitePressureLimitAt pressure pA)
    (hlow : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => lower φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hupp : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun R : ℝ => upper φ R t) atTop
        (𝓝 (populationSecondMomentPressure Seed a κ lambda α β coef probeFam q φ t)))
    (hsq : ∀ (φ : FinalProbeSpace A B) (t : ℝ),
      ∀ᶠ R in atTop, lower φ R t ≤ pressure φ R t ∧ pressure φ R t ≤ upper φ R t) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_measurablePressureLimit Seed a κ lambda pA Ag fg
    coef probeFam q α β hFocal
    (measurablePressureLimit_of_squeeze Seed a κ lambda pA pressure lower upper
      α β coef probeFam q hPA hlow hupp hsq)
    hRoot

end OTSelector.Reconstruction
