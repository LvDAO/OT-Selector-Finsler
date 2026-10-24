import OTSelector.Reconstruction.FinslerOriginalFrozenLowerDomination
import OTSelector.Reconstruction.FinslerOriginalUpperPressureData
import OTSelector.Reconstruction.FinslerOriginalMeasurablePressureLimitProof

/-!
# The pressure limit sandwich from the repository probability bounds

The residual of the population focal-value chain P1 isolated in
FinslerOriginalMeasurablePressureLimitProof is the two-sided eventual sandwich
PressureLimitSandwich, equivalently the measured pressure limit
MeasurablePressureLimit (given the finite pressure limit identification
FinitePressureLimitAt).  This module supplies the two sides of the sandwich from
the repository probability bounds of the endgame lane.

* The LOWER side is supplied by the F12 lower probability bound, i.e. by
  FinalProbLowerData: the probability that the supported finite-scale pressure
  falls below the lower readout minus eps vanishes.  Together with the
  deterministic lower bound L - M <= V this forces the expectations eventually
  above L - eps (eventually_integral_ge_of_underperformanceProbability, whose
  core is the negative-part deficit estimate).  The paper consumer is
  finalProbLowerData_of_frozen_domination,
  which produce exactly this FinalProbLowerData from the frozen mean
  identification and the paper's unshifted support bound.
* The UPPER side is supplied by the cellwise upper bound data, i.e. by
  FinalProbUpperData of the F18 lane (the hupper field of EndgamePressureData,
  consumed through actualUpperReadout_of_endgamePressureData): the expectations
  of the supported finite-scale pressure are eventually at most the upper
  readout plus eps.

Combining the two sides with the readout identification pressureLower =
pressureUpper (the endgame value identification) gives convergence of the
expected finite-scale pressures to the common readout
(tendsto_expectedSupportedPressure_of_finalData), which is the two-sided
sandwich in sequence form.  The real-scale form PressureLimitSandwich is then
assembled through the sample-size floor (pressureLimitSandwich_of_nat_tendsto),
and the resulting lane identification FinitePressureLimitAt feeds
MeasurablePressureLimit and P1
(measurablePressureLimit_of_pressureSandwich,
populationFocalValueLimit_of_pressureSandwich,
populationFocalValueLimit_of_finalPressureBounds).

The physical estimates hold on the common perturbation interval; the assembled
sandwich is recorded both on that interval (PressureLimitSandwichOnRadius) and
globally under the hypothesis that the radius covers every tilt.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module
  OTSelector.Probability
open OTSelector.Geometry OTSelector.PointProcess
  OTSelector.Geometry.ContinuousFinslerNorm
  OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
  OTSelector.PointProcess.StationaryForwardMatching
open scoped Topology NNReal ENNReal BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The abstract squeeze: a probability lower bound and an upper
expectation bound -/

/-- The negative part of a random variable bounded below by L - M is controlled
by the probability of falling below L - delta. -/
theorem negPart_integral_le_deficit_aux {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {V : Ω → ℝ} (hmV : Measurable V)
    (hV : Integrable V P) {L M δ : ℝ} (hM : 0 ≤ M) (hδ : 0 < δ)
    (hbound : ∀ᵐ ω ∂P, L - M ≤ V ω) :
    (∫ ω, max (-(V ω - L)) 0 ∂P) ≤
      (M + 1) * P.real {ω | V ω < L - δ} + δ := by
  have hE : MeasurableSet {ω | V ω < L - δ} :=
    measurableSet_lt hmV measurable_const
  have hI1 : Integrable (fun ω => max (-(V ω - L)) 0) P :=
    (hV.sub (integrable_const L)).neg.pos_part
  have hpoint : ∀ᵐ ω ∂P, max (-(V ω - L)) 0 ≤
      (M + 1) * (Set.indicator {ω | V ω < L - δ} (fun _ => (1 : ℝ)) ω) + δ := by
    filter_upwards [hbound] with ω hω
    by_cases hlt : V ω < L - δ
    · have hmem : ω ∈ {ω | V ω < L - δ} := hlt
      simp only [Set.indicator_of_mem hmem]
      exact max_le (by linarith) (by linarith)
    · have hmem : ω ∉ {ω | V ω < L - δ} := hlt
      rw [Set.indicator_of_notMem hmem, mul_zero, zero_add]
      exact max_le (by linarith [not_lt.mp hlt]) hδ.le
  have hI2 : Integrable (fun ω => (M + 1) *
      (Set.indicator {ω | V ω < L - δ} (fun _ => (1 : ℝ)) ω) + δ) P :=
    (((integrable_const (1 : ℝ)).indicator hE).const_mul (M + 1)).add
      (integrable_const δ)
  have hmono := integral_mono_ae hI1 hI2 hpoint
  have hright : (∫ ω, (M + 1) *
      (Set.indicator {ω | V ω < L - δ} (fun _ => (1 : ℝ)) ω) + δ ∂P) =
      (M + 1) * P.real {ω | V ω < L - δ} + δ := by
    rw [integral_add (((integrable_const (1 : ℝ)).indicator hE).const_mul (M + 1))
      (integrable_const δ), integral_const_mul, integral_indicator hE,
      integral_const]
    simp [measureReal_def]
  rwa [hright] at hmono

/-- **The lower side of the sandwich in expectation form.**  A probability lower
bound (the probability of underperforming L - eps vanishes) together with the
deterministic lower bound L - M <= V forces the expectations eventually above
L - eps.  This is the F12 lower probability bound read at the level of
expectations. -/
theorem eventually_integral_ge_of_underperformanceProbability
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {V : ∀ n, Ω n → ℝ} (hV : ∀ n, Measurable (V n))
    (hint : ∀ n, Integrable (V n) (P n))
    {L M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n, ∀ᵐ ω ∂P n, L - M ≤ V n ω)
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P n).real {ω | V n ω < L - ε}) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, L - ε ≤ ∫ ω, V n ω ∂P n := by
  intro ε hε
  have hδ : 0 < ε / 3 := by linarith
  have hlim : Tendsto
      (fun n => (M + 1) * (P n).real {ω | V n ω < L - ε / 3}) atTop (𝓝 0) := by
    simpa using (hprob (ε / 3) hδ).const_mul (M + 1)
  have hpr : ∀ᶠ n in atTop,
      (M + 1) * (P n).real {ω | V n ω < L - ε / 3} < ε / 3 :=
    hlim.eventually (Iio_mem_nhds (by linarith))
  filter_upwards [hpr] with n hn
  have hdef := negPart_integral_le_deficit_aux (P n) (hV n) (hint n) hM hδ (hbound n)
  have hdec : (∫ ω, V n ω ∂P n) =
      L + (∫ ω, max (V n ω - L) 0 ∂P n) -
        (∫ ω, max (-(V n ω - L)) 0 ∂P n) := by
    have hi : Integrable (fun ω => V n ω - L) (P n) :=
      (hint n).sub (integrable_const L)
    have hpos : Integrable (fun ω => max (V n ω - L) 0) (P n) := hi.pos_part
    have hneg : Integrable (fun ω => max (-(V n ω - L)) 0) (P n) := hi.neg.pos_part
    have hpoint : (fun ω => V n ω - L) =
        fun ω => max (V n ω - L) 0 - max (-(V n ω - L)) 0 := by
      funext ω
      rcases le_total (V n ω - L) 0 with hx | hx
      · rw [max_eq_right hx, max_eq_left (by linarith)]
        ring
      · rw [max_eq_left hx, max_eq_right (by linarith)]
        ring
    calc (∫ ω, V n ω ∂P n)
        = (∫ ω, (V n ω - L) ∂P n) + L := by
          rw [integral_sub (hint n) (integrable_const L), integral_const]
          simp [measureReal_def]
      _ = ((∫ ω, max (V n ω - L) 0 ∂P n) -
            (∫ ω, max (-(V n ω - L)) 0 ∂P n)) + L := by
          rw [hpoint, integral_sub hpos hneg]
      _ = L + (∫ ω, max (V n ω - L) 0 ∂P n) -
            (∫ ω, max (-(V n ω - L)) 0 ∂P n) := by
          ring
  have hnonneg : 0 ≤ ∫ ω, max (V n ω - L) 0 ∂P n :=
    integral_nonneg fun _ => le_max_right _ _
  linarith

/-! ## 2. The physical finite-scale pressure and its expectation -/

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]

/-- The supported physical finite-scale pressure of the paper at probe f, tilt
t, sample size n and sample point s.  This is the finite-scale pressure family
whose thermodynamic limit is the legal pressure pA. -/
noncomputable def supportedPressureValue
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ) (s : Ω n) : ℝ :=
  finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
    (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
    (fun i => X n i s) (fun i => Y n i s) u
    (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t

/-- The expected finite-scale pressure at sample size n. -/
noncomputable def expectedSupportedPressure
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n))
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (n : ℕ) (f : FinalProbeSpace A B) (t : ℝ) : ℝ :=
  ∫ s, supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n s ∂P n

/-! ## 3. The two sides of the sandwich from the repository bounds -/

/-- **The UPPER side of the sandwich is the cellwise upper bound data.**  The F18
upper expectation localization FinalProbUpperData (the hupper field of
EndgamePressureData) states exactly that the expectation of the supported
finite-scale pressure is eventually at most the upper readout plus eps. -/
theorem finalProbUpperData_upper_side
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureUpper : FinalPressureField A B) (radius : FinalRadiusField A B)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius)
    {f : FinalProbeSpace A B} {t : ℝ} (ht : |t| < radius f) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u n f t ≤
        pressureUpper f t + ε := by
  intro ε hε
  simpa only [expectedSupportedPressure, supportedPressureValue] using
    hupper f t ε ht hε

/-- **The LOWER side of the sandwich is the F12 lower probability bound.**  The
lower probability localization FinalProbLowerData together with the
deterministic lower bound and integrability forces the expectations eventually
above the lower readout minus eps.  The paper producer of the probability
hypothesis is finalProbLowerData_of_frozen_domination (equivalently
finalProbLowerData_of_frozen_domination). -/
theorem finalProbLowerData_lower_side
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureLower : FinalPressureField A B) (radius : FinalRadiusField A B)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    {f : FinalProbeSpace A B} {t : ℝ} (ht : |t| < radius f)
    {Mbd : ℝ} (hMbd : 0 ≤ Mbd)
    (hbound : ∀ n, ∀ᵐ s ∂P n,
      pressureLower f t - Mbd ≤
        supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n s)
    (hV : ∀ n, Measurable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n))
    (hint : ∀ n, Integrable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n) (P n)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      pressureLower f t - ε ≤
        expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u n f t := by
  intro ε hε
  have hprob' : ∀ δ : ℝ, 0 < δ → Tendsto (fun n =>
      (P n).real {s | supportedPressureValue F μ ν hA hB hμA hνB X Y u
        f t n s < pressureLower f t - δ}) atTop (𝓝 0) := by
    intro δ hδ
    simpa only [supportedPressureValue] using hprob f t δ ht hδ
  exact eventually_integral_ge_of_underperformanceProbability P hV hint hMbd
    hbound hprob' ε hε

/-- **The two-sided sandwich in sequence form.**  The F12 lower probability
bound and the F18 cellwise upper bound, together with the endgame value
identification pressureLower = pressureUpper, the deterministic lower bound and
integrability, give convergence of the expected finite-scale pressures to the
common readout. -/
theorem tendsto_expectedSupportedPressure_of_finalData
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius)
    (Mbd : FinalProbeSpace A B → ℝ → ℝ) (hMbd : ∀ f t, 0 ≤ Mbd f t)
    (hvalue : ∀ f t, pressureLower f t = pressureUpper f t)
    (hbound : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      pressureLower f t - Mbd f t ≤
        supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n s)
    (hV : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Measurable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n))
    (hint : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Integrable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n) (P n)) :
    ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
      Tendsto (fun n => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u n f t)
        atTop (𝓝 (pressureLower f t)) := by
  intro f t ht
  rw [tendsto_order]
  constructor
  · intro b hb
    have hε : 0 < (pressureLower f t - b) / 2 := by linarith
    filter_upwards [finalProbLowerData_lower_side F μ ν hA hB hμA hνB P X Y u
      pressureLower radius hprob ht (hMbd f t) (fun n => hbound f t n)
      (fun n => hV f t n) (fun n => hint f t n) ((pressureLower f t - b) / 2) hε]
      with n hn
    linarith
  · intro b hb
    have hε : 0 < (b - pressureLower f t) / 2 := by linarith
    filter_upwards [finalProbUpperData_upper_side F μ ν hA hB hμA hνB P X Y u
      pressureUpper radius hupper ht ((b - pressureLower f t) / 2) hε] with n hn
    have hv := hvalue f t
    linarith

/-! ## 4. The real-scale sandwich -/

/-- The two-sided sandwich on the common perturbation interval.  The physical
estimates are available only on that interval; off it the readouts follow the
paper's convention. -/
def PressureLimitSandwichOnRadius {A B : Set M}
    (radius : FinalRadiusField A B)
    (p2 : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ) : Prop :=
  ((∀ (f : FinalProbeSpace A B) (t : ℝ) (b : ℝ), |t| < radius f →
      b < p2 f t → ∀ᶠ R in atTop, b < pressure f R t) ∧
    (∀ (f : FinalProbeSpace A B) (t : ℝ) (b : ℝ), |t| < radius f →
      p2 f t < b → ∀ᶠ R in atTop, pressure f R t < b))

/-- **The real-scale sandwich from a sequence limit**, through the sample-size
floor: a nat-indexed two-sided limit of pressures gives the real-scale
PressureLimitSandwich for the floor-indexed family. -/
theorem pressureLimitSandwich_of_nat_tendsto {A B : Set M}
    {pA : FinalProbeSpace A B → ℝ → ℝ}
    {pressure : FinalProbeSpace A B → ℕ → ℝ → ℝ}
    (h : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun n : ℕ => pressure f n t) atTop (𝓝 (pA f t))) :
    PressureLimitSandwich pA (fun f R t => pressure f ⌊R⌋₊ t) := by
  have hfloor : Tendsto (fun R : ℝ => ⌊R⌋₊) atTop atTop := tendsto_nat_floor_atTop
  constructor
  · intro f t b hb
    exact (tendsto_order.1 ((h f t).comp hfloor)).1 b hb
  · intro f t b hb
    exact (tendsto_order.1 ((h f t).comp hfloor)).2 b hb

/-- The lane identification: the floor-indexed real-scale family has the
sequence limit as its finite pressure limit. -/
theorem finitePressureLimitAt_of_nat_tendsto {A B : Set M}
    {pA : FinalProbeSpace A B → ℝ → ℝ}
    {pressure : FinalProbeSpace A B → ℕ → ℝ → ℝ}
    (h : ∀ (f : FinalProbeSpace A B) (t : ℝ),
      Tendsto (fun n : ℕ => pressure f n t) atTop (𝓝 (pA f t))) :
    FinitePressureLimitAt (fun f R t => pressure f ⌊R⌋₊ t) pA :=
  fun f t => (h f t).comp tendsto_nat_floor_atTop

/-- **The sandwich on the perturbation interval from the repository bounds.** -/
theorem pressureLimitSandwichOnRadius_of_finalData
    (F : ContinuousFinslerNorm E M) (μ ν : ProbabilityMeasure M)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius)
    (Mbd : FinalProbeSpace A B → ℝ → ℝ) (hMbd : ∀ f t, 0 ≤ Mbd f t)
    (hvalue : ∀ f t, pressureLower f t = pressureUpper f t)
    (hbound : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      pressureLower f t - Mbd f t ≤
        supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n s)
    (hV : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Measurable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n))
    (hint : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Integrable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n) (P n)) :
    PressureLimitSandwichOnRadius radius (fun f t => pressureLower f t)
      (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
        ⌊R⌋₊ f t) := by
  have h := tendsto_expectedSupportedPressure_of_finalData F μ ν hA hB hμA hνB P
    X Y u pressureLower pressureUpper radius hprob hupper Mbd hMbd hvalue
    hbound hV hint
  have hfloor : Tendsto (fun R : ℝ => ⌊R⌋₊) atTop atTop := tendsto_nat_floor_atTop
  constructor
  · intro f t b ht hb
    exact (tendsto_order.1 ((h f t ht).comp hfloor)).1 b hb
  · intro f t b ht hb
    exact (tendsto_order.1 ((h f t ht).comp hfloor)).2 b hb

/-- If the perturbation radius covers every tilt, the on-radius sandwich is the
global PressureLimitSandwich. -/
theorem pressureLimitSandwich_of_onRadius {A B : Set M}
    {radius : FinalRadiusField A B}
    {p2 : FinalProbeSpace A B → ℝ → ℝ}
    {pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ}
    (hAll : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f)
    (hon : PressureLimitSandwichOnRadius radius p2 pressure) :
    PressureLimitSandwich p2 pressure := by
  obtain ⟨h1, h2⟩ := hon
  exact ⟨fun f t b hb => h1 f t b (hAll f t) hb,
    fun f t b hb => h2 f t b (hAll f t) hb⟩

/-! ## 5. MeasurablePressureLimit and P1 from the sandwich -/

/-- **MeasurablePressureLimit from the sandwich** (and the lane identification
of pA): the batch109 equivalence, applied. -/
theorem measurablePressureLimit_of_pressureSandwich
    {A B : Set M} (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (α β : Measure OTSelector.UnitMark)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ)
    (hPA : FinitePressureLimitAt pressure pA)
    (hsand : PressureLimitSandwich
      (fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef
        probeFam q φ t) pressure) :
    MeasurablePressureLimit Seed a κ lambda pA α β coef probeFam q :=
  (measurablePressureLimit_iff_pressureLimitSandwich Seed a κ lambda pA pressure
    α β coef probeFam q hPA).mpr hsand

/-- **P1 from the sandwich**, with the focal-value equality, the a.e. rootwise
gluing, the lane identification and the sandwich. -/
theorem populationFocalValueLimit_of_pressureSandwich
    {A B : Set M} (F : ContinuousFinslerNorm E M) (u : M → ℝ)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (pA : FinalProbeSpace A B → ℝ → ℝ)
    (pressure : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (hFocal : FocalValueEquality pA Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam)
    (hPA : FinitePressureLimitAt pressure pA)
    (hsand : PressureLimitSandwich
      (fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef
        probeFam q φ t) pressure) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q :=
  populationFocalValueLimit_of_measurablePressureLimit Seed a κ lambda pA Ag fg
    coef probeFam q α β hFocal
    (measurablePressureLimit_of_pressureSandwich F u Seed a κ lambda pA pressure
      α β coef probeFam q hPA hsand)
    hRoot

/-- **P1 from the repository probability bounds and the readout identification.**
The residual list is exactly: the F12 lower probability bound (hprob), the F18
cellwise upper bound (hupper), the endgame value identification
(pressureLower = pressureUpper), the deterministic lower bound, measurability and
integrability of the supported pressure, the covering radius, the readout
identification pressureLower = measured atlas second-moment pressure, the
focal-value equality and the a.e. rootwise gluing.  The finite pressure limit
identification is not assumed: it is produced from the two boundary estimates. -/
theorem populationFocalValueLimit_of_finalPressureBounds
    (F : ContinuousFinslerNorm E M) (A B : Set M)
    (hA : IsCompact A) (hB : IsCompact B)
    (μ ν : ProbabilityMeasure M)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M) (u : M → ℝ)
    (pressureLower pressureUpper : FinalPressureField A B)
    (radius : FinalRadiusField A B)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius)
    (Mbd : FinalProbeSpace A B → ℝ → ℝ) (hMbd : ∀ f t, 0 ≤ Mbd f t)
    (hvalue : ∀ f t, pressureLower f t = pressureUpper f t)
    (hbound : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      pressureLower f t - Mbd f t ≤
        supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n s)
    (hV : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Measurable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n))
    (hint : ∀ (f : FinalProbeSpace A B) (t : ℝ) (n : ℕ), Integrable
      (supportedPressureValue F μ ν hA hB hμA hνB X Y u f t n) (P n))
    (hAll : ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f)
    {Z : Type*} [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
    (Seed : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (Seed j).seed.covector.ker) (lambda : Measure Z)
    (Ag : FinalProbeSpace A B → ℝ → ℝ → ℝ)
    (fg : FinalProbeSpace A B → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (coef : FinalProbeSpace A B → ℕ → Z → ℝ → ℝ → ℝ)
    (probeFam : FinalProbeSpace A B → ℕ → Z →
      MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q : ℝ) (α β : Measure OTSelector.UnitMark)
    (hreadout : ∀ (f : FinalProbeSpace A B) (t : ℝ), pressureLower f t =
      populationSecondMomentPressure Seed a κ lambda α β coef probeFam q f t)
    (hFocal : FocalValueEquality pressureLower Ag fg α β)
    (hRoot : PerRootFocalValueEqualityAe Seed a κ lambda α β coef probeFam) :
    PopulationFocalValueLimit Seed a κ lambda Ag fg α β coef probeFam q := by
  have hon := pressureLimitSandwichOnRadius_of_finalData F μ ν hA hB hμA hνB P
    X Y u pressureLower pressureUpper radius hprob hupper Mbd hMbd hvalue
    hbound hV hint
  have hfull : PressureLimitSandwich (fun f t => pressureLower f t)
      (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
        ⌊R⌋₊ f t) := pressureLimitSandwich_of_onRadius hAll hon
  have hfun : (fun (f : FinalProbeSpace A B) (t : ℝ) => pressureLower f t) =
      fun f t => populationSecondMomentPressure Seed a κ lambda α β coef
        probeFam q f t := by
    funext f t
    exact hreadout f t
  have hsand : PressureLimitSandwich
      (fun φ t => populationSecondMomentPressure Seed a κ lambda α β coef
        probeFam q φ t)
      (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
        ⌊R⌋₊ f t) := by
    rw [← hfun]
    exact hfull
  have hPA : FinitePressureLimitAt
      (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P X Y u
        ⌊R⌋₊ f t) (fun f t => pressureLower f t) :=
    finitePressureLimitAt_of_nat_tendsto (pA := fun f t => pressureLower f t)
      (pressure := fun f n t => expectedSupportedPressure F μ ν hA hB hμA hνB
        P X Y u n f t)
      (fun f t => tendsto_expectedSupportedPressure_of_finalData F μ ν hA hB
        hμA hνB P X Y u pressureLower pressureUpper radius hprob hupper Mbd
        hMbd hvalue hbound hV hint f t (hAll f t))
  exact populationFocalValueLimit_of_pressureSandwich F u Seed a κ lambda
    pressureLower (fun f R t => expectedSupportedPressure F μ ν hA hB hμA hνB P
      X Y u ⌊R⌋₊ f t) Ag fg coef probeFam q α β hFocal hRoot hPA hsand

end OTSelector.Reconstruction
