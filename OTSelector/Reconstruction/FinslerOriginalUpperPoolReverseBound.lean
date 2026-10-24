import OTSelector.Reconstruction.FinslerOriginalUpperPoolDuality
import OTSelector.Reconstruction.FinslerOriginalReadoutGlue
import OTSelector.Limit.FinslerPressureSqueeze

/-!
# The reverse half of the F18 bridge from the paper's two pressure estimates

This module closes the last named input of the actual endgame assembly, the
reverse half of the upper stationary readout

  UpperPoolReverseBound q m pc datum : forall f t,
    (datum f).I2 t <= endgameUpperPressure_actual q m pc f t,

as far as the physical localization data of the paper reach it, and isolates
exactly what remains outside their common perturbation interval.

## What the upper localization in the repository gives

The functional-analytic content of the upper lane is stated in
FinslerOriginalWeightedUpperLocalizationData.  PhysicalWeightedLocalizationFamily
and its specialisation finalProbUpperData_actualPool have the single inequality
direction

  integral of the supported physical pressure  <=  block weighted sum of the
  local marked pressure limits pc  +  eps,

i.e. expected physical pressure <= pool.  This is a statement about the
physical pressure, not about the stationary cost K + t P: the localization
limits of PopData are limits of markedScalePressure (finite-scale marked
expectations), and no theorem in the repository identifies them with the
stationary pressure of any competitor family.  Hence the upper localization
alone is one-sided; it does not compare the pool with the second-moment
infimum.  (This is recorded in FinslerOriginalUpperPoolEnvelope as the
distinction between the upper readout inequality pressure <= pool and the
envelope lower-bound half pool <= K w + t P w, which is proved from weak
duality in FinslerOriginalUpperPoolDuality.)

## The exact paper inequality for the reverse half

In main.tex the reverse half is produced by the two global pressure estimates of
the paper, not by the localization alone:

* Proposition general-gluing-weighted-lower: for every eps > 0 the probability
  that the normalised empirical value V_n(t) is below P_w(t) - eps vanishes;
* Proposition general-gluing-second-moment-upper:
  limsup_n E V_n(t) <= P_2(t);
* the deterministic slack bound V_n(t) >= -|t| ||f||_infinity.

The two estimates together with the slack bound force P_w(t) <= P_2(t) (this is
the paragraph after eq:general-finsler-pressure-limit in main.tex, where the
negative part of V_n relative to the common limit vanishes in mean).  With the
paper's class screening I_w = I_2, and with P_w = I_w, P_2 = pool, this is the
reverse half I_2 <= pool.

The repository already has the two asymptotic inputs as the consumer fields
FinalProbLowerData (the concentration lower bound, pressureLower) and
FinalProbUpperData (the expectation upper bound, pressureUpper), and it has the
slack bound Pressure.supportedDistancePressure_ge_neg_abs_mul.  The missing step
was the elementary measure-theoretic comparison

  bounded below + P(V_n < L - eps) -> 0 + E V_n <= U + eps  implies  L <= U.

That comparison is proved here self-contained
(le_of_probabilityLower_and_integralUpper), then instantiated at the physical
pressure (pressureLower_le_pressureUpper_of_lower_and_upper_data), and finally
composed with the frozen lower readout and the screening identification to give
the reverse bound on the common perturbation interval
(upperPoolReverseBoundOnRadius_of_pressure_data).

## The perturbation interval

Both the lower and the upper data fields are restricted to |t| < radius f: the
physical pressure estimates are only available on that interval, and the local
marked pressure limits pc are constrained by the localization only there.
Off the interval, pc is arbitrary and the localization gives no information; so
the unconditional interface needs the off-interval convention
UpperPoolReverseBoundOffRadius.  The module therefore proves the exact split

  UpperPoolReverseBound  <->  (on the interval) and (off the interval),

and records that the physical content off the interval is a convention on pc,
not a gap in the estimates.  With the lower-bound half proved in
FinslerOriginalUpperPoolDuality this gives the full bridge ActualUpperReadout
once the off-interval convention is supplied, and the envelope once attainment
is supplied.

No sorry, admit or added axiom occurs.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Topology TopologicalSpace
open OTSelector.Geometry OTSelector.Geometry.ContinuousFinslerNorm OTSelector.Probability
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex OTSelector.Pressure Module
open scoped Topology ENNReal NNReal CompactlySupported BoundedContinuousFunction BigOperators

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ⊤ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {μ ν : ProbabilityMeasure M}

/-! ## 1. The abstract comparison of a probability lower bound with an
expectation upper bound -/

/-- max x 0 = x + max (-x) 0. -/
private lemma max_eq_add_max_neg (x : ℝ) : max x 0 = x + max (-x) 0 := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left hx, max_eq_right (by linarith)]
    ring

/-- Pointwise comparison of the negative part with a deficit event: a random
variable bounded below by L - M has its negative part relative to L controlled
by the probability of falling below L - delta. -/
private lemma negPart_integral_le_deficit {Ω : Type*} [MeasurableSpace Ω]
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
      (Set.indicator {ω | V ω < L - δ} (fun _ => (1 : ℝ)) ω) + δ) P := by
    exact (((integrable_const (1 : ℝ)).indicator hE).const_mul (M + 1)).add
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

/-- The abstract comparison: a sequence bounded below whose probability of being
below L - eps vanishes and whose expectations are eventually at most U + eps has
L <= U.  This is the measure-theoretic step of the paper's pressure comparison
(the negative part relative to the limit vanishes in mean). -/
theorem le_of_probabilityLower_and_integralUpper
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (V : ∀ n, Ω n → ℝ) (hV : ∀ n, Measurable (V n))
    (hint : ∀ n, Integrable (V n) (P n))
    {L U M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ n, ∀ᵐ ω ∂P n, L - M ≤ V n ω)
    (hprob : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => (P n).real {ω | V n ω < L - ε}) atTop (𝓝 0))
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∫ ω, V n ω ∂P n ≤ U + ε) :
    L ≤ U := by
  by_contra h
  rw [not_le] at h
  have hd : 0 < L - U := sub_pos.mpr h
  have hδ : 0 < (L - U) / 3 := by positivity
  have hup : ∀ᶠ n in atTop, ∫ ω, V n ω ∂P n ≤ L - 2 * ((L - U) / 3) := by
    filter_upwards [hupper ((L - U) / 3) hδ] with n hn
    linarith
  have hlim : Tendsto (fun n => (M + 1) *
      (P n).real {ω | V n ω < L - (L - U) / 3}) atTop (𝓝 0) := by
    simpa using (hprob ((L - U) / 3) hδ).const_mul (M + 1)
  have hpr : ∀ᶠ n in atTop, (M + 1) *
      (P n).real {ω | V n ω < L - (L - U) / 3} < (L - U) / 3 :=
    hlim.eventually (Iio_mem_nhds hδ)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hup.and hpr)
  have hnup : ∫ ω, V N ω ∂P N ≤ L - 2 * ((L - U) / 3) := (hN N le_rfl).1
  have hnpr : (M + 1) * (P N).real {ω | V N ω < L - (L - U) / 3} < (L - U) / 3 :=
    (hN N le_rfl).2
  have hdeficit := negPart_integral_le_deficit (P N) (hV N) (hint N) hM hδ (hbound N)
  have hdef2 : ∫ ω, max (-(V N ω - L)) 0 ∂P N < 2 * ((L - U) / 3) := by
    have hle : (M + 1) * (P N).real {ω | V N ω < L - (L - U) / 3} +
        (L - U) / 3 < 2 * ((L - U) / 3) := by linarith
    exact lt_of_le_of_lt hdeficit hle
  have hid : (∫ ω, max (V N ω - L) 0 ∂P N) =
      (∫ ω, V N ω ∂P N) - L + ∫ ω, max (-(V N ω - L)) 0 ∂P N := by
    have hsplit : (fun ω => max (V N ω - L) 0) =
        fun ω => (V N ω - L) + max (-(V N ω - L)) 0 := by
      funext ω
      exact max_eq_add_max_neg (V N ω - L)
    rw [hsplit]
    have hi1 : Integrable (fun ω => V N ω - L) (P N) :=
      (hint N).sub (integrable_const L)
    have hi2 : Integrable (fun ω => max (-(V N ω - L)) 0) (P N) :=
      ((hint N).sub (integrable_const L)).neg.pos_part
    rw [integral_add hi1 hi2, integral_sub (hint N) (integrable_const L), integral_const]
    simp
  have hpos : 0 ≤ ∫ ω, max (V N ω - L) 0 ∂P N :=
    integral_nonneg fun _ => le_max_right _ _
  have hlow : L - 2 * ((L - U) / 3) < ∫ ω, V N ω ∂P N := by
    linarith
  linarith

/-! ## 2. The physical pressure comparison at one probe and tilt -/

/-- **The paper pressure comparison in the consumer interface.**  If the lower
consumer field pressureLower is a probability lower bound of the supported
physical pressure and the upper consumer field pressureUpper is an expectation
upper bound, then pressureLower <= pressureUpper at every probe and every tilt
in the common perturbation interval. -/
theorem pressureLower_le_pressureUpper_of_lower_and_upper_data
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instPressureComparison : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    {pressureLower pressureUpper : FinalPressureField A B} {radius : FinalRadiusField A B}
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u pressureUpper radius)
    {f : FinalProbeSpace A B} {t : ℝ} (ht : |t| < radius f) :
    pressureLower f t ≤ pressureUpper f t := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hφc : Continuous u := hφ.continuous
  have hXK (n : ℕ) : ∀ᵐ s ∂P n, ∀ i, X n i s ∈ A ∪ B := by
    apply ae_all_iff.mpr
    intro i
    exact ae_of_ae_map (hX n i).aemeasurable (by
      rw [hXlaw n i]
      exact hμA.mono fun x hx => Or.inl hx)
  have hYK (n : ℕ) : ∀ᵐ s ∂P n, ∀ j, Y n j s ∈ A ∪ B := by
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (hY n j).aemeasurable (by
      rw [hYlaw n j]
      exact hνB.mono fun y hy => Or.inr hy)
  have hkpos (n : ℕ) :
      0 < (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) :=
    Real.rpow_pos_of_pos (by positivity) _
  have hknonneg (n : ℕ) :
      0 ≤ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) :=
    (hkpos n).le
  refine le_of_probabilityLower_and_integralUpper P
    (fun n s => finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
      (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
      (fun i => X n i s) (fun i => Y n i s) u
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (fun n => by
      simpa only [finslerSupportedPressure] using
        (measurable_supportedDistancePressure μ ν (A ∪ B)
          (hA.union hB).measurableSet (hμA.mono fun x hx => Or.inl hx)
          (hνB.mono fun y hy => Or.inr hy) (X n) (Y n) (hX n) (hY n) u hφc
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t))
    (fun n => by
      simpa only [finslerSupportedPressure] using
        (integrable_supportedDistancePressure (P n) μ ν (A ∪ B)
          (hA.union hB).measurableSet (hμA.mono fun x hx => Or.inl hx)
          (hνB.mono fun y hy => Or.inr hy) (X n) (Y n) (hX n) (hY n) u hφ hφc
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
          (Nat.succ_pos n) (hknonneg n) (hA.union hB) (hXK n) (hYK n)))
    (L := pressureLower f t) (U := pressureUpper f t)
    (M := |pressureLower f t| + |t| * (‖f‖₊ : ℝ))
    (by positivity)
    (fun n => by
      filter_upwards [hXK n, hYK n] with s hxs hys
      have hlow : -(|t| * (‖f‖₊ : ℝ)) ≤
          finslerSupportedPressure F μ ν (A ∪ B) (hA.union hB).measurableSet
            (hμA.mono fun x hx => Or.inl hx) (hνB.mono fun y hy => Or.inr hy)
            (fun i => X n i s) (fun i => Y n i s) u
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t := by
        simpa only [finslerSupportedPressure] using
          (supportedDistancePressure_ge_neg_abs_mul μ ν (A ∪ B)
            (hA.union hB).measurableSet (hμA.mono fun x hx => Or.inl hx)
            (hνB.mono fun y hy => Or.inr hy) (Nat.succ_pos n)
            (fun i => X n i s) (fun j => Y n j s) u hφ
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1)))
            (hknonneg n) f t)
      have hLM : pressureLower f t - (|pressureLower f t| + |t| * (‖f‖₊ : ℝ)) ≤
          -(|t| * (‖f‖₊ : ℝ)) := by
        have := le_abs_self (pressureLower f t)
        linarith
      exact hLM.trans hlow)
    (fun ε hε => hprob f t ε ht hε)
    (fun ε hε => hupper f t ε ht hε)

/-! ## 3. The reverse bound on the perturbation interval -/

section PoolReverse

variable {A B : Set M} {W : Type*} {G Cb : ℝ} {q m : ℕ}
  {pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ}
  {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}

/-- Reverse half of the upper pool bridge on the common perturbation interval:
the second-moment readout is at most the block weighted pool for every probe and
tilt with |t| < radius f. -/
def UpperPoolReverseBoundOnRadius (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (radius : FinalRadiusField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), |t| < radius f →
    (datum f).I2 t ≤ endgameUpperPressure_actual q m pc f t

/-- The off-interval convention needed by the unconditional interface: the
localization data constrain the pool only on the perturbation interval, so the
comparison with the second-moment readout off that interval is a convention on
the local limits pc, not a consequence of the estimates. -/
def UpperPoolReverseBoundOffRadius (q m : ℕ)
    (pc : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ)
    (datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb)
    (radius : FinalRadiusField A B) : Prop :=
  ∀ (f : FinalProbeSpace A B) (t : ℝ), radius f ≤ |t| →
    (datum f).I2 t ≤ endgameUpperPressure_actual q m pc f t

/-- **The off-interval part of the reverse bound is always arrangeable.**  Given
the reverse bound on the perturbation interval, there is a modification of the
local limits, equal to them on the interval, for which the unconditional reverse
bound holds.  Off the interval the pool is given the constant value I2 + 1, so
the comparison I2 <= pool is automatic there.  Thus the off-interval part is a
convention on the local limits, not a missing estimate: the localization
constrains them only on the perturbation interval. -/
theorem exists_upperPoolReverseBound_extension_of_onRadius {hm : 0 < m}
    {radius : FinalRadiusField A B}
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius) :
    ∃ pc' : FinalProbeSpace A B → ℝ → (Fin q → Fin m) → ℝ,
      (∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m),
        |t| < radius f → pc' f t c = pc f t c) ∧
      UpperPoolReverseBound q m pc' datum := by
  classical
  refine ⟨fun f t c => if |t| < radius f then pc f t c else (datum f).I2 t + 1, ?_, ?_⟩
  · intro f t c ht
    show (if |t| < radius f then pc f t c else (datum f).I2 t + 1) = pc f t c
    exact ite_eq_left ht
  · intro f t
    by_cases ht : |t| < radius f
    · have hpool : endgameUpperPressure_actual q m
          (fun f t c => if |t| < radius f then pc f t c else (datum f).I2 t + 1) f t =
          endgameUpperPressure_actual q m pc f t := by
        rw [endgameUpperPressure_actual_apply, endgameUpperPressure_actual_apply]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [ite_eq_left ht]
      rw [hpool]
      exact hon f t ht
    · rw [endgameUpperPressure_actual_apply]
      have hsum : (∑ c : Fin q → Fin m,
          (1 / (((m ^ q : ℕ) : ℝ))) *
            (if |t| < radius f then pc f t c else (datum f).I2 t + 1)) =
          (∑ c : Fin q → Fin m,
            (1 / (((m ^ q : ℕ) : ℝ))) * ((datum f).I2 t + 1)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [ite_eq_right ht]
      rw [hsum, sum_blockWeight_mul hm ((datum f).I2 t + 1)]
      linarith

/-- The reverse bound is exactly its perturbation-interval part together with
the off-interval convention. -/
theorem upperPoolReverseBound_of_onRadius_and_offRadius
    {radius : FinalRadiusField A B}
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius)
    (hoff : UpperPoolReverseBoundOffRadius q m pc datum radius) :
    UpperPoolReverseBound q m pc datum := by
  intro f t
  rcases lt_or_ge (|t|) (radius f) with h | h
  · exact hon f t h
  · exact hoff f t h

/-- **The reverse bound from the paper's pressure estimates.**  The upper
localization gives the expectation upper bound for the pool
(finalProbUpperData_actualPool).  The lower consumer field is a probability
lower bound of the same physical pressure (FinalProbLowerData).  The abstract
comparison then gives pressureLower <= pool on the perturbation interval, and
the frozen lower readout together with the screening identification
(Iw = I2) turns this into the reverse half I2 <= pool. -/
theorem upperPoolReverseBoundOnRadius_of_pressure_data
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instPressureComparison : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    {W : Type*} {G Cb : ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {pressureLower : FinalPressureField A B}
    {radius : FinalRadiusField A B}
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hL : LowerStationaryReadout pressureLower datum)
    (hscreen : StationaryScreening datum) :
    UpperPoolReverseBoundOnRadius q m pc datum radius := by
  intro f t ht
  have hupper : FinalProbUpperData F μ ν hA hB hμA hνB P X Y u
      (endgameUpperPressure_actual q m pc) radius :=
    finalProbUpperData_actualPool (q := q) (m := m) hLoc
  have hcmp : pressureLower f t ≤ endgameUpperPressure_actual q m pc f t :=
    pressureLower_le_pressureUpper_of_lower_and_upper_data hA hB hμA hνB
      hcomplete hX hY hXlaw hYlaw hφ hprob hupper ht
  have hIw : (datum f).Iw t = (datum f).I2 t := by
    simpa only [stationaryLowerField, stationaryUpperField] using
      finalValueIdentification_stationaryFields datum hscreen f t
  rw [← hIw, ← hL f t]
  exact hcmp

/-! ## 4. Composition to the actual upper readout -/

/-- **The bridge from the two halves plus the off-interval convention.**  The
lower-bound half is proved in FinslerOriginalUpperPoolDuality from blockwise
weak duality; the reverse half is proved on the perturbation interval above. -/
theorem actualUpperReadout_of_lowerBound_and_reverseBoundOnRadius
    {radius : FinalRadiusField A B}
    (hlow : UpperPoolLowerBound q m pc datum)
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius)
    (hoff : UpperPoolReverseBoundOffRadius q m pc datum radius) :
    ActualUpperReadout q m pc datum :=
  actualUpperReadout_of_lowerBound_and_reverseBound q m pc datum hlow
    (upperPoolReverseBound_of_onRadius_and_offRadius hon hoff)

/-- **The envelope from the two halves plus the off-interval convention plus
attainment.**  This is the strongest form: the envelope also gives the bridge. -/
theorem upperPoolEnvelope_of_lowerBound_and_reverseBoundOnRadius
    {radius : FinalRadiusField A B}
    (hlow : UpperPoolLowerBound q m pc datum)
    (hon : UpperPoolReverseBoundOnRadius q m pc datum radius)
    (hoff : UpperPoolReverseBoundOffRadius q m pc datum radius)
    (hatt : UpperPoolReadoutAttained q m pc datum) :
    UpperPoolEnvelope q m pc datum :=
  (upperPoolEnvelope_iff_lowerBound_and_reverseBound_and_readoutAttained q m pc datum).mpr
    ⟨hlow, upperPoolReverseBound_of_onRadius_and_offRadius hon hoff, hatt⟩

/-- **Full closure of F18 from the paper inputs.**  Blockwise weak duality gives
the lower-bound half (FinslerOriginalUpperPoolDuality), the pressure estimates
give the reverse half on the perturbation interval, and the off-interval
convention extends it.  The result is the actual upper readout bridge for the
pool, i.e. the hU field of the actual endgame assembly. -/
theorem actualUpperReadout_of_blockwiseWeakDuality_and_pressure_data
    (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(μ : Measure M), x ∈ A) (hνB : ∀ᵐ y ∂(ν : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {P : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (P n)]
    {X Y : ∀ n, Fin (n + 1) → Ω n → M}
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hφ : let _instPressureComparison : MetricSpace M := F.metricSpace;
      LipschitzWith 1 u)
    {hm : 0 < m}
    {W : Type*} {G Cb : ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    {pressureLower : FinalPressureField A B}
    {radius : FinalRadiusField A B}
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * π c w)
    (hLoc : PhysicalWeightedLocalizationFamily F μ ν hA hB hμA hνB P X Y u
      (fun _ : Fin q → Fin m => 1 / (((m ^ q : ℕ) : ℝ)))
      (fun f t c => pc f t c) radius)
    (hprob : FinalProbLowerData F μ ν hA hB hμA hνB P X Y u pressureLower radius)
    (hL : LowerStationaryReadout pressureLower datum)
    (hscreen : StationaryScreening datum)
    (hoff : UpperPoolReverseBoundOffRadius q m pc datum radius) :
    ActualUpperReadout q m pc datum :=
  actualUpperReadout_of_blockwiseWeakDuality_and_reverseBound hm pc datum κ π hloc hK hP
    (upperPoolReverseBound_of_onRadius_and_offRadius
      (upperPoolReverseBoundOnRadius_of_pressure_data hA hB hμA hνB hcomplete
        hX hY hXlaw hYlaw hφ hLoc hprob hL hscreen)
      hoff)

/-- **Full closure of the upper pool envelope from the paper inputs.**  Same as
the bridge closure but retaining attainment; no pressure comparison is needed
for this route (attainment already gives the reverse bound). -/
theorem upperPoolEnvelope_of_blockwiseWeakDuality_and_pressure_data
    {hm : 0 < m} {W : Type*} {G Cb : ℝ}
    {datum : FinalProbeSpace A B → StationaryPressureDatum W G Cb}
    (κ π : (Fin q → Fin m) → W → ℝ)
    (hloc : ∀ (f : FinalProbeSpace A B) (t : ℝ) (c : Fin q → Fin m) (w : W),
      w ∈ (datum f).C2 → pc f t c ≤ κ c w + t * π c w)
    (hK : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).K w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * κ c w)
    (hP : ∀ (f : FinalProbeSpace A B) (w : W), w ∈ (datum f).C2 →
      (datum f).P w = ∑ c : Fin q → Fin m,
        (1 / (((m ^ q : ℕ) : ℝ))) * π c w)
    (hatt : UpperPoolAttainment q m pc datum) :
    UpperPoolEnvelope q m pc datum :=
  upperPoolEnvelope_of_blockwiseWeakDuality_and_attainment hm pc datum κ π hloc hK hP hatt

end PoolReverse

end OTSelector.Reconstruction
