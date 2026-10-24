import OTSelector.Limit.FinslerPressureSqueeze
import OTSelector.Probability.GoodEventBounds
import OTSelector.Limit.SupportedPressureConcentration

/-!
# The probability lower bound for the physical Finsler pressure

`OTSelector/Limit/FinslerPressureSqueeze.lean` reduces pointwise convergence of
the physical Dirichlet semidiscrete mean to two asymptotic inputs at a common
value `L = pressure f t`:

* `hprob`, the probability lower bound
  `P (V n < L - eps) -> 0` for every `eps > 0`;
* `hupper`, the expectation upper bound `limsup E V n <= L`,

where `V n` is the supported physical empirical pressure
`finslerSupportedPressure` at the paper's scale `(n+1)^(2/(d-1))`.

This file works on `hprob`.  It does not touch the main declaration chain; it
adds upstream interfaces only.

## Existing lower-bound infrastructure

* `Pressure.supportedDistancePressure_ge_neg_abs_mul`
  (`Limit/PressureLowerBound.lean`): the deterministic pathwise slack bound
  `-|t| * ||f|| <= V n`.  It only makes the sequence bounded below and carries
  no information about the population value `pressure f t`.
* `Probability.markedPressure_lower_bound` and
  `Probability.exists_abs_markedPressure_bound`
  (`Probability/MarkedPressureLimit.lean`): the marked Poisson model obeys
  `-r * |t| * G <= markedPressure <= ...` at intensity `r`; again only a slack
  bound.
* `Probability.tendsto_integral_of_probability_lower_and_integral_upper`
  (`Probability/PressureConvergenceFromBounds.lean`): the abstract engine
  `hprob + hupper => E V n -> L`.
* `Probability.tendsto_measureReal_lt_sub_of_good_event`
  (`Limit/GoodEventBounds.lean`): a pathwise bound `L - eps <= V n` on events
  `G n` with `P (G n)^c -> 0` yields `hprob`.
* `Pressure.tendsto_centered_supportedDistancePressure`
  (`Limit/SupportedPressureConcentration.lean`): unconditional two-sided
  concentration of `V n` about its own mean at scale `(n+1)^(2/q)`,
  `q = d - 1 > 4`, which is exactly the squeeze scale when `d >= 6`.

## The exact remaining gap

No compiled theorem compares `V n` with the population weighted value
`P_w(t) = sum_j int theta_j^s * I_w(z, t theta_j^(2/q)) dz` of `main.tex`,
Proposition `general-gluing-weighted-lower` (lines 7790--7945), and no compiled
theorem proves `P (V n < P_w(t) - eta) -> 0`.  In the paper that proposition is
proved by extracting subsequential rooted-scene limits of actual empirical
optimizers and by dominating one frozen finite-cutoff functional on good sample
events (equation `general-gluing-finite-domination`).  The formalization of
that rooted-scene/point-process analysis is the remaining geometric input; the
measure-theoretic transfer from good events to `hprob` is not a gap.

## What this file proves

1. The strict deficit event `{V < L - eps}` used by the squeeze and the
   `max (L - V) 0` event used by `Limit/SupportedEmpiricalSelector.lean`,
   `Limit/PressureReadout.lean` and `Limit/PressureSelector.lean` are
   interchangeable up to `eps / 2`
   (`tendsto_measureReal_lt_sub_of_measureReal_max_sub` and
   `tendsto_measureReal_max_sub_of_lt_sub`).
2. `hprob` follows from the paper's pathwise good-event statement, both at a
   fixed probe/tilt (`finslerSupportedPressure_probability_lower_of_good_event`)
   and in the exact family shape consumed by the squeeze
   (`finsler_probability_lower_bound_of_good_events`).
3. `hprob` follows from a lower comparison with any model sequence `W n` whose
   own deficit probability vanishes
   (`tendsto_measureReal_lt_sub_of_eventually_lower_model`).  This is the
   abstract form of the paper's finite-domination step
   `Gamma_n(F_{R,N}) <= V n + B_t + o_P(1)` together with the convergence of
   the frozen functional to `P_w(t)`.
4. Because the centred concentration is unconditional, `hprob` follows from an
   *expectation* lower bound `liminf E V n >= L`
   (`finslerSupportedPressure_probability_lower_of_integral_lower`) or from
   mean convergence `E V n -> L`
   (`finslerSupportedPressure_probability_lower_of_tendsto_integral`), with the
   family forms `finsler_probability_lower_bound_of_integral_lower` and
   `finsler_probability_lower_bound_of_tendsto_integral`.  Consequently the
   probability lower bound input of the squeeze can be replaced by an
   expectation-level lower bound; the physical endpoint
   `tendsto_finslerSemidiscreteMean_of_integral_lower_and_integral_upper`
   records this alternative route.
5. The physical endpoint with the paper's pathwise good-event hypothesis in
   place of `hprob`:
   `tendsto_finslerSemidiscreteMean_of_good_event_lower_and_integral_upper`.
6. The paper's **subsequence criterion**: if every subsequence of the scalar
   laws `law (V n)` has a further subsequence converging weakly to a
   probability measure supported on `[L, ∞)`, then `hprob` holds
   (`tendsto_measureReal_lt_sub_of_subseq_weak_limit`; the fixed-probe and
   whole-family Finsler forms are
   `finslerSupportedPressure_probability_lower_of_subseq_weak_limit` and
   `finsler_probability_lower_bound_of_subseq_weak_limit`).  This is the exact
   form in which the rooted-scene compactness, stationarity and Campbell-formula
   analysis of `main.tex` concludes.  The measurability input is discharged by
   `measurable_finslerSupportedPressure`.  The support form
   `finsler_probability_lower_bound_of_subseq_weak_support` takes the cleaner
   hypothesis that every subsequential weak limit is supported on
   `[pressure f t, ∞)` itself.

No `sorry`, `admit`, or added axiom occurs.  Every theorem is a reduction whose
explicit hypotheses are the remaining inputs; nothing here asserts the
population lower value.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace OTSelector.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- The `max (L - V) 0` deficit event used by the selector and readout modules
implies the strict deficit event used by the pressure squeeze, because
`max (L - V) 0 >= eps` forces `V <= L - eps < L - eps / 2`. -/
theorem tendsto_measureReal_lt_sub_of_measureReal_max_sub
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {V : ∀ n, Ω n → ℝ} {L : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (P n).real {x | ε ≤ max (L - V n x) 0}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {x | V n x < L - ε}) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) (h (ε / 2) (by linarith))
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hLV : ε / 2 ≤ L - V n x := by linarith
  exact hLV.trans (le_max_of_le_left le_rfl)

/-- Conversely, the strict deficit event used by the pressure squeeze implies
the `max (L - V) 0` deficit event used by the selector modules. -/
theorem tendsto_measureReal_max_sub_of_lt_sub
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {V : ∀ n, Ω n → ℝ} {L : ℝ}
    (h : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (P n).real {x | V n x < L - ε}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {x | ε ≤ max (L - V n x) 0}) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) (h (ε / 2) (by linarith))
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hLV : ε ≤ L - V n x := by
    rcases le_max_iff.mp hx with h' | h'
    · exact h'
    · linarith
  linarith

/-- **Lower comparison with a model sequence.**  If on good events `G n` the
empirical value is at least the model value `W n` minus a vanishing error
`δ n`, the bad events have vanishing probability, and the model satisfies its
own probability lower bound at `L`, then the empirical value does too.

This is the abstract form of the paper's finite-domination step: `W n` is the
frozen finite-cutoff scene functional whose expectation converges to the
weighted population pressure and whose lower deficit probability is controlled
by the law of large numbers / Campbell formula. -/
theorem tendsto_measureReal_lt_sub_of_eventually_lower_model
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    {V W : ∀ n, Ω n → ℝ} {G : ∀ n, Set (Ω n)} {δ : ℕ → ℝ} {L ε : ℝ}
    (hε : 0 < ε) (hδ : Tendsto δ atTop (𝓝 0))
    (hgood : ∀ n, ∀ x ∈ G n, W n x - δ n ≤ V n x)
    (hbad : Tendsto (fun n ↦ (P n).real ((G n)ᶜ)) atTop (𝓝 0))
    (hW : Tendsto (fun n ↦ (P n).real {x | W n x < L - ε / 2}) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (P n).real {x | V n x < L - ε}) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n ↦ (P n).real ((G n)ᶜ) +
      (P n).real {x | W n x < L - ε / 2}) atTop (𝓝 0) := by
    simpa using hbad.add hW
  have hδev : ∀ᶠ n in atTop, δ n ≤ ε / 2 := by
    exact (hδ.eventually (Iic_mem_nhds (by linarith : (0 : ℝ) < ε / 2))).mono
      fun n hn ↦ hn
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ hsum
  filter_upwards [hδev] with n hn
  calc (P n).real {x | V n x < L - ε}
      ≤ (P n).real ((G n)ᶜ ∪ {x | W n x < L - ε / 2}) := by
        refine measureReal_mono ?_ (measure_ne_top _ _)
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx
        by_cases hG : x ∈ G n
        · right
          simp only [Set.mem_ofPred_eq]
          have h1 : W n x - δ n ≤ V n x := hgood n x hG
          linarith
        · exact Or.inl (by simpa only [Set.mem_compl_iff] using hG)
    _ ≤ (P n).real ((G n)ᶜ) + (P n).real {x | W n x < L - ε / 2} :=
        measureReal_union_le _ _

/-- A one-sided version of centred concentration: lower deviations below the
empirical mean have vanishing probability. -/
theorem tendsto_measureReal_lt_sub_integral_of_centered
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (V : ∀ n, Ω n → ℝ)
    (hcent : ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
      {x | ε ≤ |V n x - ∫ x', V n x' ∂P n|}) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real
      {x | V n x < (∫ x', V n x' ∂P n) - ε}) atTop (𝓝 0) := by
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) (hcent ε hε)
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have hneg : V n x - ∫ x', V n x' ∂P n < 0 := by linarith
  rw [abs_of_neg hneg]
  linarith

/-- The law of a scalar empirical process at sample size `n`: the pushforward of
the sample law under the scalar statistic `V n`. -/
noncomputable def pressureScalarLaw
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (V : ∀ n, Ω n → ℝ) (hV : ∀ n, Measurable (V n)) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨(P n).map (V n), Measure.isProbabilityMeasure_map (hV n).aemeasurable⟩

/-- **Portmanteau step of the subsequence criterion.**  If the scalar laws
converge weakly to a probability measure supported on `[L, ∞)`, then the
deficit probability at `L - ε` vanishes.  The proof is the closed-set
Portmanteau inequality at `Iic (L - ε)`, whose frontier is `{L - ε}` and hence
carries no mass. -/
theorem tendsto_measureReal_lt_sub_of_tendsto_scalarLaw
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (V : ∀ n, Ω n → ℝ) (hV : ∀ n, Measurable (V n))
    {L ε : ℝ} (ν : ProbabilityMeasure ℝ)
    (hν : (ν : Measure ℝ) (Iic (L - ε)) = 0)
    (hlim : Tendsto (fun n ↦ pressureScalarLaw P V hV n) atTop (𝓝 ν)) :
    Tendsto (fun n ↦ (P n).real {x | V n x < L - ε}) atTop (𝓝 0) := by
  have hfront : (ν : Measure ℝ) (frontier (Iic (L - ε))) = 0 := by
    rw [frontier_Iic]
    refine le_antisymm ?_ (by simp)
    calc (ν : Measure ℝ) {L - ε}
        ≤ (ν : Measure ℝ) (Iic (L - ε)) :=
          measure_mono (Set.singleton_subset_iff.mpr (mem_Iic.mpr le_rfl))
      _ = 0 := hν
  have hlimENN : Tendsto (fun n ↦
      ((pressureScalarLaw P V hV n : ProbabilityMeasure ℝ) : Measure ℝ) (Iic (L - ε)))
      atTop (𝓝 0) := by
    have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hlim hfront
    simpa only [hν] using h
  have hlimReal : Tendsto (fun n ↦
      (((pressureScalarLaw P V hV n : ProbabilityMeasure ℝ) : Measure ℝ)
        (Iic (L - ε))).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ⊤)).comp hlimENN
    convert h using 1
    · ext n
      rfl
    · simp
  refine squeeze_zero (fun n ↦ measureReal_nonneg) (fun n ↦ ?_) hlimReal
  have hsub : {x | V n x < L - ε} ⊆ V n ⁻¹' Iic (L - ε) := by
    intro x hx
    show V n x ∈ Iic (L - ε)
    exact mem_Iic.mpr hx.le
  have heq : (P n).real (V n ⁻¹' Iic (L - ε)) =
      (((pressureScalarLaw P V hV n : ProbabilityMeasure ℝ) : Measure ℝ)
        (Iic (L - ε))).toReal := by
    rw [measureReal_def]
    congr 1
    exact (Measure.map_apply (hV n) measurableSet_Iic).symm
  calc (P n).real {x | V n x < L - ε}
      ≤ (P n).real (V n ⁻¹' Iic (L - ε)) := measureReal_mono hsub (measure_ne_top _ _)
    _ = _ := heq

/-- **The subsequence criterion of `main.tex` Proposition
`general-gluing-weighted-lower`.**  If every subsequence of the scalar laws of
the pressure has a further subsequence converging weakly to a probability
measure supported on `[L, ∞)`, then the deficit probability at `L - ε`
vanishes.  This is exactly the form in which the paper's rooted-scene
compactness and Campbell-formula argument concludes. -/
theorem tendsto_measureReal_lt_sub_of_subseq_weak_limit
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (V : ∀ n, Ω n → ℝ) (hV : ∀ n, Measurable (V n))
    {L ε : ℝ} (_hε : 0 < ε)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
        Tendsto (fun k ↦ pressureScalarLaw P V hV (φ (ψ k))) atTop (𝓝 νlim) ∧
        (νlim : Measure ℝ) (Iic (L - ε)) = 0) :
    Tendsto (fun n ↦ (P n).real {x | V n x < L - ε}) atTop (𝓝 0) := by
  by_contra hc
  rw [Metric.tendsto_atTop] at hc
  push Not at hc
  obtain ⟨δ, hδ, hfreq⟩ := hc
  have hfreq' : ∀ N : ℕ, ∃ n > N, δ ≤ (P n).real {x | V n x < L - ε} := by
    intro N
    obtain ⟨n, hnN, hn⟩ := hfreq (N + 1)
    refine ⟨n, Nat.lt_of_succ_le hnN, ?_⟩
    have hdist : dist ((P n).real {x | V n x < L - ε}) 0 =
        (P n).real {x | V n x < L - ε} := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    simpa only [hdist] using hn
  obtain ⟨φ, hφmono, hφle⟩ := Nat.exists_strictMono_subsequence hfreq'
  obtain ⟨ψ, hψmono, ν, hlim, hν⟩ := hsub φ hφmono
  have h0 := tendsto_measureReal_lt_sub_of_tendsto_scalarLaw
    (fun k ↦ P (φ (ψ k))) (fun k ↦ V (φ (ψ k))) (fun k ↦ hV (φ (ψ k)))
    ν hν (by simpa only [pressureScalarLaw] using hlim)
  have hev : ∀ᶠ k in atTop,
      (P (φ (ψ k))).real {x | V (φ (ψ k)) x < L - ε} < δ :=
    h0.eventually (Iio_mem_nhds hδ)
  obtain ⟨k, hk⟩ := hev.exists
  linarith [hφle (ψ k), hk]

/-- The subsequence criterion with the natural support hypothesis: every
subsequential weak limit of the scalar laws is supported on `[L, ∞)` itself. -/
theorem tendsto_measureReal_lt_sub_of_subseq_weak_support
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (V : ∀ n, Ω n → ℝ) (hV : ∀ n, Measurable (V n))
    {L ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
        Tendsto (fun k ↦ pressureScalarLaw P V hV (φ (ψ k))) atTop (𝓝 νlim) ∧
        (νlim : Measure ℝ) (Iio L) = 0) :
    Tendsto (fun n ↦ (P n).real {x | V n x < L - ε}) atTop (𝓝 0) := by
  refine tendsto_measureReal_lt_sub_of_subseq_weak_limit P V hV hε ?_
  intro φ hφ
  obtain ⟨ψ, hψ, νlim, hlim, hν⟩ := hsub φ hφ
  refine ⟨ψ, hψ, νlim, hlim, ?_⟩
  refine le_antisymm ?_ (by simp)
  calc (νlim : Measure ℝ) (Iic (L - ε))
      ≤ (νlim : Measure ℝ) (Iio L) := by
        apply measure_mono
        intro x hx
        simp only [Set.mem_Iic] at hx
        exact Set.mem_Iio.mpr (by linarith)
    _ = 0 := hν

end OTSelector.Probability

namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}

/-- Bridge: the Finsler supported pressure is the ambient supported pressure
under the genuine length-metric space structure. -/
theorem finslerSupportedPressure_eq_supportedDistancePressure
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (X Y : Fin n → M) (φ : M → ℝ) (k : ℝ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    finslerSupportedPressure F μ ν K hK hμ hν X Y φ k f t =
      letI : MetricSpace M := F.metricSpace
      Pressure.supportedDistancePressure μ ν K hK hμ hν X Y φ k f t := rfl

/-- **Unconditional centred concentration of the physical pressure.**  At
dimension `d >= 6` the paper's scale exponent `2/(d-1)` is smaller than `1/2`,
so the normalized empirical supported pressure concentrates about its own
mean. -/
theorem tendsto_centered_finslerSupportedPressure
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {s | ε ≤ |finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t -
      ∫ s', finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s') (fun i ↦ Y n i s') φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n|})
      atTop (𝓝 0) := by
  letI : MetricSpace M := F.metricSpace
  have hq : 4 < ((Module.finrank ℝ E : ℕ) : ℝ) - 1 := by
    have h6 : (6 : ℝ) ≤ ((Module.finrank ℝ E : ℕ) : ℝ) := by exact_mod_cast hdim
    linarith
  have hφc : Continuous φ := hφ
  have h := Pressure.tendsto_centered_supportedDistancePressure (M := M) P μ ν K hK
    hμ hν X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφc
    (((Module.finrank ℝ E : ℕ) : ℝ) - 1) hq f t (ε := ε) hε
  simpa only [finslerSupportedPressure] using h

/-- **Unconditional one-sided lower deviation.**  At dimension `d >= 6` the
physical supported pressure falls below its own mean by more than `ε` only with
vanishing probability. -/
theorem finslerSupportedPressure_tendsto_measureReal_lt_integral
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
      (∫ s', finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s') (fun i ↦ Y n i s') φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) - ε})
      atTop (𝓝 0) := by
  let V : ∀ n, Ω n → ℝ := fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet
    hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
    (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
  have hcent : ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
      {s | ε ≤ |V n s - ∫ s', V n s' ∂P n|}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [V] using
      tendsto_centered_finslerSupportedPressure hdim μ ν K hK hμ hν P X Y hX hY
        hXi hYi hXlaw hYlaw hXY φ hφ f t hε
  simpa only [V] using
    OTSelector.Probability.tendsto_measureReal_lt_sub_integral_of_centered P V hcent hε

/-- **`hprob` from the paper's pathwise good-event bound** at a fixed probe,
tilt and target value. -/
theorem finslerSupportedPressure_probability_lower_of_good_event
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ) (f : (K × K) →ᵇ ℝ) (t L ε : ℝ) (G : ∀ n, Set (Ω n))
    (hgood : ∀ n, ∀ s ∈ G n, L - ε ≤ finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hbad : Tendsto (fun n ↦ (P n).real ((G n)ᶜ)) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t < L - ε})
      atTop (𝓝 0) := by
  let V : ∀ n, Ω n → ℝ := fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet
    hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
    (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
  exact OTSelector.Probability.tendsto_measureReal_lt_sub_of_good_event P V G hgood hbad

/-- **`hprob` from an expectation lower bound.**  Since the centred
concentration of the physical pressure is unconditional at `d >= 6`, the
probability lower bound at `L` follows from the eventual expectation bound
`L - ε / 2 <= E V n`. -/
theorem finslerSupportedPressure_probability_lower_of_integral_lower
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t L : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hlower : ∀ᶠ n in atTop, L - ε / 2 ≤
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) :
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t < L - ε})
      atTop (𝓝 0) := by
  let V : ∀ n, Ω n → ℝ := fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet
    hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
    (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
  have hcent : ∀ ε : ℝ, 0 < ε → Tendsto (fun n ↦ (P n).real
      {s | ε ≤ |V n s - ∫ s', V n s' ∂P n|}) atTop (𝓝 0) := by
    intro ε hε
    simpa only [V] using
      tendsto_centered_finslerSupportedPressure hdim μ ν K hK hμ hν P X Y hX hY
        hXi hYi hXlaw hYlaw hXY φ hφ f t hε
  have hlowV : ∀ᶠ n in atTop, L - ε / 2 ≤ ∫ s, V n s ∂P n := hlower
  have hdev := OTSelector.Probability.tendsto_measureReal_lt_sub_integral_of_centered
    P V hcent (by linarith : (0 : ℝ) < ε / 2)
  refine squeeze_zero' (Eventually.of_forall fun n ↦ measureReal_nonneg) ?_ hdev
  filter_upwards [hlowV] with n hn
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro s hs
  simp only [Set.mem_ofPred_eq] at hs ⊢
  have hge : L - ε / 2 ≤ ∫ s', V n s' ∂P n := hn
  linarith

/-- **`hprob` from mean convergence.**  If the expected physical pressure
converges to `L`, then the probability of a deficit at `L` vanishes. -/
theorem finslerSupportedPressure_probability_lower_of_tendsto_integral
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t L : ℝ)
    (hmean : Tendsto (fun n ↦
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n)
      atTop (𝓝 L))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t < L - ε})
      atTop (𝓝 0) := by
  refine finslerSupportedPressure_probability_lower_of_integral_lower hdim μ ν K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t L hε ?_
  exact (hmean.eventually (Ioi_mem_nhds (by linarith : L - ε / 2 < L))).mono
    fun n hn ↦ hn.le

/-- **The whole `hprob` clause from pathwise good events.**  This is the exact
family shape consumed by `exists_finsler_pressure_producer_of_squeeze`. -/
theorem finsler_probability_lower_bound_of_good_events
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (G : (f : (K × K) →ᵇ ℝ) → ℝ → ℝ → ∀ n, Set (Ω n))
    (hgood : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      ∀ n, ∀ s ∈ G f t ε n, pressure f t - ε ≤ finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hbad : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real ((G f t ε n)ᶜ)) atTop (𝓝 0)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0) := by
  intro f t ε ht hε
  exact finslerSupportedPressure_probability_lower_of_good_event μ ν K hK hμ hν P X Y
    φ f t (pressure f t) ε (G f t ε) (hgood f t ε ht hε) (hbad f t ε ht hε)

/-- **The whole `hprob` clause from a lower comparison with a frozen model.**
This is the exact assembly used by the paper's proof of
`general-gluing-weighted-lower`: on good events `G f t ε n` the physical
pressure is at least the frozen finite-cutoff functional `W f t n` minus a
deterministic vanishing error `δ f t n`, while `W f t n` itself satisfies the
deficit probability bound at the population value `pressure f t`. -/
theorem finsler_probability_lower_bound_of_comparison
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (W : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (δ : (f : (K × K) →ᵇ ℝ) → ℝ → ℕ → ℝ)
    (G : (f : (K × K) →ᵇ ℝ) → ℝ → ℝ → ∀ n, Set (Ω n))
    (hδ : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      Tendsto (fun n ↦ δ f t n) atTop (𝓝 0))
    (hgood : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      ∀ n, ∀ s ∈ G f t ε n, W f t n s - δ f t n ≤ finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hbad : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real ((G f t ε n)ᶜ)) atTop (𝓝 0))
    (hW : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | W f t n s < pressure f t - ε / 2})
        atTop (𝓝 0)) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0) := by
  intro f t ε ht hε
  let V : ∀ n, Ω n → ℝ := fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet
    hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
    (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
  have hgood' : ∀ n, ∀ s ∈ G f t ε n, W f t n s - δ f t n ≤ V n s :=
    fun n s hs ↦ hgood f t ε ht hε n s hs
  have hres := OTSelector.Probability.tendsto_measureReal_lt_sub_of_eventually_lower_model
    P (V := V) (W := fun n s ↦ W f t n s) (G := G f t ε) (δ := δ f t)
    hε (hδ f t ht) hgood' (hbad f t ε ht hε) (hW f t ε ht hε)
  simpa only [V] using hres

/-- **The whole `hprob` clause from expectation lower bounds.**  Replaces the
pathwise probability statement by an expectation-level lower bound at the same
population value. -/
theorem finsler_probability_lower_bound_of_integral_lower
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (hlower : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
        pressure f t - ε ≤ ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet
          hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0) := by
  intro f t ε ht hε
  exact finslerSupportedPressure_probability_lower_of_integral_lower hdim μ ν K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t (pressure f t) hε
    (hlower f t ht (ε / 2) (by linarith))

/-- **The whole `hprob` clause from mean convergence** of the expected physical
pressure. -/
theorem finsler_probability_lower_bound_of_tendsto_integral
    (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (hmean : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      Tendsto (fun n ↦ ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n)
        atTop (𝓝 (pressure f t))) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0) := by
  intro f t ε ht hε
  exact finslerSupportedPressure_probability_lower_of_tendsto_integral hdim μ ν K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t (pressure f t)
    (hmean f t ht) hε

/-- **Physical endpoint with pathwise good events.**  The same conclusion as
`tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper`, with
the probability lower bound replaced by the paper's pathwise bound on good
sample events. -/
theorem tendsto_finslerSemidiscreteMean_of_good_event_lower_and_integral_upper
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 2 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instSqueezeGoodEventPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t L : ℝ)
    (G : ℝ → ∀ n, Set (Ω n))
    (hgood : ∀ ε : ℝ, 0 < ε → ∀ n, ∀ s ∈ G ε n,
      L - ε ≤ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (hbad : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n ↦ (P n).real ((G ε n)ᶜ)) atTop (𝓝 0))
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤ L + ε) :
    Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop (𝓝 L) := by
  refine tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
    hF hcomplete m hdim μ ν hμchart hνchart K hK hμ hν P X Y hX hY hXi hYi
    hXlaw hYlaw hXY φ hφ f t L ?_ hupper
  intro ε hε
  exact finslerSupportedPressure_probability_lower_of_good_event μ ν K hK hμ hν P X Y
    φ f t L ε (G ε) (hgood ε hε) (hbad ε hε)

/-- **Physical endpoint with an expectation lower bound.**  The probability
lower bound input of the squeeze is replaced by an expectation lower bound
`liminf E V n >= L`; the centred concentration then supplies `hprob`.  This is
an alternative to the pathwise rooted-scene route of `main.tex`. -/
theorem tendsto_finslerSemidiscreteMean_of_integral_lower_and_integral_upper
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (m : Measure E) [m.IsAddHaarMeasure] (hdim : 6 ≤ Module.finrank ℝ E)
    (μ ν : ProbabilityMeasure M)
    (hμchart : ∀ old : M, ((μ : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, ((ν : Measure M).restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) = (μ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) = (ν : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instSqueezeIntegralLowerPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t L : ℝ)
    (hlower : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      L - ε ≤ ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n)
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n ≤ L + ε) :
    Tendsto (fun n ↦ finslerSemidiscreteMean F μ ν K hK hμ hν φ f t n) atTop (𝓝 L) := by
  letI : MetricSpace M := F.metricSpace
  have hφc : Continuous φ := hφ.continuous
  refine tendsto_finslerSemidiscreteMean_of_probability_lower_and_integral_upper
    hF hcomplete m (by omega : 2 ≤ Module.finrank ℝ E) μ ν hμchart hνchart K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ f t L ?_ hupper
  intro ε hε
  exact finslerSupportedPressure_probability_lower_of_integral_lower hdim μ ν K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφc f t L hε
    (hlower (ε / 2) (by linarith))

/-- Measurability of the physical pressure process at the paper's scale.
This is the measurability input of the scalar-law subsequence criterion. -/
theorem measurable_finslerSupportedPressure
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ) :
    ∀ n, Measurable (fun s ↦ finslerSupportedPressure F μ ν K hK hμ hν
      (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t) := by
  intro n
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hφc : Continuous φ := hφ
  have h := Pressure.measurable_supportedDistancePressure μ ν K hK hμ hν
    (X n) (Y n) (hX n) (hY n) φ hφc
    (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
  simpa only [finslerSupportedPressure] using h

/-- **`hprob` from the paper's subsequence criterion** at a fixed probe, tilt
and target value.  The hypothesis is the conclusion of the rooted-scene
compactness, stationarity and Campbell-formula analysis: every subsequence of
the scalar laws has a further subsequence converging weakly to a probability
measure supported on `[L, ∞)`. -/
theorem finslerSupportedPressure_probability_lower_of_subseq_weak_limit
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t L ε : ℝ) (hε : 0 < ε)
    (hsub : ∀ φidx : ℕ → ℕ, StrictMono φidx →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
        Tendsto (fun k ↦ pressureScalarLaw P
          (fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
            (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
          (measurable_finslerSupportedPressure hcomplete μ ν K hK.measurableSet hμ hν
            X Y hX hY φ hφ f t)
          (φidx (ψ k))) atTop (𝓝 νlim) ∧
        (νlim : Measure ℝ) (Iic (L - ε)) = 0) :
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t < L - ε})
      atTop (𝓝 0) := by
  have h := tendsto_measureReal_lt_sub_of_subseq_weak_limit P
    (fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
      (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (measurable_finslerSupportedPressure hcomplete μ ν K hK.measurableSet hμ hν
      X Y hX hY φ hφ f t)
    hε hsub
  simpa only using h

/-- **The whole `hprob` clause from the subsequence criterion.**  This is the
exact closing interface for the paper's Proposition
`general-gluing-weighted-lower`: it remains to prove that every subsequential
weak limit of the scalar physical-pressure laws is supported on
`[pressure f t, ∞)`. -/
theorem finsler_probability_lower_bound_of_subseq_weak_limit
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (hsub : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      ∀ ε : ℝ, 0 < ε → ∀ φidx : ℕ → ℕ, StrictMono φidx →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
          Tendsto (fun k ↦ pressureScalarLaw P
            (fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
              (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
              (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
            (measurable_finslerSupportedPressure hcomplete μ ν K hK.measurableSet hμ hν
              X Y hX hY φ hφ f t)
            (φidx (ψ k))) atTop (𝓝 νlim) ∧
          (νlim : Measure ℝ) (Iic (pressure f t - ε)) = 0) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0) := by
  intro f t ε ht hε
  exact finslerSupportedPressure_probability_lower_of_subseq_weak_limit hcomplete μ ν K hK
    hμ hν P X Y hX hY φ hφ f t (pressure f t) ε hε (hsub f t ht ε hε)

/-- **`hprob` from a support statement on subsequential weak limits** at a
fixed probe, tilt and target value: every subsequential weak limit of the
scalar physical-pressure laws is supported on `[L, ∞)`. -/
theorem finslerSupportedPressure_probability_lower_of_subseq_weak_support
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (f : (K × K) →ᵇ ℝ) (t L : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ φidx : ℕ → ℕ, StrictMono φidx →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
        Tendsto (fun k ↦ pressureScalarLaw P
          (fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
            (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
            (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
          (measurable_finslerSupportedPressure hcomplete μ ν K hK.measurableSet hμ hν
            X Y hX hY φ hφ f t)
          (φidx (ψ k))) atTop (𝓝 νlim) ∧
        (νlim : Measure ℝ) (Iio L) = 0) :
    Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t < L - ε})
      atTop (𝓝 0) := by
  have h := tendsto_measureReal_lt_sub_of_subseq_weak_support P
    (fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
      (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
    (measurable_finslerSupportedPressure hcomplete μ ν K hK.measurableSet hμ hν
      X Y hX hY φ hφ f t)
    hε hsub
  simpa only using h

/-- **The whole `hprob` clause from a support statement on subsequential weak
limits.**  For every probe and tilt it suffices that each subsequential weak
limit of the scalar pressure laws is supported on `[pressure f t, ∞)`.  This
support statement is exactly the outcome of
`main.tex` Proposition `general-gluing-weighted-lower`: the limiting rooted
scene has value at least the weighted population pressure almost surely. -/
theorem finsler_probability_lower_bound_of_subseq_weak_support
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (φ : M → ℝ)
    (hφ : let _inst : MetricSpace M := F.metricSpace; Continuous φ)
    (pressure : ((K × K) →ᵇ ℝ) → ℝ → ℝ) (radius : ((K × K) →ᵇ ℝ) → ℝ)
    (hsub : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), |t| < radius f →
      ∀ φidx : ℕ → ℕ, StrictMono φidx →
        ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
          Tendsto (fun k ↦ pressureScalarLaw P
            (fun n s ↦ finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
              (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
              (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t)
            (measurable_finslerSupportedPressure hcomplete μ ν K hK.measurableSet hμ hν
              X Y hX hY φ hφ f t)
            (φidx (ψ k))) atTop (𝓝 νlim) ∧
          (νlim : Measure ℝ) (Iio (pressure f t)) = 0) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressure f t - ε}) atTop (𝓝 0) := by
  intro f t ε ht hε
  exact finslerSupportedPressure_probability_lower_of_subseq_weak_support hcomplete μ ν K hK
    hμ hν P X Y hX hY φ hφ f t (pressure f t) hε (hsub f t ht)

end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
