import OTSelector.Limit.FinslerProbabilityLowerBound
import OTSelector.Limit.PhysicalSelectorWrapper
import OTSelector.Reconstruction.FiniteDominationCore

/-!
# Actual iid global lower pressure localization for the intrinsic Finsler length cost

The general Finsler selector assembly
(`OTSelector/Reconstruction/FinslerGeneralSelectorAssembly.lean`) consumes, as its
first analytic input `hprob`, the original iid *lower* pressure localization

  for every probe `f`, tilt `t` and accuracy `eps > 0`,
  `P_n {s | V_n(s) < pressureLower f t - eps} -> 0`,

where `V_n` is the supported physical empirical pressure `finslerSupportedPressure`
at the paper scale `(n+1)^(2/(d-1))`, `d = dim M >= 6`.

This module proves that lower localization from the paper's two lower-lane
ingredients, with every population datum explicit (compact supports, iid arrays,
fixed tilt and test) and with the probe constant `B_t = |t| * ||f||` paid once:

* **Finite domination** (`general-gluing-finite-domination`).  On the actual
  optimal fractional assignment `A_n` of the tilted empirical problem, every
  frozen core matrix `E_n` whose entries are pointwise at most the tilted edge
  cost plus `B_t` has total frozen cost at most the empirical pressure plus
  `B_t`.  The deterministic core of this inequality is proved in
  `OTSelector/Reconstruction/FiniteDominationCore.lean`; the glue to the
  physical supported pressure is proved here
  (`OTSelector.Pressure.frozenCost_div_le_supportedDistancePressure_add`,
  `ae_frozenCost_div_le_finslerSupportedPressure_add`).
* **Campbell mean comparison**.  The asymptotic lower bound of the *expected*
  frozen core cost by the population pressure plus `B_t`, i.e. the
  expectation-level form of the Campbell-formula comparison.  The atlas-level
  Campbell comparison itself is already formalized
  (`FinslerCampbellLowerAssembly.campbellAveragedStationaryPressure_le_campbellAveragedFrozenCost`);
  what is *not* formalized anywhere is its identification with the mean of the
  frozen core cost of the original empirical optimal face (the law-of-large
  numbers for the rooted-scene frozen functional).  That single expectation-level
  statement is the remaining hypothesis `hfrozen_mean` below.

From those two ingredients the actual probability statement follows: finite
domination converts the mean comparison into `liminf_n E[V_n] >= pressureLower`,
and the unconditional centred concentration of `V_n` about its own mean at
`d >= 6` (`tendsto_centered_finslerSupportedPressure`) turns the mean bound into
the probability bound.  No density lower bound, support-boundary regularity or
geometric condition is used beyond the compact carrier and the one-Lipschitz
potential.

The main results are

* `finslerSupportedPressure_probability_lower_of_frozen_mean_lower`: the family
  form of `hprob` at an abstract population pressure `pressureLower`, from
  frozen-core domination, integrability and the mean lower bound;
* `finslerSupportedPressure_probability_lower_of_frozen_pathwise_lower`: the
  same conclusion from the paper's *pathwise* lower comparison
  `pressureLower f t + |t| ||f|| - eps <= frozenCost` eventually almost surely
  (the form `PointProcess.CampbellLowerComparison` takes);
* `finslerSupportedPressure_probability_lower_of_frozen_weak_limit`: the same
  conclusion when every subsequential weak limit of the frozen core cost laws is
  supported on `[pressureLower f t + |t| ||f||, inf)` -- the exact conclusion of
  the paper's rooted-scene compactness, stationarity and Campbell-formula
  analysis;
* `physical_finsler_probability_lower_of_frozen_mean_lower` and
  `physical_finsler_probability_lower_of_frozen_pathwise_lower`: the same
  statements for the exact population data of the assembly
  (`physicalSourceProbability`, `physicalTargetProbability`, `A ∪ B`),
  producing the assembly's `hprob` clause verbatim, with its `radius` parameter;
* `ae_frozenCost_div_le_finslerSupportedPressure_add`: finite domination
  (`general-gluing-finite-domination`) on the physical empirical optimal face,
  together with its deterministic matrix core
  `OTSelector.Pressure.frozenCost_div_le_supportedDistancePressure_add`;
* `tendsto_integral_lower_of_subseq_weak_support`: the paper's rooted-scene
  conclusion (weak limits of a bounded-below statistic's laws are supported on
  `[c, inf)`) upgraded to the expectation-level lower bound consumed above.

No `sorry`, `admit` or added axiom occurs.  The remaining gap is precisely the
identification of the frozen core mean (or its weak limits) with the population
Campbell value `P_w(t)`; the probability transfer, finite domination and the
weak-limit-to-mean passage are unconditional here.
-/

open Set Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Probability
open scoped Topology ContDiff NNReal ENNReal BoundedContinuousFunction

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace OTSelector.Pressure
open Probability

variable {M : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]

/-- **Deterministic frozen-core domination at the physical supported pressure.**

If `A` is an optimal fractional assignment of the tilted empirical problem with
scaled distance-slack base cost and carrier probe, and the frozen matrix `E` is
pointwise at most the tilted edge cost plus the probe constant `|t| ‖f‖`, then
the normalized frozen cost is at most the supported empirical pressure plus
`|t| ‖f‖`.  This is the deterministic matrix core of the paper's
`general-gluing-finite-domination`, glued to the physical pressure. -/
theorem frozenCost_div_le_supportedDistancePressure_add
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : MeasurableSet K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    {n : ℕ} (hn : 0 < n) (X Y : Fin n → M) (φ : M → ℝ) (_hφ : LipschitzWith 1 φ)
    (k : ℝ) (f : (K × K) →ᵇ ℝ) (t : ℝ)
    {E A : Matrix (Fin n) (Fin n) ℝ}
    (hA : OptimalFractionalAssignment (perturbedEdgeCost
      (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
      (fun i j ↦ f (supportProjection μ K hK hμ (X i),
        supportProjection ν K hK hν (Y j))) t) A)
    (hE : ∀ i j, E i j ≤ perturbedEdgeCost
      (fun i j ↦ k * distanceSlackEdgeCost X Y φ i j)
      (fun i j ↦ f (supportProjection μ K hK hμ (X i),
        supportProjection ν K hK hν (Y j))) t i j + |t| * (‖f‖₊ : ℝ)) :
    fractionalAssignmentCost E A / (n : ℝ) ≤
      supportedDistancePressure μ ν K hK hμ hν X Y φ k f t + |t| * (‖f‖₊ : ℝ) := by
  simpa only [supportedDistancePressure] using
    (fractionalAssignmentCost_div_le_perturbedAssignmentValue_div_add hn hA hE)

end OTSelector.Pressure

namespace OTSelector.Probability

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

/-- **The paper's rooted-scene weak-limit conclusion implies the mean lower bound.**

Let `X n` be an integrable real statistic of the `n`-th sample, bounded below by
`Clo`.  If every subsequence of its scalar laws has a further subsequence
converging weakly to a probability measure supported on `[c, ∞)`, then
`liminf_n E[X n] >= c`: for every `eps > 0`, eventually `c - eps <= E[X n]`.

This is the measure-theoretic step which turns the support statement produced by
the rooted-scene compactness, stationarity and Campbell-formula analysis (a
statement about weak limits of laws) into the expectation-level Campbell lower
bound consumed by
`finslerSupportedPressure_probability_lower_of_frozen_mean_lower`. -/
theorem tendsto_integral_lower_of_subseq_weak_support
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X : ∀ n, Ω n → ℝ) (hX : ∀ n, Measurable (X n))
    (hint : ∀ n, Integrable (X n) (P n))
    {Clo c : ℝ}
    (hlow : ∀ n, ∀ᵐ x ∂P n, Clo ≤ X n x)
    (hsub : ∀ φidx : ℕ → ℕ, StrictMono φidx →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
        Tendsto (fun k ↦ pressureScalarLaw P X hX (φidx (ψ k))) atTop (𝓝 νlim) ∧
        (νlim : Measure ℝ) (Iio c) = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, c - ε ≤ ∫ x, X n x ∂P n := by
  classical
  by_contra hcon
  rw [Filter.not_eventually] at hcon
  have hfreq : ∀ N : ℕ, ∃ n > N, ∫ x, X n x ∂P n < c - ε := by
    intro N
    obtain ⟨n, hnN, hlt⟩ := Filter.frequently_atTop'.1 hcon (N + 1)
    exact ⟨n, by omega, not_le.1 hlt⟩
  obtain ⟨φidx, hφmono, hφprop⟩ := Nat.exists_strictMono_subsequence hfreq
  obtain ⟨ψ, _hψmono, νlim, hlim, hsupp⟩ := hsub φidx hφmono
  by_cases hcase : c - ε ≤ Clo
  · -- the lower bound alone already contradicts the deficit subsequence
    have hge : c - ε ≤ ∫ x, X (φidx 0) x ∂P (φidx 0) := by
      have h := integral_mono_ae (integrable_const Clo) (hint (φidx 0)) (hlow (φidx 0))
      have hc : ∫ _x, Clo ∂P (φidx 0) = Clo := by
        rw [integral_const]
        simp [measureReal_def]
      rw [hc] at h
      exact hcase.trans h
    linarith [hφprop 0]
  · -- main case: `Clo < c - eps`
    set δ : ℝ := ε / 2 with hδdef
    set a : ℝ := c - Clo with hadef
    have hδpos : 0 < δ := by positivity
    have hδε : δ < ε := by rw [hδdef]; linarith
    have hcδ : Clo < c - δ := by linarith
    have ha : 0 < a := by rw [hadef]; linarith
    have had : 0 < a - δ := by rw [hadef]; linarith
    -- the limiting law is supported on `[c, inf)`, so the upper event has
    -- frontier of zero mass and limit measure one
    have hfront : (νlim : Measure ℝ) (frontier (Ioi (c - δ))) = 0 := by
      rw [frontier_Ioi]
      exact measure_mono_null
        (fun x hx ↦ by
          rw [mem_singleton_iff] at hx
          rw [hx]
          exact mem_Iio.mpr (by linarith))
        hsupp
    have hνone : (νlim : Measure ℝ) (Ioi (c - δ)) = 1 := by
      have hcomp : (νlim : Measure ℝ) (Iic (c - δ)) = 0 :=
        measure_mono_null
          (fun x hx ↦ mem_Iio.mpr (lt_of_le_of_lt (mem_Iic.mp hx) (by linarith)))
          hsupp
      have hset : Ioi (c - δ) = (Iic (c - δ))ᶜ := by
        ext x
        simp only [mem_Ioi, mem_compl_iff, mem_Iic, not_le]
      rw [hset, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ, hcomp,
        tsub_zero]
    have hconv := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hlim hfront
    have hρ : Tendsto (fun k ↦
        ((pressureScalarLaw P X hX (φidx (ψ k)) : Measure ℝ) (Ioi (c - δ))).toReal)
        atTop (𝓝 1) := by
      have h1 : Tendsto (fun k ↦
          ((pressureScalarLaw P X hX (φidx (ψ k)) : Measure ℝ) (Ioi (c - δ))))
          atTop (𝓝 1) := by
        simpa only [hνone] using hconv
      have h2 : Tendsto (fun k ↦
          ((pressureScalarLaw P X hX (φidx (ψ k)) : Measure ℝ) (Ioi (c - δ))).toReal)
          atTop (𝓝 1) :=
        (ENNReal.tendsto_toReal (by norm_num : (1 : ℝ≥0∞) ≠ ⊤)).comp h1
      exact h2
    -- eventually the mean of the upper threshold exceeds `a - eps`
    have hkey : ∀ᶠ k in atTop, a - ε < (a - δ) *
        ((pressureScalarLaw P X hX (φidx (ψ k)) : Measure ℝ) (Ioi (c - δ))).toReal := by
      have ht : Tendsto (fun k ↦ (a - δ) *
          ((pressureScalarLaw P X hX (φidx (ψ k)) : Measure ℝ) (Ioi (c - δ))).toReal)
          atTop (𝓝 ((a - δ) * 1)) := hρ.const_mul (a - δ)
      refine ht.eventually (Ioi_mem_nhds ?_)
      rw [mul_one]
      linarith
    -- per-sample integral lower bound against the event mass
    have key : ∀ n : ℕ, (a - δ) * ((P n).real {x | c - δ < X n x}) ≤
        ∫ x, X n x ∂P n - Clo := by
      intro n
      have hs : MeasurableSet {x | c - δ < X n x} :=
        measurableSet_lt measurable_const (hX n)
      have hYint : Integrable (fun x ↦ X n x - Clo) (P n) :=
        (hint n).sub (integrable_const Clo)
      have hmono : ∫ x in {x | c - δ < X n x}, (a - δ) ∂P n ≤
          ∫ x in {x | c - δ < X n x}, (X n x - Clo) ∂P n := by
        refine setIntegral_mono_on_ae (integrable_const (a - δ)).integrableOn
          hYint.integrableOn hs ?_
        filter_upwards with x hx
        rw [hadef]
        linarith
      have hconst : ∫ x in {x | c - δ < X n x}, (a - δ) ∂P n =
          (a - δ) * (P n).real {x | c - δ < X n x} := by
        rw [setIntegral_const, smul_eq_mul, mul_comm]
      have hsplit := integral_add_compl hs hYint
      have hnonneg : 0 ≤ ∫ x in {x | c - δ < X n x}ᶜ, (X n x - Clo) ∂P n := by
        refine integral_nonneg_of_ae ?_
        change ∀ᵐ x ∂(P n).restrict {x | c - δ < X n x}ᶜ, (0 : ℝ) ≤ X n x - Clo
        rw [ae_restrict_iff' hs.compl]
        filter_upwards [hlow n] with x hxl hxmem
        simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at hxmem
        linarith
      have hYeq : ∫ x, (X n x - Clo) ∂P n = ∫ x, X n x ∂P n - Clo := by
        rw [integral_sub (hint n) (integrable_const Clo), integral_const]
        simp [measureReal_def]
      rw [hconst] at hmono
      linarith
    -- identify the event mass with the law of the statistic
    have hlaw (n : ℕ) : ((pressureScalarLaw P X hX n : Measure ℝ) (Ioi (c - δ))).toReal =
        (P n).real {x | c - δ < X n x} := by
      have hmap : ((pressureScalarLaw P X hX n : Measure ℝ) (Ioi (c - δ))) =
          (P n) {x | c - δ < X n x} := by
        change (P n).map (X n) (Ioi (c - δ)) = (P n) {x | c - δ < X n x}
        rw [Measure.map_apply (hX n) measurableSet_Ioi]
        rfl
      rw [hmap, measureReal_def]
    obtain ⟨k, hk⟩ := hkey.exists
    have hk' := key (φidx (ψ k))
    rw [hlaw (φidx (ψ k))] at hk
    linarith [hφprop (ψ k)]

end OTSelector.Probability


namespace OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {F : ContinuousFinslerNorm E M}


/-- **Finite domination on the physical empirical optimal face.**

For every sample size, almost surely, *every* optimal fractional assignment
`Amat n s` of the tilted empirical problem at the paper scale
`k_n = (n+1)^(2/(d-1))` controls the total frozen core matrix `Emat n s` by the
supported physical pressure plus the probe constant `|t| ‖f‖`.  This is
`main.tex`, `general-gluing-finite-domination`, with `Emat` the compact frozen
core matrix and with the probe overhead paid once for the whole assignment.
The scaled distance-slack edge cost is written with the intrinsic length
`F.lengthEDist`, so that the statement needs no metric structure on `M`. -/
theorem ae_frozenCost_div_le_finslerSupportedPressure_add
    (μ ν : ProbabilityMeasure M) (K : Set M) (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂(μ : Measure M), x ∈ K) (hν : ∀ᵐ y ∂(ν : Measure M), y ∈ K)
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (φ : M → ℝ)
    (hφ : let _instFinslerLowerPotentialMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (f : (K × K) →ᵇ ℝ) (t : ℝ)
    (Amat Emat : ∀ n, Ω n → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : ∀ n, ∀ᵐ s ∂P n, OptimalFractionalAssignment (perturbedEdgeCost
      (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
        ((F.lengthEDist (X n i s) (Y n j s)).toReal -
          φ (Y n j s) + φ (X n i s)))
      (fun i j ↦ f (supportProjection μ K hK.measurableSet hμ (X n i s),
        supportProjection ν K hK.measurableSet hν (Y n j s))) t) (Amat n s))
    (hE : ∀ n, ∀ᵐ s ∂P n, ∀ i j, Emat n s i j ≤ perturbedEdgeCost
      (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
        ((F.lengthEDist (X n i s) (Y n j s)).toReal -
          φ (Y n j s) + φ (X n i s)))
      (fun i j ↦ f (supportProjection μ K hK.measurableSet hμ (X n i s),
        supportProjection ν K hK.measurableSet hν (Y n j s))) t i j +
        |t| * (‖f‖₊ : ℝ)) :
    ∀ n, ∀ᵐ s ∂P n,
      fractionalAssignmentCost (Emat n s) (Amat n s) / ((n + 1 : ℕ) : ℝ) ≤
        finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ) := by
  letI : MetricSpace M := F.metricSpace
  have hφL : LipschitzWith 1 φ := hφ
  intro n
  filter_upwards [hA n, hE n] with s hAs hEs
  have hAs' : OptimalFractionalAssignment (perturbedEdgeCost
      (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
        distanceSlackEdgeCost (fun k ↦ X n k s) (fun l ↦ Y n l s) φ i j)
      (fun i j ↦ f (supportProjection μ K hK.measurableSet hμ (X n i s),
        supportProjection ν K hK.measurableSet hν (Y n j s))) t) (Amat n s) := by
    simpa only [distanceSlackEdgeCost, F.metricSpace_dist] using hAs
  have hEs' : ∀ i j, Emat n s i j ≤ perturbedEdgeCost
      (fun i j ↦ (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) *
        distanceSlackEdgeCost (fun k ↦ X n k s) (fun l ↦ Y n l s) φ i j)
      (fun i j ↦ f (supportProjection μ K hK.measurableSet hμ (X n i s),
        supportProjection ν K hK.measurableSet hν (Y n j s))) t i j +
        |t| * (‖f‖₊ : ℝ) := by
    intro i j
    simpa only [distanceSlackEdgeCost, F.metricSpace_dist] using hEs i j
  have h := Pressure.frozenCost_div_le_supportedDistancePressure_add μ ν K
    hK.measurableSet hμ hν (Nat.succ_pos n) (fun i ↦ X n i s) (fun j ↦ Y n j s) φ hφL
    (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t hAs' hEs'
  simpa only [finslerSupportedPressure] using h

/-- **Actual iid global lower pressure localization (family form).**

Let `V n s` be the supported physical empirical pressure at the paper scale
`k_n = (n+1)^(2/(d-1))` for a fixed bounded continuous probe `f` and tilt `t`.
Suppose that a frozen core cost `frozenCost f t n` is, almost surely at each
sample size, at most `V n` plus the probe constant `|t| ‖f‖` (finite domination,
proved unconditionally by
`ae_frozenCost_div_le_finslerSupportedPressure_add` for the geometric frozen
matrix), that it is integrable, and that its expectation obeys the
Campbell-formula lower bound

  `pressureLower f t + |t| ‖f‖ - eps <= E[frozenCost f t n]` eventually.

Then the empirical pressure itself satisfies, for every `eps > 0`,

  `P_n {s | V n s < pressureLower f t - eps} -> 0`.

The proof composes finite domination with the unconditional centred
concentration of the physical pressure about its own mean at `d >= 6`. -/
theorem finslerSupportedPressure_probability_lower_of_frozen_mean_lower
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
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
    (hφ : let _instFinslerLowerPressureMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_mean : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressureLower f t - ε}) atTop (𝓝 0) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : SecondCountableTopology M :=
    @secondCountable_of_proper M F.metricSpace.toPseudoMetricSpace
      (F.properSpace_of_complete hcomplete)
  have hφL : LipschitzWith 1 φ := hφ
  have hφc : Continuous φ := hφL.continuous
  intro f t ε hε
  have hXK (n : ℕ) : ∀ᵐ s ∂P n, ∀ i, X n i s ∈ K := by
    apply ae_all_iff.mpr
    intro i
    exact ae_of_ae_map (hX n i).aemeasurable (by rw [hXlaw n i]; exact hμ)
  have hYK (n : ℕ) : ∀ᵐ s ∂P n, ∀ j, Y n j s ∈ K := by
    apply ae_all_iff.mpr
    intro j
    exact ae_of_ae_map (hY n j).aemeasurable (by rw [hYlaw n j]; exact hν)
  have hVint (n : ℕ) : Integrable (fun s ↦ finslerSupportedPressure F μ ν K
      hK.measurableSet hμ hν (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
      (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t) (P n) := by
    have hkpos : 0 < (((n + 1 : ℕ) : ℝ) ^
        (2 / ((Module.finrank ℝ E : ℝ) - 1))) :=
      Real.rpow_pos_of_pos (by positivity) _
    simpa only [finslerSupportedPressure] using
      (Pressure.integrable_supportedDistancePressure (P n) μ ν K hK.measurableSet hμ hν
        (X n) (Y n) (hX n) (hY n) φ hφL hφc
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t
        (Nat.succ_pos n) hkpos.le hK (hXK n) (hYK n))
  have hmean_le (n : ℕ) : ∫ s, frozenCost f t n s ∂P n ≤
      (∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) +
        |t| * (‖f‖₊ : ℝ) := by
    have hBint : Integrable (fun s ↦ finslerSupportedPressure F μ ν K hK.measurableSet
        hμ hν (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
        (|t| * (‖f‖₊ : ℝ))) (P n) :=
      (hVint n).add (integrable_const _)
    have hcmp : ∫ s, frozenCost f t n s ∂P n ≤
        ∫ s, (finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          (|t| * (‖f‖₊ : ℝ))) ∂P n :=
      integral_mono_ae (hfrozen_int f t n) hBint (hfrozen_dom f t n)
    have hsplit : ∫ s, (finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
        (|t| * (‖f‖₊ : ℝ))) ∂P n =
        (∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n) +
          |t| * (‖f‖₊ : ℝ) := by
      rw [integral_add (hVint n) (integrable_const _), integral_const]
      simp [measureReal_def]
    rw [hsplit] at hcmp
    exact hcmp
  have hlower : ∀ᶠ n in atTop, pressureLower f t - ε / 2 ≤
      ∫ s, finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
        (fun i ↦ X n i s) (fun j ↦ Y n j s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t ∂P n := by
    filter_upwards [hfrozen_mean f t (ε / 2) (by linarith)] with n hn
    have h1 := hmean_le n
    linarith
  exact finslerSupportedPressure_probability_lower_of_integral_lower hdim μ ν K hK
    hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφc f t (pressureLower f t) hε hlower


/-- **`hprob` from the paper's pathwise lower comparison.**  If the frozen core
cost is, eventually almost surely, at least the population pressure plus the
probe constant (the form in which the rooted-scene Campbell argument concludes,
cf. `PointProcess.CampbellLowerComparison`), then the same probability lower
localization holds.  This replaces the expectation-level hypothesis by the
pathwise one; the two are equivalent for integrable frozen costs. -/
theorem finslerSupportedPressure_probability_lower_of_frozen_pathwise_lower
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
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
    (hφ : let _instFinslerLowerPathwiseMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_lower : ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε → ∀ᶠ n in atTop,
      ∀ᵐ s ∂P n,
        pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε ≤ frozenCost f t n s) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressureLower f t - ε}) atTop (𝓝 0) := by
  refine finslerSupportedPressure_probability_lower_of_frozen_mean_lower hcomplete hdim
    μ ν K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ pressureLower frozenCost
    hfrozen_int hfrozen_dom ?_
  intro f t ε hε
  filter_upwards [hfrozen_lower f t ε hε] with n hn
  have h := integral_mono_ae
    (integrable_const (pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε))
    (hfrozen_int f t n) hn
  have hc : ∫ _x, (pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε) ∂P n =
      pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε := by
    rw [integral_const]
    simp [measureReal_def]
  rwa [hc] at h

/-- **Actual iid global lower pressure localization for the assembly's population
data.**  This is the assembly's `hprob` clause, verbatim: the exact population
data `physicalSourceProbability ωM ρ₀`, `physicalTargetProbability ωM ρ₁`, compact
carrier `A ∪ B`, the original iid arrays and the fixed one-Lipschitz probe `φ`.
It is proved from frozen-core finite domination, integrability and the
expectation-level Campbell lower bound at the same population pressure
`pressureLower`. -/
theorem physical_finsler_probability_lower_of_frozen_mean_lower
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) =
      (physicalSourceProbability ωM ρ₀ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) =
      (physicalTargetProbability ωM ρ₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instFinslerLowerAssemblyMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressureLower : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (frozenCost : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_mean : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop,
        pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε ≤ ∫ s, frozenCost f t n s ∂P n) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F
        (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressureLower f t - ε}) atTop (𝓝 0) := by
  intro f t ε _ht hε
  exact finslerSupportedPressure_probability_lower_of_frozen_mean_lower hcomplete hdim
    (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁) (A ∪ B)
    (hA.union hB) (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
    P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ pressureLower frozenCost
    hfrozen_int hfrozen_dom hfrozen_mean f t ε hε
/-- **The assembly's `hprob` clause from a pathwise frozen-core lower bound.**
Same exact population data as `physical_finsler_probability_lower_of_frozen_mean_lower`,
but the analytic input is the paper's pathwise form: eventually almost surely the
frozen core cost is at least the population pressure plus the probe constant. -/
theorem physical_finsler_probability_lower_of_frozen_pathwise_lower
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hdim : 6 ≤ Module.finrank ℝ E)
    (ωM : Measure M) (ρ₀ ρ₁ : M → ℝ)
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₀ x)))]
    [IsProbabilityMeasure (ωM.withDensity (fun x ↦ ENNReal.ofReal (ρ₁ x)))]
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμA : ∀ᵐ x ∂(physicalSourceProbability ωM ρ₀ : Measure M), x ∈ A)
    (hνB : ∀ᵐ y ∂(physicalTargetProbability ωM ρ₁ : Measure M), y ∈ B)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (X Y : ∀ n, Fin (n + 1) → Ω n → M)
    (hX : ∀ n i, Measurable (X n i)) (hY : ∀ n i, Measurable (Y n i))
    (hXi : ∀ n, iIndepFun (X n) (P n)) (hYi : ∀ n, iIndepFun (Y n) (P n))
    (hXlaw : ∀ n i, (P n).map (X n i) =
      (physicalSourceProbability ωM ρ₀ : Measure M))
    (hYlaw : ∀ n i, (P n).map (Y n i) =
      (physicalTargetProbability ωM ρ₁ : Measure M))
    (hXY : ∀ n, IndepFun (fun sample i ↦ X n i sample)
      (fun sample i ↦ Y n i sample) (P n))
    (φ : M → ℝ)
    (hφ : let _instFinslerLowerAssemblyPathwiseMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressureLower : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ℝ)
    (radius : ((↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ)
    (frozenCost : (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_int : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_dom : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F
          (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
          (A ∪ B) (hA.union hB).measurableSet
          (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_lower : ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      ∀ᶠ n in atTop, ∀ᵐ s ∂P n,
        pressureLower f t + |t| * (‖f‖₊ : ℝ) - ε ≤ frozenCost f t n s) :
    ∀ (f : (↥(A ∪ B) × ↥(A ∪ B)) →ᵇ ℝ) (t ε : ℝ),
      |t| < radius f → 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F
        (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁)
        (A ∪ B) (hA.union hB).measurableSet
        (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
        (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressureLower f t - ε}) atTop (𝓝 0) := by
  intro f t ε _ht hε
  exact finslerSupportedPressure_probability_lower_of_frozen_pathwise_lower hcomplete hdim
    (physicalSourceProbability ωM ρ₀) (physicalTargetProbability ωM ρ₁) (A ∪ B)
    (hA.union hB) (hμA.mono fun _ hx ↦ Or.inl hx) (hνB.mono fun _ hy ↦ Or.inr hy)
    P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ pressureLower frozenCost
    hfrozen_int hfrozen_dom hfrozen_lower f t ε hε

/-- **`hprob` from the paper's weak-limit support statement on the frozen core cost.**

This is the closest form to the paper's proof of `general-gluing-weight-lower`: the
rooted-scene compactness/stationarity/Campbell analysis produces, for the frozen
core functional `frozenCost f t n`, the statement that every subsequential weak
limit of its scalar laws is supported on
`[pressureLower f t + |t| ‖f‖, inf)`.  Combined with finite domination, frozen
integrability, frozen nonnegativity and measurability, this yields the family
`hprob` at `pressureLower`.  The extra inputs beyond the mean form are only the
measurability and a.e. nonnegativity of the frozen core cost, both automatic for
the geometric frozen matrix. -/
theorem finslerSupportedPressure_probability_lower_of_frozen_weak_limit
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
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
    (hφ : let _instFinslerLowerWeakMetric : MetricSpace M := F.metricSpace
      LipschitzWith 1 φ)
    (pressureLower : ((K × K) →ᵇ ℝ) → ℝ → ℝ)
    (frozenCost : (f : (K × K) →ᵇ ℝ) → ℝ → ∀ n, Ω n → ℝ)
    (hfrozen_meas : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Measurable (frozenCost f t n))
    (hfrozen_int : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ),
      Integrable (frozenCost f t n) (P n))
    (hfrozen_nonneg : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      0 ≤ frozenCost f t n s)
    (hfrozen_dom : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ) (n : ℕ), ∀ᵐ s ∂P n,
      frozenCost f t n s ≤
        finslerSupportedPressure F μ ν K hK.measurableSet hμ hν
          (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
          (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t +
          |t| * (‖f‖₊ : ℝ))
    (hfrozen_weak : ∀ (f : (K × K) →ᵇ ℝ) (t : ℝ), ∀ φidx : ℕ → ℕ, StrictMono φidx →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ νlim : ProbabilityMeasure ℝ,
        Tendsto (fun k ↦ pressureScalarLaw P (fun n ↦ frozenCost f t n)
          (hfrozen_meas f t) (φidx (ψ k))) atTop (𝓝 νlim) ∧
        (νlim : Measure ℝ) (Iio (pressureLower f t + |t| * (‖f‖₊ : ℝ))) = 0) :
    ∀ (f : (K × K) →ᵇ ℝ) (t ε : ℝ), 0 < ε →
      Tendsto (fun n ↦ (P n).real {s | finslerSupportedPressure F μ ν K
        hK.measurableSet hμ hν (fun i ↦ X n i s) (fun i ↦ Y n i s) φ
        (((n + 1 : ℕ) : ℝ) ^ (2 / ((Module.finrank ℝ E : ℝ) - 1))) f t <
          pressureLower f t - ε}) atTop (𝓝 0) := by
  refine finslerSupportedPressure_probability_lower_of_frozen_mean_lower hcomplete hdim
    μ ν K hK hμ hν P X Y hX hY hXi hYi hXlaw hYlaw hXY φ hφ pressureLower frozenCost
    hfrozen_int hfrozen_dom ?_
  intro f t ε hε
  exact tendsto_integral_lower_of_subseq_weak_support P (fun n ↦ frozenCost f t n)
    (hfrozen_meas f t) (hfrozen_int f t) (hfrozen_nonneg f t) (hfrozen_weak f t) hε
end OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
