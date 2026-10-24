import OTSelector.PointProcess.Campbell
import OTSelector.PointProcess.MassTransport
import OTSelector.PointProcess.RootedCampbell
import OTSelector.PointProcess.MatchingScenePerfect
import OTSelector.Reconstruction.FinslerStationaryPressureValue
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Stationary forward perfect matchings and the two stationary pressure classes

This module introduces the population lower-bound interface of the general Finsler
selector (`main.tex`, definition `general-gluing-two-classes`).  A
`StationaryForwardMatching α β` is a stationary forward perfect matching of two
independent unit-intensity marked Poisson clouds with source mark law `α` and
target mark law `β`.  Its source-Palm law of a typical matched marked pair carries
the kinetic energy `palmKinetic A` and the bounded mark probe `palmProbe f`, where
`A` is the calibrated quadratic coefficient and `f` the probe.

The two stationary classes are

* `FiniteWeightedKinetic A`, the paper's class `C_w`, requiring a finite weighted
  kinetic mean `𝔼^S[½ A(a,b) D²]`, and
* `FiniteSecondMoment`, the paper's class `C_2`, requiring a finite unweighted
  second moment `𝔼^S[D²]`.

The class inclusion `C_2 ⊆ C_w` is proved (`finiteSecondMoment_subset_finiteWeightedKinetic`),
with the quantitative domination `K ≤ (C/2) 𝔼^S[D²]`
(`palmKinetic_le_half_mul_secondMoment`).  The weighted kinetic energy is nonnegative
(`palmKinetic_nonneg`), the probe is uniformly bounded on the class (`abs_palmProbe_le`),
and a `StationaryPressureDatum` is constructed from a nonnegative bounded coefficient, a
bounded measurable probe, and two finite-energy competitors (`stationaryForwardDatum`).
Consequently the paper's chain `-|v| G ≤ I_w ≤ I_2 ≤ C_b + |v| G` and the root family
feeding `populationAtlasPressure` are obtained.

## What is constructed and what remains a hypothesis

The concrete Poisson construction of a matching is *not* formalized here.  The carrier
`StationaryForwardMatching` keeps the actual scene `MatchingScene` together with the
stationary Campbell data as fields:

* `pairCampbell_eq` is the Campbell factorization of the matched-pair intensity,
  `pairCampbell = volume.prod palm`;
* `sourceIntensity_eq` and `targetIntensity_eq` identify the input intensities as
  `volume.prod α` and `volume.prod β` (unit intensity and the prescribed mark laws);
* `inputCampbell_eq` states that the joint input intensity factorizes as the product of
  the two intensities, i.e. the two Poisson clouds are independent;
* `forward` and `perfect` state that the integer matching is forward and perfect;
* `source_mark_marginal` and `target_mark_marginal` identify the mark marginals of the
  typical matched pair.

The fields are consistent with the existing Campbell infrastructure:
`unitWindowPalm_pairCampbell` derives `unitWindowPalm pairCampbell = palm` from the
Campbell factorization and unit source intensity.

These are precisely the properties that the Poisson/perfect-matching construction would
have to establish.  Likewise, nonemptiness of the two classes (a finite-second-moment
stationary competitor) is supplied as explicit competitor fields of the constructed
datum, matching the paper's traffic-matrix construction but not formalized here.

The finite-domination/Campbell lower comparison is stated as an explicit hypothesis
(`FiniteDominationInequality`, `CampbellLowerComparison`) and combined into the
paper's probability statement in the final section; the Campbell step itself is
documented there and is not faked.

## Remaining gaps

1. *Concrete Poisson construction.*  Produce a `StationaryForwardMatching α β` from two
   independent unit-intensity marked Poisson clouds and a translation-covariant
   matching rule, and prove the Campbell/Palm fields (`pairCampbell_eq`,
   `sourceIntensity_eq`, `targetIntensity_eq`, `inputCampbell_eq`), forwardness,
   perfectness and the mark marginals.  No such construction is attempted here.
2. *Finite-second-moment competitors.*  The paper's traffic-matrix construction (a
   fixed stationary finite-second-moment two-color scheme on separated monochromatic
   runs) is not formalized; `stationaryForwardDatum` takes the two competitors as
   explicit hypotheses.
3. *Finite-domination inequality.*  The pathwise bound
   `Γ_n(F_{R,N}) ≤ V_n(t) + B_t + o_ℙ(1)` for actual empirical optimizers
   (`FiniteDominationInequality`) is assumed.
4. *Campbell lower comparison.*  The identification of the limiting frozen core cost
   with the source-Palm average, via Campbell's formula, rooted scene convergence and
   perfect matching retention (`CampbellLowerComparison`), is assumed.
5. *Attainment and regularity.*  Attainment of `I_w`/`I_2` and their universally
   measurable/continuous dependence on the root are not addressed here; the continuity
   lane lives in `Reconstruction/FinslerStationaryPressureContinuity.lean`.

The kinetic and probe functionals of the carrier are `palmKinetic` and `palmProbe`.
-/

open Set Function MeasureTheory MeasureTheory.Measure ProbabilityTheory Manifold
  OTSelector.Geometry Filter
open scoped Topology ContDiff ENNReal BigOperators

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 4096

namespace OTSelector.PointProcess

open OTSelector.Reconstruction

/-! ## The stationary matching carrier -/

/-- A marked point of a unit-intensity cloud: a scalar height and a `UnitMark` label. -/
abbrev MarkedCloudPoint := MatchingPoint

/-- Perfectness of a marked edge configuration: almost every source atom and almost
every target atom, counted with multiplicity, is incident to exactly one edge.  This is
the intensity-level statement that the integer matching leaves no input point unmatched
and gives no input point two partners. -/
def PerfectEdgeConfiguration (scene : MatchingScene) : Prop :=
  (∀ᵐ x ∂LocalConfiguration.countingMeasure scene.source,
      LocalConfiguration.countingMeasure scene.edges
        {e : MarkedCloudPoint × MarkedCloudPoint | e.1 = x} = 1) ∧
    (∀ᵐ y ∂LocalConfiguration.countingMeasure scene.target,
      LocalConfiguration.countingMeasure scene.edges
        {e : MarkedCloudPoint × MarkedCloudPoint | e.2 = y} = 1)

/-- A stationary forward perfect matching of two independent unit-intensity marked
Poisson clouds, with source mark law `α` and target mark law `β`.

The Poisson construction of such a matching is the remaining modeling step.  This
carrier records the resulting stationary/Palm/Campbell data as fields; the only fields
used by the pressure functionals below are `palm` and `palm_isProbability`, while the
remaining fields specify the probabilistic meaning of the carrier. -/
structure StationaryForwardMatching (α β : Measure UnitMark) where
  /-- The underlying marked scene: source cloud, target cloud, matched edges and
  feedback path. -/
  scene : MatchingScene
  /-- The source-Palm probability law of a typical matched marked pair, in coordinates
  rooted at the observation root. -/
  palm : Measure (MarkedCloudPoint × MarkedCloudPoint)
  /-- The Palm law is a probability measure.  Unit source intensity is exactly the
  normalization making the unnormalized Palm mass equal to one. -/
  palm_isProbability : IsProbabilityMeasure palm
  /-- Campbell measure of matched pairs: root location times rooted pair label. -/
  pairCampbell : Measure (ℝ × (MarkedCloudPoint × MarkedCloudPoint))
  /-- Campbell factorization of the matched-pair intensity measure. -/
  pairCampbell_eq : pairCampbell = (volume : Measure ℝ).prod palm
  /-- The Campbell intensity of the source cloud. -/
  sourceIntensity : Measure MarkedCloudPoint
  /-- Unit source intensity and source mark law `α`. -/
  sourceIntensity_eq : sourceIntensity = (volume : Measure ℝ).prod α
  /-- The Campbell intensity of the target cloud. -/
  targetIntensity : Measure MarkedCloudPoint
  /-- Unit target intensity and target mark law `β`. -/
  targetIntensity_eq : targetIntensity = (volume : Measure ℝ).prod β
  /-- The joint Campbell intensity of the two input clouds. -/
  inputCampbell : Measure (MarkedCloudPoint × MarkedCloudPoint)
  /-- Independence of the two unit-intensity marked Poisson clouds: the joint input
  Campbell intensity is the product of the two intensities. -/
  inputCampbell_eq : inputCampbell = sourceIntensity.prod targetIntensity
  /-- Every matched pair is forward: the target height strictly exceeds the source
  height. -/
  forward : ∀ᵐ p ∂palm, p.1.1 < p.2.1
  /-- The integer matching encoded by the scene is perfect. -/
  perfect : PerfectEdgeConfiguration scene
  /-- The source marks of a typical matched pair follow the source mark law. -/
  source_mark_marginal : palm.map (fun p : MarkedCloudPoint × MarkedCloudPoint => p.1.2) = α
  /-- The target marks of a typical matched pair follow the target mark law. -/
  target_mark_marginal : palm.map (fun p : MarkedCloudPoint × MarkedCloudPoint => p.2.2) = β

namespace StationaryForwardMatching

variable {α β : Measure UnitMark}

/-- The unit-window source Palm of the pair Campbell measure is the Palm law itself.
The Campbell factorization `pairCampbell = volume.prod palm` has unit source intensity,
so restricting the source location to `(0,1]` and projecting to the pair label
recovers `palm`.  This is the normalized form of `campbell_eq_volume_prod_palm` for the
matched-pair process. -/
theorem unitWindowPalm_pairCampbell (M : StationaryForwardMatching α β) :
    unitWindowPalm M.pairCampbell = M.palm := by
  let _ : IsProbabilityMeasure M.palm := M.palm_isProbability
  rw [M.pairCampbell_eq]
  ext B hB
  rw [unitWindowPalm_apply _ hB, Measure.prod_prod]
  simp

/-! ## Kinetic energy, probe and the two stationary classes -/

/-- Signed scalar displacement `D = b - a` of a matched pair. -/
def edgeDisplacement (p : MarkedCloudPoint × MarkedCloudPoint) : ℝ := p.2.1 - p.1.1

/-- The weighted kinetic integrand `½ A(a,b) D²`, where `a` and `b` are the source and
target heights and `A` is the calibrated quadratic coefficient. -/
def kineticIntegrand (A : ℝ → ℝ → ℝ) (p : MarkedCloudPoint × MarkedCloudPoint) : ℝ :=
  (1 / 2 : ℝ) * A p.1.1 p.2.1 * edgeDisplacement p ^ 2

/-- The weighted kinetic energy `K = 𝔼^S[½ A(a,b) D²]`, the source-Palm expectation of
the weighted kinetic integrand. -/
def palmKinetic (A : ℝ → ℝ → ℝ) (M : StationaryForwardMatching α β) : ℝ :=
  ∫ p, kineticIntegrand A p ∂M.palm

/-- The bounded mark probe `P = 𝔼^S[f(X(a), X(b))]`, the source-Palm expectation of the
probe evaluated at the matched marked endpoints. -/
def palmProbe (f : MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (M : StationaryForwardMatching α β) : ℝ :=
  ∫ p, f p.1 p.2 ∂M.palm

/-- The paper's weighted class `C_w`: stationary forward perfect matchings with finite
weighted kinetic mean. -/
def FiniteWeightedKinetic (A : ℝ → ℝ → ℝ) (M : StationaryForwardMatching α β) : Prop :=
  Integrable (kineticIntegrand A) M.palm

/-- The paper's second-moment class `C_2`: stationary forward perfect matchings with
finite unweighted second moment `𝔼^S[D²]`. -/
def FiniteSecondMoment (M : StationaryForwardMatching α β) : Prop :=
  Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint => edgeDisplacement p ^ 2) M.palm

/-- The weighted kinetic energy is nonnegative when the quadratic coefficient is
nonnegative.  This holds on the whole carrier, hence in particular on `C_w`. -/
theorem palmKinetic_nonneg {A : ℝ → ℝ → ℝ} (hA : ∀ a b, 0 ≤ A a b)
    (M : StationaryForwardMatching α β) : 0 ≤ palmKinetic A M :=
  integral_nonneg (fun p => by
    have h1 : 0 ≤ (1 / 2 : ℝ) * A p.1.1 p.2.1 := by
      have hA' := hA p.1.1 p.2.1
      linarith
    have h2 : 0 ≤ edgeDisplacement p ^ 2 := sq_nonneg _
    exact mul_nonneg h1 h2)

/-- The probe is uniformly bounded on the whole carrier by `G`, hence in particular on
`C_w`, as soon as the probe is measurable and bounded by `G`. -/
theorem abs_palmProbe_le {f : MarkedCloudPoint → MarkedCloudPoint → ℝ} {G : ℝ}
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G) (M : StationaryForwardMatching α β) :
    |palmProbe f M| ≤ G := by
  let _ : IsProbabilityMeasure M.palm := M.palm_isProbability
  have hbound : ∀ᵐ p ∂M.palm, ‖f p.1 p.2‖ ≤ G :=
    Eventually.of_forall fun p => by simpa only [Real.norm_eq_abs] using hfG p.1 p.2
  have hint : Integrable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2) M.palm :=
    Integrable.of_bound hf.aestronglyMeasurable G hbound
  have hmono : (∫ p, ‖f p.1 p.2‖ ∂M.palm) ≤
      ∫ _ : MarkedCloudPoint × MarkedCloudPoint, G ∂M.palm :=
    integral_mono_ae hint.norm (integrable_const G) hbound
  have hconst : (∫ _ : MarkedCloudPoint × MarkedCloudPoint, G ∂M.palm) = G := by
    rw [integral_const, smul_eq_mul]
    simp
  calc |palmProbe f M| = ‖∫ p, f p.1 p.2 ∂M.palm‖ := by
        simp only [palmProbe, Real.norm_eq_abs]
    _ ≤ ∫ p, ‖f p.1 p.2‖ ∂M.palm := norm_integral_le_integral_norm _
    _ ≤ G := by rw [← hconst]; exact hmono

/-- The second-moment class is contained in the weighted class: a finite unweighted
second moment and a measurable coefficient bounded above by `C` give a finite weighted
kinetic mean.  This is the paper's `C_2 ⊆ C_w`. -/
theorem finiteSecondMoment_subset_finiteWeightedKinetic
    {A : ℝ → ℝ → ℝ} {C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    {M : StationaryForwardMatching α β} (hM : FiniteSecondMoment M) :
    FiniteWeightedKinetic A M := by
  have hC : 0 ≤ C := (hA_nonneg 0 0).trans (hA_bound 0 0)
  have hsq_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint =>
      edgeDisplacement p ^ 2) := by
    unfold edgeDisplacement
    exact ((measurable_fst.comp measurable_snd).sub
      (measurable_fst.comp measurable_fst)).pow_const 2
  have hw_meas : AEStronglyMeasurable (kineticIntegrand A) M.palm := by
    unfold kineticIntegrand
    exact (((hA_meas.const_mul (1 / 2 : ℝ)).mul hsq_meas).aestronglyMeasurable)
  refine (hM.const_mul (C / 2)).mono' hw_meas ?_
  filter_upwards with p
  have hsq : 0 ≤ edgeDisplacement p ^ 2 := sq_nonneg _
  have hAn : 0 ≤ A p.1.1 p.2.1 := hA_nonneg _ _
  have hAb : A p.1.1 p.2.1 ≤ C := hA_bound _ _
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hnonneg : 0 ≤ kineticIntegrand A p := by
    unfold kineticIntegrand
    exact mul_nonneg (mul_nonneg hhalf hAn) hsq
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  have hbound : kineticIntegrand A p ≤ C / 2 * edgeDisplacement p ^ 2 := by
    unfold kineticIntegrand edgeDisplacement
    calc (1 / 2 : ℝ) * A p.1.1 p.2.1 * (p.2.1 - p.1.1) ^ 2
        ≤ (1 / 2 : ℝ) * C * (p.2.1 - p.1.1) ^ 2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hAb hhalf) hsq
      _ = C / 2 * (p.2.1 - p.1.1) ^ 2 := by ring
  exact hbound

/-- On the second-moment class the weighted kinetic energy is controlled by the
unweighted second moment: `K ≤ (C/2) 𝔼^S[D²]` when `0 ≤ A ≤ C`.  Together with
`palmKinetic_nonneg` this is the quantitative form of `C_2 ⊆ C_w`. -/
theorem palmKinetic_le_half_mul_secondMoment
    {A : ℝ → ℝ → ℝ} {C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    {M : StationaryForwardMatching α β} (hM : FiniteSecondMoment M) :
    palmKinetic A M ≤ C / 2 * ∫ p, edgeDisplacement p ^ 2 ∂M.palm := by
  have hw : Integrable (kineticIntegrand A) M.palm :=
    finiteSecondMoment_subset_finiteWeightedKinetic hA_meas hA_nonneg hA_bound hM
  have hmono : palmKinetic A M ≤
      ∫ p : MarkedCloudPoint × MarkedCloudPoint,
        C / 2 * edgeDisplacement p ^ 2 ∂M.palm :=
    integral_mono hw (hM.const_mul (C / 2)) (fun p => by
      have hsq : 0 ≤ edgeDisplacement p ^ 2 := sq_nonneg _
      have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
      unfold kineticIntegrand
      calc (1 / 2 : ℝ) * A p.1.1 p.2.1 * edgeDisplacement p ^ 2
          ≤ (1 / 2 : ℝ) * C * edgeDisplacement p ^ 2 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA_bound _ _) hhalf) hsq
        _ = C / 2 * edgeDisplacement p ^ 2 := by ring)
  rwa [integral_const_mul] at hmono

/-- The weighted stationary class `C_w`, as a set of stationary forward perfect
matchings with finite weighted kinetic mean. -/
def weightedClass (α β : Measure UnitMark) (A : ℝ → ℝ → ℝ) :
    Set (StationaryForwardMatching α β) :=
  {M | FiniteWeightedKinetic A M}

/-- The second-moment stationary class `C_2`, as a set of stationary forward perfect
matchings with finite unweighted second moment. -/
def secondMomentClass (α β : Measure UnitMark) : Set (StationaryForwardMatching α β) :=
  {M | FiniteSecondMoment M}

/-! ## The stationary pressure datum -/

/-- The `StationaryPressureDatum` of the stationary forward matching class.

The coefficient `A` is measurable, nonnegative and bounded above by `C`; the probe `f`
is measurable and bounded by `G`; `competitor` and `competitor2` are members of the two
classes with kinetic energy at most `C_b`.  The last two hypotheses are the paper's
finite-second-moment competitors; their construction from a stationary finite-second-
moment two-color scheme is not formalized here. -/
def stationaryForwardDatum
    (A : ℝ → ℝ → ℝ) (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) {G Cb C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    (competitor : StationaryForwardMatching α β)
    (hcompetitor : FiniteWeightedKinetic A competitor)
    (hcompetitor_K : palmKinetic A competitor ≤ Cb)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    (hcompetitor2_K : palmKinetic A competitor2 ≤ Cb) :
    StationaryPressureDatum (StationaryForwardMatching α β) G Cb where
  K := palmKinetic A
  P := palmProbe f
  Cw := weightedClass α β A
  C2 := secondMomentClass α β
  C2_subset_Cw := fun _ hM =>
    finiteSecondMoment_subset_finiteWeightedKinetic hA_meas hA_nonneg hA_bound hM
  kinetic_nonneg := fun M _ => palmKinetic_nonneg hA_nonneg M
  probe_bound := fun M _ => abs_palmProbe_le hf hfG M
  competitor := competitor
  competitor_mem := hcompetitor
  kinetic_competitor_le := hcompetitor_K
  competitor2 := competitor2
  competitor2_mem := hcompetitor2
  kinetic_competitor2_le := hcompetitor2_K

/-- The weighted stationary pressure `I_w(v) = inf_{C_w} (K + v P)`, the paper's
`I_{j,w}(z,v)`. -/
def weightedStationaryPressure (α β : Measure UnitMark) (A : ℝ → ℝ → ℝ)
    (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) (v : ℝ) : ℝ :=
  stationaryValue (palmKinetic A) (palmProbe f) (weightedClass α β A) v

/-- The second-moment stationary pressure `I_2(v) = inf_{C_2} (K + v P)`, the paper's
`I_{j,2}(z,v)`. -/
def secondMomentStationaryPressure (α β : Measure UnitMark) (A : ℝ → ℝ → ℝ)
    (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) (v : ℝ) : ℝ :=
  stationaryValue (palmKinetic A) (palmProbe f) (secondMomentClass α β) v

/-- The datum's weighted value is the weighted stationary pressure. -/
theorem stationaryForwardDatum_Iw
    (A : ℝ → ℝ → ℝ) (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) {G Cb C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    (competitor : StationaryForwardMatching α β)
    (hcompetitor : FiniteWeightedKinetic A competitor)
    (hcompetitor_K : palmKinetic A competitor ≤ Cb)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    (hcompetitor2_K : palmKinetic A competitor2 ≤ Cb) (v : ℝ) :
    (stationaryForwardDatum A f hA_meas hA_nonneg hA_bound hf hfG competitor hcompetitor
      hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K).Iw v =
      weightedStationaryPressure α β A f v := rfl

/-- The datum's second-moment value is the second-moment stationary pressure. -/
theorem stationaryForwardDatum_I2
    (A : ℝ → ℝ → ℝ) (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) {G Cb C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    (competitor : StationaryForwardMatching α β)
    (hcompetitor : FiniteWeightedKinetic A competitor)
    (hcompetitor_K : palmKinetic A competitor ≤ Cb)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    (hcompetitor2_K : palmKinetic A competitor2 ≤ Cb) (v : ℝ) :
    (stationaryForwardDatum A f hA_meas hA_nonneg hA_bound hf hfG competitor hcompetitor
      hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K).I2 v =
      secondMomentStationaryPressure α β A f v := rfl

/-- The paper's chain `-|v| G ≤ I_w ≤ I_2 ≤ C_b + |v| G` for the stationary forward
matching classes. -/
theorem neg_abs_mul_le_weighted_le_secondMoment_le_upper
    (A : ℝ → ℝ → ℝ) (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) {G Cb C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    (competitor : StationaryForwardMatching α β)
    (hcompetitor : FiniteWeightedKinetic A competitor)
    (hcompetitor_K : palmKinetic A competitor ≤ Cb)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    (hcompetitor2_K : palmKinetic A competitor2 ≤ Cb) (v : ℝ) :
    -(|v| * G) ≤ weightedStationaryPressure α β A f v ∧
      weightedStationaryPressure α β A f v ≤ secondMomentStationaryPressure α β A f v ∧
      secondMomentStationaryPressure α β A f v ≤ Cb + |v| * G := by
  let D := stationaryForwardDatum A f hA_meas hA_nonneg hA_bound hf hfG competitor
    hcompetitor hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K
  have h := StationaryPressureDatum.neg_abs_mul_le_Iw_le_I2_le_upper D v
  rwa [stationaryForwardDatum_Iw A f hA_meas hA_nonneg hA_bound hf hfG competitor
      hcompetitor hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K v,
    stationaryForwardDatum_I2 A f hA_meas hA_nonneg hA_bound hf hfG competitor
      hcompetitor hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K v] at h

/-- The weighted stationary pressure is at most the second-moment value: `I_w ≤ I_2`. -/
theorem weightedStationaryPressure_le_secondMoment
    (A : ℝ → ℝ → ℝ) (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) {G Cb C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    (competitor : StationaryForwardMatching α β)
    (hcompetitor : FiniteWeightedKinetic A competitor)
    (hcompetitor_K : palmKinetic A competitor ≤ Cb)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    (hcompetitor2_K : palmKinetic A competitor2 ≤ Cb) (v : ℝ) :
    weightedStationaryPressure α β A f v ≤ secondMomentStationaryPressure α β A f v :=
  (neg_abs_mul_le_weighted_le_secondMoment_le_upper A f hA_meas hA_nonneg hA_bound hf hfG
    competitor hcompetitor hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K v).2.1

/-- The growth bound `|I_w(v)| ≤ C_b + |v| G`. -/
theorem abs_weightedStationaryPressure_le
    (A : ℝ → ℝ → ℝ) (f : MarkedCloudPoint → MarkedCloudPoint → ℝ) {G Cb C : ℝ}
    (hA_meas : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => A p.1.1 p.2.1))
    (hA_nonneg : ∀ a b, 0 ≤ A a b) (hA_bound : ∀ a b, A a b ≤ C)
    (hf : Measurable (fun p : MarkedCloudPoint × MarkedCloudPoint => f p.1 p.2))
    (hfG : ∀ x y, |f x y| ≤ G)
    (competitor : StationaryForwardMatching α β)
    (hcompetitor : FiniteWeightedKinetic A competitor)
    (hcompetitor_K : palmKinetic A competitor ≤ Cb)
    (competitor2 : StationaryForwardMatching α β)
    (hcompetitor2 : FiniteSecondMoment competitor2)
    (hcompetitor2_K : palmKinetic A competitor2 ≤ Cb) (v : ℝ) :
    |weightedStationaryPressure α β A f v| ≤ Cb + |v| * G := by
  let D := stationaryForwardDatum A f hA_meas hA_nonneg hA_bound hf hfG competitor
    hcompetitor hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K
  have h := StationaryPressureDatum.abs_Iw_le D v
  rwa [stationaryForwardDatum_Iw A f hA_meas hA_nonneg hA_bound hf hfG competitor
      hcompetitor hcompetitor_K competitor2 hcompetitor2 hcompetitor2_K v] at h

end StationaryForwardMatching

open StationaryForwardMatching

/-! ## The root family and the Campbell-averaged stationary pressure -/

section Atlas

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- The root family of source-Palm kinetic energies induced by a root-dependent
calibrated coefficient `A j z`. -/
def stationaryForwardKineticFamily (α β : Measure UnitMark)
    (A : ℕ → Z → ℝ → ℝ → ℝ) : ℕ → Z → StationaryForwardMatching α β → ℝ :=
  fun j z M => palmKinetic (A j z) M

/-- The root family of source-Palm probes induced by a root-dependent probe `f j z`. -/
def stationaryForwardProbeFamily (α β : Measure UnitMark)
    (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) :
    ℕ → Z → StationaryForwardMatching α β → ℝ :=
  fun j z M => palmProbe (f j z) M

/-- The root family of weighted stationary classes `C_w(j,z)`. -/
def stationaryForwardWeightedClass (α β : Measure UnitMark)
    (A : ℕ → Z → ℝ → ℝ → ℝ) : ℕ → Z → Set (StationaryForwardMatching α β) :=
  fun j z => weightedClass α β (A j z)

/-- The stationary pressure family `I_{j,w}(z,v)` induced by the stationary forward
matchings: at each root it is the infimum of kinetic energy plus tilt times probe over
the finite-weighted-kinetic class. -/
def stationaryForwardPressureFamily (α β : Measure UnitMark)
    (A : ℕ → Z → ℝ → ℝ → ℝ) (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ) :
    ℕ → Z → ℝ → ℝ :=
  stationaryPressureFamily (stationaryForwardKineticFamily α β A)
    (stationaryForwardProbeFamily α β f) (stationaryForwardWeightedClass α β A)

omit [MeasurableSpace Z] in
/-- At each root the stationary forward pressure family is exactly the weighted
stationary pressure for the corresponding coefficient and probe. -/
theorem stationaryForwardPressureFamily_apply (α β : Measure UnitMark)
    (A : ℕ → Z → ℝ → ℝ → ℝ) (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (j : ℕ) (z : Z) (v : ℝ) :
    stationaryForwardPressureFamily α β A f j z v =
      weightedStationaryPressure α β (A j z) (f j z) v := rfl

/-- The Campbell-averaged stationary infimum `𝒫_w(t)` of `main.tex`
(`general-gluing-integrated-pressures`): the population atlas pressure with local
weighted stationary values `I_{j,w}(z, t θ_j(z)^{2/q})`.

This is the quantity `Pw` in the finite-domination/Campbell lower comparison below;
the comparison itself is not derived here. -/
noncomputable def campbellAveragedStationaryPressure (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (A : ℕ → Z → ℝ → ℝ → ℝ) (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q t : ℝ) : ℝ :=
  populationAtlasPressure P a κ lambda (stationaryForwardPressureFamily α β A f) q t

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- Unfolded form of the Campbell-averaged stationary pressure: each root contributes
`θ^(-2/q)` against the original root measure times the weighted stationary value at tilt `t θ^(2/q)`. -/
theorem campbellAveragedStationaryPressure_def (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (A : ℕ → Z → ℝ → ℝ → ℝ) (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    (q t : ℝ) :
    campbellAveragedStationaryPressure α β P a κ lambda A f q t =
      ∑' j, ∫ z in populationSeedRootPiece P a κ lambda j,
        populationAtlasTheta P a κ lambda j z ^ (-2 / q) *
          weightedStationaryPressure α β (A j z) (f j z)
            (t * populationAtlasTheta P a κ lambda j z ^ (2 / q)) ∂lambda := by
  simp only [campbellAveragedStationaryPressure, populationAtlasPressure_def,
    populationAtlasIntegrand_def]
  apply tsum_congr
  intro j
  apply integral_congr_ae
  filter_upwards with z
  rw [stationaryForwardPressureFamily_apply]

end Atlas

/-! ## Finite domination and the Campbell lower comparison

The paper's pathwise lower bound for actual empirical optimizers
(`general-gluing-probability-lower`) is obtained in two steps.

1. *Finite domination* (`general-gluing-finite-domination`).  For a fixed compact
   nonnegative frozen core cost `F_{R,N}` and clip `N`, the rooted empirical scene law
   `Γ_n` satisfies `Γ_n(F_{R,N}) ≤ V_n(t) + B_t + o_ℙ(1)`, where `B_t = |t| ‖f‖_∞`.
   This uses disjoint source-core assignment, the relative expansion of the kinetic
   cost on compact collars, coefficient and probe continuity, and local count moment
   bounds.

2. *Campbell lower comparison*.  Passing to a subsequential limit of the rooted scene
   laws, the limit has independent unit-intensity marked Poisson inputs and a perfect
   forward stationary matching (input differentiation, Efron--Stein, invariant-partition
   removal, partner retention).  Campbell's formula then identifies the limiting frozen
   core cost as the source-Palm average of the kinetic-plus-probe cost, giving
   `V + B_t ≥ 𝒫_w(t) + B_t`, i.e. the second hypothesis below with `Pw = 𝒫_w(t)`.

Both steps are stated as explicit hypotheses.  Only their elementary combination and
the final passage from an almost-sure eventual bound to the paper's probability
statement are proved here; the Campbell/rooted-scene/perfect-matching content is not
faked.
-/

section FiniteDomination

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The pathwise finite-domination inequality: for every tolerance `ε`, eventually
almost surely the frozen core cost is at most the normalized empirical pressure plus
the probe constant `B` and `ε`.  This is `main.tex`, `general-gluing-finite-domination`;
`frozenCost n x` is the clipped compact core sum `Γ_n(F_{R,N})` and `Vn n x` is the
normalized empirical pressure `V_n(t)`. -/
def FiniteDominationInequality (P : Measure Ω) (frozenCost Vn : ℕ → Ω → ℝ) (B : ℝ) :
    Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ᵐ x ∂P, frozenCost n x ≤ Vn n x + B + ε

/-- The Campbell lower comparison: eventually almost surely the frozen core cost is at
least the Campbell-averaged stationary infimum `Pw` plus `B`, up to every tolerance.
This is the conclusion of applying Campbell's formula to the stationary limit of the
rooted empirical scene laws; it is an explicit hypothesis here. -/
def CampbellLowerComparison (P : Measure Ω) (frozenCost : ℕ → Ω → ℝ) (Pw B : ℝ) :
    Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ᵐ x ∂P, Pw + B - ε ≤ frozenCost n x

/-- Every empirical optimizer's normalized pressure is asymptotically at least the
Campbell-averaged stationary infimum, almost surely: for every `ε > 0`, eventually
`V_n(t) ≥ Pw - ε`. -/
def EmpiricalPressureLowerComparison (P : Measure Ω) (Vn : ℕ → Ω → ℝ) (Pw : ℝ) : Prop :=
  ∀ ε > 0, ∀ᵐ x ∂P, ∀ᶠ n in atTop, Pw - ε ≤ Vn n x

/-- The paper's probability form of the lower bound: for every `η > 0`,
`ℙ(V_n(t) < 𝒫_w(t) - η) → 0`. -/
def EmpiricalPressureProbabilityLower (P : Measure Ω) (Vn : ℕ → Ω → ℝ) (Pw : ℝ) : Prop :=
  ∀ η > 0, Tendsto (fun n => P {x | Vn n x < Pw - η}) atTop (𝓝 0)

/-- Finite domination and the Campbell lower comparison combine to give the almost-sure
asymptotic lower bound: the constants `B` cancel. -/
theorem empiricalPressureLowerComparison_of_finiteDomination
    {P : Measure Ω} {frozenCost Vn : ℕ → Ω → ℝ} {Pw B : ℝ}
    (hdom : FiniteDominationInequality P frozenCost Vn B)
    (hcamp : CampbellLowerComparison P frozenCost Pw B) :
    EmpiricalPressureLowerComparison P Vn Pw := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  have hmain : ∀ᶠ n in atTop, ∀ᵐ x ∂P, Pw - ε ≤ Vn n x := by
    filter_upwards [hdom (ε / 2) hε2, hcamp (ε / 2) hε2] with n hd hc
    filter_upwards [hd, hc] with x hdx hcx
    linarith
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hmain
  have hEach : ∀ n : ℕ, ∀ᵐ x ∂P, (n ≥ N → Pw - ε ≤ Vn n x) := by
    intro n
    by_cases hn : N ≤ n
    · filter_upwards [hN n hn] with x hx
      exact fun _ => hx
    · exact ae_of_all _ (fun _ h => absurd h hn)
  have hall : ∀ᵐ x ∂P, ∀ n, (n ≥ N → Pw - ε ≤ Vn n x) := ae_all_iff.2 hEach
  filter_upwards [hall] with x hx
  exact Filter.eventually_atTop.2 ⟨N, fun n hn => hx n hn⟩

/-- An almost-sure eventual lower bound yields the paper's probability statement
`ℙ(V_n(t) < 𝒫_w(t) - η) → 0`.  This is the final "subsequence criterion" step of
`general-gluing-probability-lower`; it only needs measurability of the empirical
pressures. -/
theorem empiricalPressureProbabilityLower_of_ae
    {P : Measure Ω} [IsProbabilityMeasure P] {Vn : ℕ → Ω → ℝ} {Pw : ℝ}
    (hmeas : ∀ n, Measurable (Vn n))
    (h : EmpiricalPressureLowerComparison P Vn Pw) :
    EmpiricalPressureProbabilityLower P Vn Pw := by
  intro η hη
  have hlim : ∀ᵐ x ∂P, ∀ᶠ n in atTop,
      (x ∈ {x | Vn n x < Pw - η} ↔ x ∈ (∅ : Set Ω)) := by
    filter_upwards [h η hη] with x hx
    filter_upwards [hx] with n hn
    simp only [mem_empty_iff_false]
    exact ⟨fun hlt => absurd hlt (not_lt.mpr hn), fun h => h.elim⟩
  have hAs : ∀ n, MeasurableSet {x | Vn n x < Pw - η} := fun n =>
    measurableSet_lt (hmeas n) measurable_const
  have ht := tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure
    (L := atTop) (μ := P) (A := (∅ : Set Ω))
    (As := fun n => {x | Vn n x < Pw - η}) MeasurableSet.empty hAs hlim
  simpa using ht

/-- The complete interface: finite domination plus the Campbell lower comparison imply
the paper's probability lower bound.  The two hypotheses are exactly the analytic
inputs not formalized in this module. -/
theorem empiricalPressureProbabilityLower_of_finiteDomination
    {P : Measure Ω} [IsProbabilityMeasure P] {frozenCost Vn : ℕ → Ω → ℝ} {Pw B : ℝ}
    (hmeas : ∀ n, Measurable (Vn n))
    (hdom : FiniteDominationInequality P frozenCost Vn B)
    (hcamp : CampbellLowerComparison P frozenCost Pw B) :
    EmpiricalPressureProbabilityLower P Vn Pw :=
  empiricalPressureProbabilityLower_of_ae hmeas
    (empiricalPressureLowerComparison_of_finiteDomination hdom hcamp)

end FiniteDomination

/-! ## The probability lower bound with the Campbell-averaged stationary infimum -/

section AtlasProbabilityLower

variable {E M Z Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace Ω]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

omit [FiniteDimensional ℝ E] [BorelSpace E] [T2Space M] [PreconnectedSpace M]
  [MeasurableSpace M] [BorelSpace M] in
/-- The paper's probability lower bound `ℙ(V_n(t) < 𝒫_w(t) - η) → 0`
(`general-gluing-probability-lower`) with the comparison value instantiated as the
Campbell-averaged stationary infimum `campbellAveragedStationaryPressure`.

The two hypotheses are the finite-domination inequality and the Campbell lower
comparison of the previous section; neither is derived here. -/
theorem campbellAveragedStationaryPressure_probabilityLower
    (α β : Measure UnitMark)
    (P : ℕ → F.CalibratedSeedWindow u) (a : M → Z)
    (κ : ∀ j, Measure (P j).seed.covector.ker) (lambda : Measure Z)
    (A : ℕ → Z → ℝ → ℝ → ℝ) (f : ℕ → Z → MarkedCloudPoint → MarkedCloudPoint → ℝ)
    {q t : ℝ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {frozenCost Vn : ℕ → Ω → ℝ} {B : ℝ}
    (hmeas : ∀ n, Measurable (Vn n))
    (hdom : FiniteDominationInequality μ frozenCost Vn B)
    (hcamp : CampbellLowerComparison μ frozenCost
      (campbellAveragedStationaryPressure α β P a κ lambda A f q t) B) :
    EmpiricalPressureProbabilityLower μ Vn
      (campbellAveragedStationaryPressure α β P a κ lambda A f q t) :=
  empiricalPressureProbabilityLower_of_finiteDomination hmeas hdom hcamp

end AtlasProbabilityLower

end OTSelector.PointProcess
