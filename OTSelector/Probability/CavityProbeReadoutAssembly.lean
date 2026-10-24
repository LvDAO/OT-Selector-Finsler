import OTSelector.Probability.CavityProbeReadout
import OTSelector.Probability.CavitySemidiscreteLegalActualCycleLimit

/-!
# Assembly of the rooted-scene probe readout

This module continues `CavityProbeReadout` by assembling the stochastic inputs
of the readout from the actual cavity scene machinery.

## Step (b): limit-scene rigidity

* `cavityCountableSceneLawRootMeasure` is the countable rooted scene law with
  the uniform root `cavityRootMeasure`, and
  `map_cavityCountableSceneLawRootMeasure_pair` shows that forgetting the
  integer cloud and the target coordinate gives exactly the two-plan scene law.
* `ae_cavityRootedCountableScene_limit_plans_eq_of_energy` takes the actual
  countable scene law along a weakly convergent sequence and derives the three
  hypotheses of `ae_cavityRootedCountableScene_limit_plans_eq` almost surely:
  the source-marginal identity from the displacement energy, the two-cycle
  monotonicity of the average support from the actual opposite-tilt optimality,
  and the common countable target support.  The atomlessness of the limiting
  cost differences remains an explicit hypothesis `hatom` (in the paper it
  follows from the diffuse source and nonconstant polynomial level sets).
* `exists_subseq_cavityRootedCountableScene_limit_plans_eq` extracts the weak
  subsequence with `exists_tendsto_subseq_cavityRootedCountableSceneLaw` and
  applies the assembly along it.

## Step (a) revisited: the single-level readout comparison

`abs_probeDifference_sub_rootAverageTest_le` compares the difference of the two
probe costs with the difference of the two root-averaged windowed mark tests,
with error twice the boundary-layer defect.  Its random form
`abs_cavityRandomProbeDifference_sub_sceneTest_le` and the integration lemma
`abs_integral_sub_integral_le_of_abs_le` turn this into the expectation-level
estimate used by the final theorem.

## Step (2): the one-dimensional boundary-layer estimate

For a cube `cavitySpatialCube L = [0,L]^ι` in dimension one, the root-window
defect of a window supported in the ball of radius `R`, with integral one, is at
most `2 R / L` times its total absolute mass
(`cavityRootWindowError_cavitySpatialCube_le`); along `L n → ∞` the defect
therefore vanishes (`tendsto_cavityRootWindowError_cavitySpatialCube`).

## Step (3): uniform boundedness of the rooted window test

`setIntegral_abs_comp_sub_le_of_support` bounds the mass a compactly supported
window sees in *any* source window by its height times the volume of its support
ball.  Consequently `abs_integral_cavityMarkWindowTest_le` bounds the rooted
plan's mark-window test by `Cg * Cη * |B_R|`, uniformly in the scale `N`, the
root `z` and the allocation.  This is the uniform boundedness input needed for
the weak-topology passage.

Note that a mark-only probe does not see the target spatial coordinate at all,
so the target-cutoff/long-edge tail is vacuous for the readout test itself; the
energy long-edge bound is used where it is genuinely needed, in the
source-marginal identity of step (b), through
`ae_actualRootedScene_equal_source_marginals_of_energy`.

## Step (4): the environment-level readout

`tendsto_expectedProbeDifference_of_sceneTest` assembles the a.e. pointwise
comparison, its integration, and the squeeze
`tendsto_probeDifference_of_scene_squeeze`: if the boundary-layer defect and the
expected scene-test difference both vanish, then the expected probe-cost
difference `q_n^+ - q_n^-` tends to zero.

## Remaining gap

Two inputs are stated explicitly rather than derived here.

* The multivariate cube estimate.  Only the one-dimensional case `[Unique ι]`
  is formalized.  For general `ι` the same argument applies with the product
  cube `[0,L]^ι`, whose boundary layer has volume `L^d - (L - 2R)^d`; the
  missing work is the product-measure version of
  `volume_cavitySpatialCube_diff_inner_le`, not a new idea.
* The derivation of `hscene` from the weak limit.  The ingredients are now
  available: `LocalFiniteMeasure.continuous_testIntegral` gives continuity of
  `π ↦ ∫ f dπ` for a compactly supported continuous `f`, and
  `abs_integral_cavityMarkWindowTest_le` gives the uniform bound on the rooted
  window test.  What is not yet formalized is the bounded-continuous
  approximation/Portmanteau step: truncate the probe in the (compactly
  generated, tight) source mark to make the test compactly supported, use
  `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` on the bounded
  continuous truncation, and evaluate the limit integral to zero using the
  a.e. plan equality `ae_cavityRootedCountableScene_limit_plans_eq_of_energy`.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

section Assembly

variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [CompactSpace B] [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

open PointProcess PointProcess.LocalConfiguration

local instance assemblyBorelTarget : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance assemblyConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance assemblyConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance assemblyConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance assemblyPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance assemblyCloudPolish : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The countable rooted scene law with the actual uniform root of total mass
`N` and domain `D` of volume `N`. -/
def cavityCountableSceneLawRootMeasure {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ))
    (hD : volume D = ENNReal.ofReal N) :
    ProbabilityMeasure (CavityCountableTargetScene (A := A) base) :=
  letI := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  cavityRootedCountableSceneLaw base P μ (cavityRootMeasure volume D N) p hp
    aplus aminus hplusm hminusm Y hY N

/-- Forgetting the integer cloud and the target coordinate of the countable
rooted scene law gives exactly the actual two-plan scene law. -/
theorem map_cavityCountableSceneLawRootMeasure_pair {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ))
    (hD : volume D = ENNReal.ofReal N) :
    letI := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
    ProbabilityMeasure.map
      (cavityCountableSceneLawRootMeasure base P μ p hp aplus aminus
        hplusm hminusm Y hY N hN D hD)
      (f := fun s : CavityCountableTargetScene (A := A) base ↦ (s.1.1, s.1.2.1))
      ((by fun_prop : Measurable (fun s : CavityCountableTargetScene (A := A) base ↦
          (s.1.1, s.1.2.1))).aemeasurable) =
      cavityRootedLocalSceneLaw P μ aplus aminus hplusm hminusm Y hY N hN D hD := by
  letI := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  apply Subtype.ext
  let pairProj : CavityCountableTargetScene (A := A) base →
      CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) :=
    fun s ↦ (s.1.1, s.1.2.1)
  have hpair : Measurable pairProj := by fun_prop
  change (Measure.map pairProj
    (Measure.map (cavityRootedCountableScene base μ p aplus aminus Y N)
      (P.prod (cavityRootMeasure volume D N)))) = _
  rw [Measure.map_map hpair
    (measurable_cavityRootedCountableScene base μ p hp aplus aminus hplusm hminusm Y hY N)]
  rfl

set_option maxHeartbeats 2000000 in
/-- **Step (b): the actual scene inputs, assembled.**  For a weak limit `Q` of the
countable rooted scenes, the displacement energy makes the two source marginals
agree, the actual opposite-tilt optimality makes the average support
two-cyclically monotone, and both plans are supported over the same countable
target cloud.  Countable-target rigidity then gives equality of the two limiting
plans almost surely.  The atomlessness of the limiting cost differences is kept
as an explicit hypothesis. -/
theorem ae_cavityRootedCountableScene_limit_plans_eq_of_energy
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (henv : ∀ n, MeasurePreserving (fun ω ↦ (p n ω, Y n ω)) (P n)
      ((dirichletOne (m n)).prod (Measure.pi (fun _ : Fin (m n + 1) ↦ ν n))))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (D : ℕ → Set (ι → ℝ))
    (hν : ∀ n, (ν n).map Prod.fst =
      (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ • volume.restrict (D n))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (k : A → B → (ι → ℝ) → ℝ)
    (g a₀ : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (htzero : Tendsto t atTop (𝓝 0)) (G : ℝ)
    (hopt : ∀ n, ∀ᵐ ω ∂P n,
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (fun s ↦ a₀ n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + t n * g n (ω, s) j)
        (fun s ↦ aplus n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + (-t n) * g n (ω, s) j)
        (fun s ↦ aminus n (ω, s)) ∧
      (∀ j, Integrable (fun s ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (μ n)) ∧
      (∀ j, Integrable (fun s ↦ g n (ω, s) j) (μ n)) ∧
      (∀ᵐ s ∂μ n, ∀ j, |g n (ω, s) j| ≤ G))
    (hc : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hk : ∀ b, Measurable (fun q : A × (ι → ℝ) ↦ k q.1 b q.2))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ n, (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y n ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aplus n (ω, s)) ∂P n) ≤ C)
    (henergyminus : ∀ n, (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y n ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aminus n (ω, s)) ∂P n) ≤ C)
    (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P n) (μ n)
      (p n) (henv n).measurable.fst (aplus n) (aminus n) (hplusm n) (hminusm n)
      (Y n) (hY n) ((m n : ℝ) + 1) (by positivity) (D n) (hD n)) atTop (𝓝 Q))
    (hatom : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      ∀ y₁ y₂ : (ι → ℝ) × B, y₁ ≠ y₂ →
        multiplicity s.2 y₁ ≠ 0 → multiplicity s.2 y₂ ≠ 0 →
        NullSingletonClass
          (((s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst).map
            (fun x ↦ cavitySpatialDifferenceCost k x y₁ -
              cavitySpatialDifferenceCost k x y₂))) :
    ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1 := by
  let N : ℕ → ℝ := fun n ↦ (m n : ℝ) + 1
  have hNpos : ∀ n, 0 < N n := fun n ↦ by dsimp [N]; positivity
  let pairProj : CavityCountableTargetScene (A := A) base →
      CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) :=
    fun s ↦ (s.1.1, s.1.2.1)
  have hpair_cont : Continuous pairProj :=
    continuous_fst.fst.prodMk continuous_fst.snd.fst
  have hpair : Measurable pairProj := hpair_cont.measurable
  let Qpair : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)) :=
    ProbabilityMeasure.map Q (f := pairProj) hpair.aemeasurable
  have hscene_eq (n : ℕ) :
      ProbabilityMeasure.map
        (cavityCountableSceneLawRootMeasure base (P n) (μ n) (p n)
          (henv n).measurable.fst (aplus n) (aminus n) (hplusm n) (hminusm n)
          (Y n) (hY n) (N n) (hNpos n) (D n) (hD n))
        (f := pairProj) hpair.aemeasurable =
        cavityRootedLocalSceneLaw (P n) (μ n) (aplus n) (aminus n)
          (hplusm n) (hminusm n) (Y n) (hY n) (N n) (hNpos n) (D n) (hD n) :=
    map_cavityCountableSceneLawRootMeasure_pair base (P n) (μ n) (p n)
      (henv n).measurable.fst (aplus n) (aminus n) (hplusm n) (hminusm n)
      (Y n) (hY n) (N n) (hNpos n) (D n) (hD n)
  have hweak_pair :
      Tendsto (fun n ↦ cavityRootedLocalSceneLaw (P n) (μ n) (aplus n) (aminus n)
        (hplusm n) (hminusm n) (Y n) (hY n) (N n) (hNpos n) (D n) (hD n))
        atTop (𝓝 Qpair) := by
    have hmap : Tendsto (fun n ↦ ProbabilityMeasure.map
        (cavityCountableSceneLawRootMeasure base (P n) (μ n) (p n)
          (henv n).measurable.fst (aplus n) (aminus n) (hplusm n) (hminusm n)
          (Y n) (hY n) (N n) (hNpos n) (D n) (hD n))
        (f := pairProj) hpair.aemeasurable) atTop (𝓝 Qpair) :=
      (ProbabilityMeasure.continuous_map (f := pairProj) hpair_cont).tendsto Q |>.comp hweak
    exact hmap.congr' (Eventually.of_forall fun n ↦ hscene_eq n)
  have hsrc_pair := ae_actualRootedScene_equal_source_marginals_of_energy
    (m := m) (P := P) (μ := μ) p Y hY aplus aminus hplusm hminusm hfeas
    D N hNpos hD C hC henergyplus henergyminus Qpair hweak_pair
  have hsrc : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      ((s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst =
        (s.1.2.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst) :=
    ae_of_ae_map (μ := (Q : Measure (CavityCountableTargetScene (A := A) base)))
      hpair.aemeasurable
      (p := fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
        (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst =
          (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst)
      hsrc_pair
  have hcycle_pair := ae_actualRootedScene_average_support_twoCycle
    (m := m) (P := P) (μ := μ) p Y hY k g a₀ aplus aminus hplusm hminusm
    t ht htzero G hopt D N hNpos hD hc Qpair hweak_pair
  have hcycle : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      OTSelector.Reconstruction.IsTwoCycleMonotone (cavitySpatialDifferenceCost k)
        ((LocalFiniteMeasure.cavityAverage (s.1.1, s.1.2.1) : Measure _)).support :=
    ae_of_ae_map (μ := (Q : Measure (CavityCountableTargetScene (A := A) base)))
      hpair.aemeasurable hcycle_pair
  haveI hrootprob : ∀ n, IsProbabilityMeasure
      (cavityRootMeasure volume (D n) (N n)) :=
    fun n ↦ isProbabilityMeasure_cavityRootMeasure volume (D n) (N n) (hNpos n) (hD n)
  have hweak' : Tendsto (fun n ↦ cavityRootedCountableSceneLaw base (P n) (μ n)
      (cavityRootMeasure volume (D n) (N n)) (p n) (henv n).measurable.fst
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n) (N n))
      atTop (𝓝 Q) := by
    simpa only [cavityCountableSceneLawRootMeasure] using hweak
  have hsupp := ae_actualRootedCountableScene_plans_supported base (m := m) P μ
    (fun n ↦ cavityRootMeasure volume (D n) (N n)) p
    (fun n ↦ (henv n).measurable.fst) Y hY aplus aminus hplusm hminusm hfeas
    N Q hweak'
  have hsupp₀ : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1 :=
    hsupp.mono fun s hs ↦ hs.1
  have hsupp₁ : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.2.1 :=
    hsupp.mono fun s hs ↦ hs.2
  exact ae_cavityRootedCountableScene_limit_plans_eq base k hk Q hsrc hcycle
    hsupp₀ hsupp₁ hatom

set_option maxHeartbeats 2000000 in
/-- **Extracted weak-scene form of the assembly.**  From the actual countable
scene law one extracts a weakly convergent subsequence; along it, the assembled
energy/cycle/support inputs and the atomlessness of all possible limit scenes
give equality of the two limiting plans.  The "good limit scenes" hypothesis is
the only model-level input that is not yet derived from the source diffuseness
in this file. -/
theorem exists_subseq_cavityRootedCountableScene_limit_plans_eq
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (henv : ∀ n, MeasurePreserving (fun ω ↦ (p n ω, Y n ω)) (P n)
      ((dirichletOne (m n)).prod (Measure.pi (fun _ : Fin (m n + 1) ↦ ν n))))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (D : ℕ → Set (ι → ℝ))
    (hν : ∀ n, (ν n).map Prod.fst =
      (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ • volume.restrict (D n))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (k : A → B → (ι → ℝ) → ℝ)
    (g a₀ : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (t : ℕ → ℝ) (ht : ∀ n, 0 ≤ t n) (htzero : Tendsto t atTop (𝓝 0)) (G : ℝ)
    (hopt : ∀ n, ∀ᵐ ω ∂P n,
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (fun s ↦ a₀ n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + t n * g n (ω, s) j)
        (fun s ↦ aplus n (ω, s)) ∧
      IsOptimalSemidiscreteAllocation (μ n) (p n ω)
        (fun s j ↦ cavitySpatialDifferenceCost k s (Y n ω j) + (-t n) * g n (ω, s) j)
        (fun s ↦ aminus n (ω, s)) ∧
      (∀ j, Integrable (fun s ↦ cavitySpatialDifferenceCost k s (Y n ω j)) (μ n)) ∧
      (∀ j, Integrable (fun s ↦ g n (ω, s) j) (μ n)) ∧
      (∀ᵐ s ∂μ n, ∀ j, |g n (ω, s) j| ≤ G))
    (hc : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hk : ∀ b, Measurable (fun q : A × (ι → ℝ) ↦ k q.1 b q.2))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ n, (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y n ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aplus n (ω, s)) ∂P n) ≤ C)
    (henergyminus : ∀ n, (∫⁻ ω, ∫⁻ e, ENNReal.ofReal (‖(Y n ω e.2).1 - e.1.1‖ ^ 2)
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aminus n (ω, s)) ∂P n) ≤ C)
    (hatomAll : ∀ (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
      (φ : ℕ → ℕ), StrictMono φ →
      Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P (φ n)) (μ (φ n))
        (p (φ n)) (henv (φ n)).measurable.fst (aplus (φ n)) (aminus (φ n))
        (hplusm (φ n)) (hminusm (φ n)) (Y (φ n)) (hY (φ n))
        ((m (φ n) : ℝ) + 1) (by positivity) (D (φ n)) (hD (φ n))) atTop (𝓝 Q) →
      ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
        ∀ y₁ y₂ : (ι → ℝ) × B, y₁ ≠ y₂ →
          multiplicity s.2 y₁ ≠ 0 → multiplicity s.2 y₂ ≠ 0 →
          NullSingletonClass
            (((s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst).map
              (fun x ↦ cavitySpatialDifferenceCost k x y₁ -
                cavitySpatialDifferenceCost k x y₂))) :
    ∃ Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base),
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P (φ n)) (μ (φ n))
          (p (φ n)) (henv (φ n)).measurable.fst (aplus (φ n)) (aminus (φ n))
          (hplusm (φ n)) (hminusm (φ n)) (Y (φ n)) (hY (φ n))
          ((m (φ n) : ℝ) + 1) (by positivity) (D (φ n)) (hD (φ n))) atTop (𝓝 Q) ∧
        ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
          (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1 := by
  haveI hrootprob : ∀ n, IsProbabilityMeasure
      (cavityRootMeasure volume (D n) ((m n : ℝ) + 1)) :=
    fun n ↦ isProbabilityMeasure_cavityRootMeasure volume (D n) ((m n : ℝ) + 1)
      (by positivity) (hD n)
  obtain ⟨Q, φ, hφ, hweak, _hsupp⟩ :=
    exists_tendsto_subseq_cavityRootedCountableSceneLaw (base := base)
      m P μ ν (fun n ↦ cavityRootMeasure volume (D n) ((m n : ℝ) + 1))
      p Y hY henv aplus aminus hplusm hminusm hfeas D hν
  refine ⟨Q, φ, hφ, ?_, ?_⟩
  · simpa only [cavityCountableSceneLawRootMeasure] using hweak
  · exact ae_cavityRootedCountableScene_limit_plans_eq_of_energy (base := base)
      (m := fun n ↦ m (φ n)) (P := fun n ↦ P (φ n)) (μ := fun n ↦ μ (φ n))
      (ν := fun n ↦ ν (φ n)) (p := fun n ↦ p (φ n)) (Y := fun n ↦ Y (φ n))
      (fun n j ↦ hY (φ n) j) (fun n ↦ henv (φ n))
      (fun n ↦ aplus (φ n)) (fun n ↦ aminus (φ n))
      (fun n j ↦ hplusm (φ n) j) (fun n j ↦ hminusm (φ n) j)
      (fun n ↦ hfeas (φ n)) (D := fun n ↦ D (φ n))
      (fun n ↦ hν (φ n)) (fun n ↦ hD (φ n))
      k (fun n ↦ g (φ n)) (fun n ↦ a₀ (φ n))
      (t := fun n ↦ t (φ n)) (fun n ↦ ht (φ n)) (htzero.comp hφ.tendsto_atTop) G
      (fun n ↦ hopt (φ n)) hc hk C hC
      (fun n ↦ henergyplus (φ n)) (fun n ↦ henergyminus (φ n)) Q
      (by simpa only [cavityCountableSceneLawRootMeasure, Function.comp_apply] using hweak)
      (hatomAll Q φ hφ (by simpa only [cavityCountableSceneLawRootMeasure] using hweak))

end Assembly

section ReadoutComparison

variable {m : ℕ}

/-- **Single-level probe readout comparison.**  For a source law that is the
normalized uniform window on `D` times a mark law, the difference of the two
probe costs differs from the difference of the two root-averaged windowed mark
tests by at most twice the boundary-layer defect.  This is the working form of
the paper's estimate `|q_n^+ - q_n^- - E ∫ η g d(τ Γ_n^+ - τ Γ_n^-)| ≤ 2 C G / L_n`;
both signs are compared separately by
`abs_rootAverage_markWindowTest_sub_probe_le`. -/
theorem abs_probeDifference_sub_rootAverageTest_le
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N)
    (hD : volume D = ENNReal.ofReal N)
    (hμ : μ = (ENNReal.ofReal N)⁻¹ • ((volume.restrict D).prod α))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (aplus aminus : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun s ↦ aplus s j))
    (hminusm : ∀ j, Measurable (fun s ↦ aminus s j))
    {p : Fin (m + 1) → ℝ}
    (hplus : IsSemidiscreteAllocation μ p aplus)
    (hminus : IsSemidiscreteAllocation μ p aminus)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη) :
    |(semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aplus -
        semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aminus)
      - ((∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aplus Y N z)) ∂cavityRootMeasure volume D N)
        - (∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aminus Y N z)) ∂cavityRootMeasure volume D N))|
    ≤ 2 * Cg * cavityRootWindowError η D N := by
  have hplus' := abs_rootAverage_markWindowTest_sub_probe_le μ α D N hN hD hμ
    gm hgm Cg hgmb Y aplus hplusm hplus η hη Cη hηb
  have hminus' := abs_rootAverage_markWindowTest_sub_probe_le μ α D N hN hD hμ
    gm hgm Cg hgmb Y aminus hminusm hminus η hη Cη hηb
  have hEq : (semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aplus -
        semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aminus)
      - ((∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aplus Y N z)) ∂cavityRootMeasure volume D N)
        - (∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aminus Y N z)) ∂cavityRootMeasure volume D N))
      = -(((∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aplus Y N z)) ∂cavityRootMeasure volume D N)
          - semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aplus)
        + (semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aminus
          - (∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aminus Y N z)) ∂cavityRootMeasure volume D N))) := by
    ring
  rw [hEq, abs_neg]
  calc
    |((∫ z, (∫ e, cavityMarkWindowTest η gm e
            ∂(cavitySpatialRootedPlan μ aplus Y N z)) ∂cavityRootMeasure volume D N)
        - semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aplus)
      + (semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aminus
        - (∫ z, (∫ e, cavityMarkWindowTest η gm e
            ∂(cavitySpatialRootedPlan μ aminus Y N z)) ∂cavityRootMeasure volume D N))|
        ≤ |(∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aplus Y N z)) ∂cavityRootMeasure volume D N)
            - semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aplus|
          + |semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aminus
            - (∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aminus Y N z)) ∂cavityRootMeasure volume D N)| :=
      abs_add_le _ _
    _ = |(∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aplus Y N z)) ∂cavityRootMeasure volume D N)
            - semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aplus|
          + |(∫ z, (∫ e, cavityMarkWindowTest η gm e
              ∂(cavitySpatialRootedPlan μ aminus Y N z)) ∂cavityRootMeasure volume D N)
            - semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aminus| := by
      rw [abs_sub_comm (semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) aminus)]
    _ ≤ Cg * cavityRootWindowError η D N + Cg * cavityRootWindowError η D N :=
      add_le_add hplus' hminus'
    _ = 2 * Cg * cavityRootWindowError η D N := by ring

/-- The random probe-cost difference at a fixed environment. -/
def cavityRandomProbeDifference {Ω : Type*} {m : ℕ} (μ : Measure ((ι → ℝ) × A))
    (gm : A → B → ℝ) (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ) (ω : Ω) : ℝ :=
  semidiscreteAllocationCost μ (cavityMarkProbeCost gm (Y ω))
      (fun s ↦ aplus (ω, s)) -
    semidiscreteAllocationCost μ (cavityMarkProbeCost gm (Y ω))
      (fun s ↦ aminus (ω, s))

/-- The random difference of the two root-averaged windowed mark tests. -/
def cavityRandomSceneTestDifference {Ω : Type*} {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) (D : Set (ι → ℝ)) (N : ℝ)
    (η : (ι → ℝ) → ℝ) (gm : A → B → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ) (ω : Ω) : ℝ :=
  (∫ z, (∫ e, cavityMarkWindowTest η gm e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z))
    ∂cavityRootMeasure volume D N) -
  (∫ z, (∫ e, cavityMarkWindowTest η gm e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z))
    ∂cavityRootMeasure volume D N)

/-- **Random form of the probe readout comparison**, obtained from
`abs_probeDifference_sub_rootAverageTest_le` by specializing the allocations at
the environment `ω`. -/
theorem abs_cavityRandomProbeDifference_sub_sceneTest_le {Ω : Type*}
    [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N)
    (hD : volume D = ENNReal.ofReal N)
    (hμ : μ = (ENNReal.ofReal N)⁻¹ • ((volume.restrict D).prod α))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (p : Fin (m + 1) → ℝ) (ω : Ω)
    (hplus : IsSemidiscreteAllocation μ p (fun s ↦ aplus (ω, s)))
    (hminus : IsSemidiscreteAllocation μ p (fun s ↦ aminus (ω, s)))
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη) :
    |cavityRandomProbeDifference μ gm Y aplus aminus ω -
        cavityRandomSceneTestDifference μ D N η gm Y aplus aminus ω|
      ≤ 2 * Cg * cavityRootWindowError η D N := by
  simpa only [cavityRandomProbeDifference, cavityRandomSceneTestDifference] using
    abs_probeDifference_sub_rootAverageTest_le μ α D N hN hD hμ gm hgm Cg hgmb
      (Y ω) (fun s ↦ aplus (ω, s)) (fun s ↦ aminus (ω, s))
      (fun j ↦ (hplusm j).comp (measurable_const.prodMk measurable_id))
      (fun j ↦ (hminusm j).comp (measurable_const.prodMk measurable_id))
      hplus hminus η hη Cη hηb

/-- Integrating an almost sure absolute bound bounds the difference of integrals. -/
theorem abs_integral_sub_integral_le_of_abs_le {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P) (C : ℝ)
    (h : ∀ᵐ ω ∂P, |f ω - g ω| ≤ C) :
    |(∫ ω, f ω ∂P) - (∫ ω, g ω ∂P)| ≤ C := by
  have hdiff : Integrable (fun ω ↦ f ω - g ω) P := hf.sub hg
  calc
    |(∫ ω, f ω ∂P) - (∫ ω, g ω ∂P)|
        = |∫ ω, (f ω - g ω) ∂P| := by rw [integral_sub hf hg]
    _ ≤ ∫ ω, |f ω - g ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, C ∂P := by
      apply integral_mono_ae hdiff.abs (integrable_const C)
      exact h
    _ = C := by
      rw [integral_const]
      simp [Measure.restrict_apply_univ, measureReal_def]

/-- A compactly supported window can be integrated over any source window at
uniform cost: the total absolute mass it sees is at most its height times the
volume of its support ball, independently of the source window. -/
theorem setIntegral_abs_comp_sub_le_of_support
    (η : (ι → ℝ) → ℝ) (Cη R : ℝ) (D : Set (ι → ℝ)) (z : ι → ℝ)
    (hη : Integrable η volume)
    (hηb : ∀ x, |η x| ≤ Cη)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0) :
    ∫ x in D, |η (x - z)| ≤ Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal := by
  have hcomp : Integrable (fun x : ι → ℝ => |η (x - z)|) volume :=
    (hη.comp_sub_right z).abs
  have hreal : volume (Metric.closedBall (0 : ι → ℝ) R) ≠ ⊤ :=
    (ProperSpace.isCompact_closedBall (0 : ι → ℝ) R).measure_lt_top.ne
  have hsupp0 : ∀ x, x ∉ Metric.closedBall (0 : ι → ℝ) R → |η x| = 0 := by
    intro x hx
    rw [hηsupp x hx, abs_zero]
  have hind : Integrable
      ((Metric.closedBall (0 : ι → ℝ) R).indicator (fun _ => (1 : ℝ))) volume :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const hreal (by simp))
  have hmaj : Integrable (fun x : ι → ℝ =>
      Cη * (Metric.closedBall (0 : ι → ℝ) R).indicator (fun _ => (1 : ℝ)) x) volume :=
    hind.const_mul Cη
  calc
    ∫ x in D, |η (x - z)|
        ≤ ∫ x, |η (x - z)| :=
      setIntegral_le_integral hcomp (Eventually.of_forall fun x ↦ abs_nonneg _)
    _ = ∫ x, |η x| := integral_sub_right_eq_self (fun x ↦ |η x|) z
    _ ≤ ∫ x, Cη * (Metric.closedBall (0 : ι → ℝ) R).indicator
          (fun _ => (1 : ℝ)) x := by
      apply integral_mono_ae hη.abs hmaj
      filter_upwards with x
      by_cases hx : x ∈ Metric.closedBall (0 : ι → ℝ) R
      · rw [Set.indicator_of_mem hx, mul_one]
        exact hηb x
      · rw [Set.indicator_of_notMem hx, mul_zero]
        exact le_of_eq (hsupp0 x hx)
    _ = Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal := by
      rw [integral_const_mul,
        integral_indicator_const (1 : ℝ) measurableSet_closedBall]
      simp [measureReal_def, smul_eq_mul]

/-- **Uniform bound for the rooted window test.**  For a window supported in the
ball of radius `R` with height `Cη` and a mark probe bounded by `Cg`, the rooted
plan's test integral is bounded by `Cg Cη |B_R|`, *uniformly in the scale `N`,
the root `z` and the allocation*.  This is the uniform boundedness input for
passing the scene test functional through the weak topology: unlike the crude
`N Cg Cη` bound, it does not grow with the scene scale. -/
theorem abs_integral_cavityMarkWindowTest_le {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N)
    (hD : volume D = ENNReal.ofReal N)
    (hμ : μ = (ENNReal.ofReal N)⁻¹ • ((volume.restrict D).prod α))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun s ↦ a s j))
    (p : Fin (m + 1) → ℝ) (ha : IsSemidiscreteAllocation μ p a)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (z : ι → ℝ) :
    |∫ e, cavityMarkWindowTest η gm e ∂(cavitySpatialRootedPlan μ a Y N z)|
      ≤ Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal := by
  let h : (ι → ℝ) × A → ℝ := fun s ↦
    ∑ j, a s j * (η (s.1 - z) * gm s.2 (Y j).2)
  have hroot := integral_cavityMarkWindowTest_cavitySpatialRootedPlan μ gm hgm Cg hgmb
    Y a ha η hη Cη hηb N hN.le z
  have hcost : N * semidiscreteAllocationCost μ
      (fun s j ↦ η (s.1 - z) * gm s.2 (Y j).2) a
      = ∫ s, h s ∂((volume.restrict D).prod α) := by
    unfold semidiscreteAllocationCost
    rw [hμ, integral_smul_measure, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal hN.le, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ hN.ne', one_mul]
  have hcne : (ENNReal.ofReal N)⁻¹ ≠ 0 := by
    rw [ENNReal.inv_ne_zero]
    exact ENNReal.ofReal_ne_top
  have hnonneg : ∀ᵐ s ∂((volume.restrict D).prod α), ∀ j, 0 ≤ a s j := by
    rw [← Measure.ae_ennreal_smul_measure_iff (c := (ENNReal.ofReal N)⁻¹) hcne, ← hμ]
    exact ha.nonneg
  have hsum : ∀ᵐ s ∂((volume.restrict D).prod α), ∑ j, a s j = 1 := by
    rw [← Measure.ae_ennreal_smul_measure_iff (c := (ENNReal.ofReal N)⁻¹) hcne, ← hμ]
    exact ha.sum_one
  have hbound_ae : ∀ᵐ s ∂((volume.restrict D).prod α),
      |h s| ≤ Cg * |η (s.1 - z)| := by
    filter_upwards [hnonneg, hsum] with s hn hs
    calc
      |h s| = |∑ j, a s j * (η (s.1 - z) * gm s.2 (Y j).2)| := rfl
      _ ≤ ∑ j, |a s j * (η (s.1 - z) * gm s.2 (Y j).2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, a s j * (|η (s.1 - z)| * |gm s.2 (Y j).2|) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hn j)]
      _ ≤ ∑ j, a s j * (|η (s.1 - z)| * Cg) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hgmb _ _) (abs_nonneg _)) (hn j)
      _ = (∑ j, a s j) * (|η (s.1 - z)| * Cg) := by rw [Finset.sum_mul]
      _ = Cg * |η (s.1 - z)| := by rw [hs, one_mul]; ring
  have hηint' : Integrable (fun s : (ι → ℝ) × A ↦ Cg * |η (s.1 - z)|)
      ((volume.restrict D).prod α) := by
    have hx : Integrable (fun x : ι → ℝ ↦ |η (x - z)|) (volume.restrict D) :=
      (hηint.comp_sub_right z).abs.mono_measure (Measure.restrict_le_self)
    exact (hx.comp_fst α).const_mul Cg
  haveI hvol : IsFiniteMeasure (volume.restrict D) := by
    constructor
    rw [Measure.restrict_apply_univ, hD]
    exact ENNReal.ofReal_lt_top
  haveI hfinprod : IsFiniteMeasure ((volume.restrict D).prod α) := inferInstance
  have hCg : 0 ≤ Cg := by
    have hne : (Set.univ : Set A).Nonempty :=
      nonempty_of_measure_ne_zero (μ := α) (by simp)
    obtain ⟨a₀, -⟩ := hne
    exact le_trans (abs_nonneg _) (hgmb a₀ (Y 0).2)
  have hInt : Integrable h ((volume.restrict D).prod α) := by
    refine Integrable.of_bound ?_ (Cg * Cη) ?_
    · exact (Finset.measurable_sum _ fun j _ ↦ (ham j).mul
        ((hη.comp (measurable_fst.sub measurable_const)).mul
          (measurable_cavityMarkProbeCost gm hgm Y j))).aestronglyMeasurable
    · filter_upwards [hbound_ae] with s hs
      rw [Real.norm_eq_abs]
      exact hs.trans (mul_le_mul_of_nonneg_left (hηb (s.1 - z)) hCg)
  have hmain : |∫ s, h s ∂((volume.restrict D).prod α)|
      ≤ Cg * ∫ x in D, |η (x - z)| := by
    calc
      |∫ s, h s ∂((volume.restrict D).prod α)|
          ≤ ∫ s, |h s| ∂((volume.restrict D).prod α) := abs_integral_le_integral_abs
      _ ≤ ∫ s, Cg * |η (s.1 - z)| ∂((volume.restrict D).prod α) :=
        integral_mono_ae hInt.abs hηint' hbound_ae
      _ = Cg * ∫ s, |η (s.1 - z)| ∂((volume.restrict D).prod α) :=
        integral_const_mul Cg _
      _ = Cg * ∫ x in D, |η (x - z)| := by
        congr 1
        have hprod := integral_prod_mul (μ := volume.restrict D) (ν := α)
          (f := fun x : ι → ℝ ↦ |η (x - z)|) (g := fun _ : A ↦ (1 : ℝ))
        have hα1 : α.real Set.univ = 1 := by
          rw [measureReal_def, measure_univ]
          simp
        simpa [hα1] using hprod
  have hCg : 0 ≤ Cg := by
    have hne : (Set.univ : Set A).Nonempty :=
      nonempty_of_measure_ne_zero (μ := α) (by simp)
    obtain ⟨a₀, -⟩ := hne
    exact le_trans (abs_nonneg _) (hgmb a₀ (Y 0).2)
  rw [hroot, hcost]
  calc
    |∫ s, h s ∂((volume.restrict D).prod α)|
        ≤ Cg * ∫ x in D, |η (x - z)| := hmain
    _ ≤ Cg * (Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal) :=
      mul_le_mul_of_nonneg_left
        (setIntegral_abs_comp_sub_le_of_support η Cη R D z hηint hηb hηsupp) hCg
    _ = Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal := by ring

/-- **Environment-level probe readout (scene-test form).**  For a source law that
is the normalized uniform window on `D n` times a fixed mark law, a.e. feasible
opposite-tilt allocations, a vanishing boundary-layer defect and a vanishing
expected scene-test difference, the expected probe-cost difference tends to
zero.  This is the final squeeze of the paper's readout argument; the two
remaining inputs are stated explicitly:
* `herror`: the geometric cube estimate (`cavityRootWindowError → 0`), proved in
  one dimension by `tendsto_cavityRootWindowError_cavitySpatialCube`;
* `hscene`: the expected scene-test difference, which is the root-averaged
  windowed mark-test difference.  Deriving it from the weak limit requires the
  target-cutoff/Portmanteau step described in the module documentation. -/
theorem tendsto_expectedProbeDifference_of_sceneTest
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (hμsrc : ∀ n, μ n = (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ •
      ((volume.restrict (D n)).prod α))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hintp : ∀ n, Integrable (fun ω ↦ cavityRandomProbeDifference (μ n) gm
      (Y n) (aplus n) (aminus n) ω) (P n))
    (hints : ∀ n, Integrable (fun ω ↦ cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω) (P n))
    (herror : Tendsto (fun n ↦ 2 * Cg * cavityRootWindowError η (D n)
      ((m n : ℝ) + 1)) atTop (𝓝 0))
    (hscene : Tendsto (fun n ↦ ∫ ω, cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω ∂P n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ ω, cavityRandomProbeDifference (μ n) gm (Y n)
      (aplus n) (aminus n) ω ∂P n) atTop (𝓝 0) := by
  have hpoint : ∀ n, ∀ᵐ ω ∂P n,
      |cavityRandomProbeDifference (μ n) gm (Y n) (aplus n) (aminus n) ω -
        cavityRandomSceneTestDifference (μ n) (D n) ((m n : ℝ) + 1) η gm
          (Y n) (aplus n) (aminus n) ω|
        ≤ 2 * Cg * cavityRootWindowError η (D n) ((m n : ℝ) + 1) := by
    intro n
    filter_upwards [hfeas n] with ω hω
    exact abs_cavityRandomProbeDifference_sub_sceneTest_le (μ n) α (D n)
      ((m n : ℝ) + 1) (by positivity) (hD n) (hμsrc n) gm hgm Cg hgmb
      (Y n) (aplus n) (aminus n) (hplusm n) (hminusm n) (p n ω) ω hω.1 hω.2
      η hη Cη hηb
  have hbound : ∀ n, |(∫ ω, cavityRandomProbeDifference (μ n) gm (Y n)
        (aplus n) (aminus n) ω ∂P n)
      - (∫ ω, cavityRandomSceneTestDifference (μ n) (D n) ((m n : ℝ) + 1) η gm
          (Y n) (aplus n) (aminus n) ω ∂P n)|
      ≤ 2 * Cg * cavityRootWindowError η (D n) ((m n : ℝ) + 1) := fun n ↦
    abs_integral_sub_integral_le_of_abs_le (P n) _ _ (hintp n) (hints n) _
      (hpoint n)
  exact tendsto_probeDifference_of_scene_squeeze _ _ _ herror hscene
    (Eventually.of_forall hbound)

end ReadoutComparison

section GeometricOneDimensional

open scoped Pointwise

variable [Unique ι]

/-- The spatial cube `[0,L]^ι`. -/
def cavitySpatialCube (L : ℝ) : Set (ι → ℝ) := Set.Icc (0 : ι → ℝ) (fun _ => L)

/-- The inner cube at distance `R` from the boundary. -/
def cavitySpatialInner (R L : ℝ) : Set (ι → ℝ) :=
  Set.Icc (fun _ => R) (fun _ => L - R)

/-- The lower boundary slab of width `R`. -/
def cavitySpatialLowerSlab (R : ℝ) : Set (ι → ℝ) :=
  Set.Icc (0 : ι → ℝ) (fun _ => R)

/-- The upper boundary slab of width `R`. -/
def cavitySpatialUpperSlab (R L : ℝ) : Set (ι → ℝ) :=
  Set.Icc (fun _ => L - R) (fun _ => L)

/-- The one-dimensional cube has volume `L`. -/
theorem volume_cavitySpatialCube {L : ℝ} (hL : 0 ≤ L) :
    volume (cavitySpatialCube (ι := ι) L) = ENNReal.ofReal L := by
  rw [cavitySpatialCube, Real.volume_Icc_pi]
  simp [hL]

/-- The lower slab has volume `R`. -/
theorem volume_cavitySpatialLowerSlab {R : ℝ} (hR : 0 ≤ R) :
    volume (cavitySpatialLowerSlab (ι := ι) R) = ENNReal.ofReal R := by
  rw [cavitySpatialLowerSlab, Real.volume_Icc_pi]
  simp [hR]

/-- The upper slab has volume `R`. -/
theorem volume_cavitySpatialUpperSlab {R L : ℝ} :
    volume (cavitySpatialUpperSlab (ι := ι) R L) = ENNReal.ofReal R := by
  rw [cavitySpatialUpperSlab, Real.volume_Icc_pi]
  have h : L - (L - R) = R := by ring
  simp [h]

/-- The cube minus its inner cube is contained in the two boundary slabs. -/
theorem cavitySpatialCube_diff_inner_subset {R L : ℝ} (hR : 0 ≤ R) :
    cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L ⊆
      cavitySpatialLowerSlab (ι := ι) R ∪ cavitySpatialUpperSlab (ι := ι) R L := by
  intro x hx
  obtain ⟨hxcube, hxinner⟩ := hx
  obtain ⟨hx0, hxL⟩ := Set.mem_Icc.mp hxcube
  by_cases hlo : x default < R
  · exact Or.inl (Set.mem_Icc.mpr ⟨hx0, fun i ↦ by
      rw [Subsingleton.elim i default]
      exact le_of_lt hlo⟩)
  · have hge : R ≤ x default := le_of_not_gt hlo
    have hhi : L - R < x default := by
      by_contra hnot
      have hxle : x default ≤ L - R := le_of_not_gt hnot
      exact hxinner (Set.mem_Icc.mpr ⟨fun i ↦ by
        rw [Subsingleton.elim i default]
        exact hge, fun i ↦ by
        rw [Subsingleton.elim i default]
        exact hxle⟩)
    exact Or.inr (Set.mem_Icc.mpr ⟨fun i ↦ by
      rw [Subsingleton.elim i default]
      exact le_of_lt hhi, hxL⟩)

/-- The boundary layer has volume at most `2R`. -/
theorem volume_cavitySpatialCube_diff_inner_le {R L : ℝ} (hR : 0 ≤ R) :
    volume (cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L) ≤
      ENNReal.ofReal (2 * R) := by
  calc
    volume (cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L)
        ≤ volume (cavitySpatialLowerSlab (ι := ι) R ∪
            cavitySpatialUpperSlab (ι := ι) R L) :=
      measure_mono (cavitySpatialCube_diff_inner_subset hR)
    _ ≤ volume (cavitySpatialLowerSlab (ι := ι) R) +
          volume (cavitySpatialUpperSlab (ι := ι) R L) := measure_union_le _ _
    _ = ENNReal.ofReal R + ENNReal.ofReal R := by
      rw [volume_cavitySpatialLowerSlab hR, volume_cavitySpatialUpperSlab]
    _ = ENNReal.ofReal (2 * R) := by
      rw [← ENNReal.ofReal_add hR hR]
      congr 1
      ring

/-- Reflection identifies `{x} - D` with the preimage of `D` under `u ↦ x - u`. -/
theorem cavitySpatialCube_reflect_preimage (L : ℝ) (x : ι → ℝ) :
    ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L =
      (fun u ↦ x - u) ⁻¹' cavitySpatialCube (ι := ι) L := by
  ext u
  simp only [Set.mem_sub, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, rfl, d, hd, hsub⟩
    rw [← hsub]
    rwa [sub_sub_cancel]
  · intro hu
    exact ⟨x, rfl, x - u, hu, by rw [sub_sub_cancel]⟩

/-- The windowed integral over the cube is the integral over the reflected cube. -/
theorem integral_cavitySpatialCube_window_eq (η : (ι → ℝ) → ℝ) (L : ℝ) (x : ι → ℝ) :
    ∫ z in cavitySpatialCube (ι := ι) L, η (x - z) =
      ∫ u in ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L, η u := by
  have hDmeas : MeasurableSet (cavitySpatialCube (ι := ι) L) := measurableSet_Icc
  have hreflect : ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L =
      (fun u ↦ x - u) ⁻¹' cavitySpatialCube (ι := ι) L :=
    cavitySpatialCube_reflect_preimage L x
  have hreflect_meas : MeasurableSet
      (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L) := by
    rw [hreflect]
    exact hDmeas.preimage (measurable_const.sub measurable_id)
  rw [← integral_indicator hDmeas, ← integral_indicator hreflect_meas]
  have h := integral_sub_left_eq_self
    (f := fun u ↦ (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L).indicator
      η u) (μ := volume) x
  rw [← h]
  apply integral_congr_ae
  filter_upwards with a
  by_cases ha : a ∈ cavitySpatialCube (ι := ι) L
  · have hm : x - a ∈ ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L :=
      ⟨x, rfl, a, ha, rfl⟩
    rw [Set.indicator_of_mem ha, Set.indicator_of_mem hm]
  · have hm : x - a ∉ ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L := by
      rintro ⟨x', hx', d, hd, hxd⟩
      rw [Set.mem_singleton_iff.mp hx'] at hxd
      rw [sub_right_inj.mp hxd] at hd
      exact ha hd
    rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem hm]

/-- On the inner cube the reflected cube contains the support ball, so the
windowed integral is exactly the total integral of the window. -/
theorem integral_cavitySpatialCube_window_eq_one (η : (ι → ℝ) → ℝ) (L R : ℝ)
    (x : ι → ℝ) (hηint : ∫ u, η u = 1)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (hx : x ∈ cavitySpatialInner (ι := ι) R L) :
    ∫ z in cavitySpatialCube (ι := ι) L, η (x - z) = 1 := by
  rw [integral_cavitySpatialCube_window_eq]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hηint
  · intro u hu
    apply hηsupp u
    intro huR
    apply hu
    have hu_norm : ‖u‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using huR
    have hu_abs : |u default| ≤ R := by
      rw [Pi.norm_def] at hu_norm
      simpa using hu_norm
    have hu_le : u default ≤ R := (abs_le.mp hu_abs).2
    have hu_ge : -R ≤ u default := (abs_le.mp hu_abs).1
    have hxR : R ≤ x default := (Set.mem_Icc.mp hx).1 default
    have hxLR : x default ≤ L - R := (Set.mem_Icc.mp hx).2 default
    have hmem : x - u ∈ cavitySpatialCube (ι := ι) L := by
      refine Set.mem_Icc.mpr ⟨Pi.le_def.mpr (fun i ↦ ?_), Pi.le_def.mpr (fun i ↦ ?_)⟩
      · rw [Subsingleton.elim i default]
        simp only [Pi.sub_apply, Pi.zero_apply]
        linarith
      · rw [Subsingleton.elim i default]
        simp only [Pi.sub_apply]
        linarith
    refine ⟨x, rfl, x - u, hmem, ?_⟩
    change x - (x - u) = u
    rw [sub_sub_cancel]

/-- Pointwise defect bound: the windowed integral differs from one by at most
the total absolute mass of the window. -/
theorem abs_integral_cavitySpatialCube_window_sub_one_le (η : (ι → ℝ) → ℝ) (L : ℝ)
    (x : ι → ℝ) (hη : Integrable η) (hηint : ∫ u, η u = 1) :
    |(∫ z in cavitySpatialCube (ι := ι) L, η (x - z)) - 1| ≤ ∫ u, |η u| := by
  rw [integral_cavitySpatialCube_window_eq, ← hηint]
  have hDmeas : MeasurableSet (cavitySpatialCube (ι := ι) L) := measurableSet_Icc
  have hreflect_meas : MeasurableSet
      (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L) := by
    rw [cavitySpatialCube_reflect_preimage]
    exact hDmeas.preimage (measurable_const.sub measurable_id)
  have hcompl := integral_add_compl (μ := volume) hreflect_meas hη
  have hEq : (∫ u in ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L, η u) -
      ∫ u, η u = -∫ u in (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L)ᶜ, η u := by
    linarith
  rw [hEq, abs_neg]
  calc
    |∫ u in (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L)ᶜ, η u|
        ≤ ∫ u in (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L)ᶜ, |η u| :=
      abs_integral_le_integral_abs
    _ ≤ ∫ u, |η u| :=
      setIntegral_le_integral hη.abs (Eventually.of_forall fun u ↦ abs_nonneg (η u))

/-- **One-dimensional boundary-layer estimate.**  For a cube `[0,L]` and a window
supported in the ball of radius `R` with total integral one, the root-window
defect is at most `2 R / L` times the total absolute mass of the window. -/
theorem cavityRootWindowError_cavitySpatialCube_le (η : (ι → ℝ) → ℝ) (L R : ℝ)
    (hR : 0 ≤ R) (hL : 0 < L) (hRL : R ≤ L)
    (hη : Integrable η) (hηm : Measurable η)
    (hηint : ∫ u, η u = 1)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0) :
    cavityRootWindowError η (cavitySpatialCube (ι := ι) L) L
      ≤ (2 * R / L) * ∫ u, |η u| := by
  let A : ℝ := ∫ u, |η u|
  have hA : 0 ≤ A := integral_nonneg fun u ↦ abs_nonneg (η u)
  let defect : (ι → ℝ) → ℝ :=
    fun x ↦ |(∫ z in cavitySpatialCube (ι := ι) L, η (x - z)) - 1|
  have hdefect_bound : ∀ x, defect x ≤ A := fun x ↦
    abs_integral_cavitySpatialCube_window_sub_one_le η L x hη hηint
  have hdefect_meas : Measurable defect := by
    have hjoint : Measurable (fun p : (ι → ℝ) × (ι → ℝ) ↦ η (p.1 - p.2)) :=
      hηm.comp (measurable_fst.sub measurable_snd)
    have hparam : Measurable
        (fun x : ι → ℝ ↦ ∫ z in cavitySpatialCube (ι := ι) L, η (x - z)) :=
      (hjoint.stronglyMeasurable.integral_prod_right'
        (ν := volume.restrict (cavitySpatialCube (ι := ι) L))).measurable
    exact continuous_abs.measurable.comp (hparam.sub measurable_const)
  haveI hfin : IsFiniteMeasure (volume.restrict (cavitySpatialCube (ι := ι) L)) := by
    constructor
    rw [Measure.restrict_apply_univ, volume_cavitySpatialCube (ι := ι) hL.le]
    exact ENNReal.ofReal_lt_top
  have hdefect_int : IntegrableOn defect (cavitySpatialCube (ι := ι) L) volume :=
    Integrable.of_bound hdefect_meas.aestronglyMeasurable A
      (Eventually.of_forall fun x ↦ by
        have hx : 0 ≤ defect x := abs_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg hx]
        exact hdefect_bound x)
  have hinner_sub : cavitySpatialInner (ι := ι) R L ⊆ cavitySpatialCube (ι := ι) L := by
    intro x hx
    obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hx
    refine Set.mem_Icc.mpr ⟨Pi.le_def.mpr (fun i ↦ ?_), Pi.le_def.mpr (fun i ↦ ?_)⟩
    · simpa using le_trans hR (h1 i)
    · simpa using le_trans (h2 i) (by linarith : L - R ≤ L)
  have hinner_meas : MeasurableSet (cavitySpatialInner (ι := ι) R L) := measurableSet_Icc
  have hdiff_meas : MeasurableSet (cavitySpatialCube (ι := ι) L \
      cavitySpatialInner (ι := ι) R L) := measurableSet_Icc.diff hinner_meas
  haveI hfindiff : IsFiniteMeasure
      (volume.restrict (cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono Set.sdiff_subset) (by
      rw [volume_cavitySpatialCube (ι := ι) hL.le]
      exact ENNReal.ofReal_lt_top)
  have hzero_inner : ∀ x ∈ cavitySpatialInner (ι := ι) R L, defect x = 0 := by
    intro x hx
    dsimp only [defect]
    rw [integral_cavitySpatialCube_window_eq_one η L R x hηint hηsupp hx, sub_self, abs_zero]
  have hsdiff : ∫ x in cavitySpatialCube (ι := ι) L \
        cavitySpatialInner (ι := ι) R L, defect x ∂volume =
      (∫ x in cavitySpatialCube (ι := ι) L, defect x ∂volume) -
        ∫ x in cavitySpatialInner (ι := ι) R L, defect x ∂volume :=
    setIntegral_sdiff (μ := volume) (f := defect) hinner_meas hdefect_int hinner_sub
  have hzero_int : ∫ x in cavitySpatialInner (ι := ι) R L, defect x = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero hzero_inner
  have hle : ∫ x in cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L,
      defect x ≤ ∫ x in cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L, A := by
    apply integral_mono_ae
    · exact hdefect_int.mono_set Set.sdiff_subset
    · exact integrable_const A
    · filter_upwards with x using hdefect_bound x
  have hconst : ∫ x in cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L, A =
      A * (volume (cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L)).toReal := by
    rw [integral_const]
    simp only [Measure.restrict_apply_univ, measureReal_def, smul_eq_mul]
    ring
  have hvol : (volume (cavitySpatialCube (ι := ι) L \
      cavitySpatialInner (ι := ι) R L)).toReal ≤ 2 * R := by
    have h := volume_cavitySpatialCube_diff_inner_le (ι := ι) (L := L) hR
    calc
      (volume (cavitySpatialCube (ι := ι) L \
          cavitySpatialInner (ι := ι) R L)).toReal
          ≤ (ENNReal.ofReal (2 * R)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
      _ = 2 * R := ENNReal.toReal_ofReal (by positivity)
  have hmain : ∫ x in cavitySpatialCube (ι := ι) L, defect x ≤ A * (2 * R) := by
    have hcube : ∫ x in cavitySpatialCube (ι := ι) L, defect x =
        ∫ x in cavitySpatialCube (ι := ι) L \
          cavitySpatialInner (ι := ι) R L, defect x := by
      rw [hsdiff, hzero_int, sub_zero]
    rw [hcube]
    calc
      ∫ x in cavitySpatialCube (ι := ι) L \
            cavitySpatialInner (ι := ι) R L, defect x
          ≤ ∫ x in cavitySpatialCube (ι := ι) L \
              cavitySpatialInner (ι := ι) R L, A := hle
      _ = A * (volume (cavitySpatialCube (ι := ι) L \
                cavitySpatialInner (ι := ι) R L)).toReal := hconst
      _ ≤ A * (2 * R) := mul_le_mul_of_nonneg_left hvol hA
  show L⁻¹ * ∫ x in cavitySpatialCube (ι := ι) L, defect x ≤ (2 * R / L) * A
  calc
    L⁻¹ * ∫ x in cavitySpatialCube (ι := ι) L, defect x
        ≤ L⁻¹ * (A * (2 * R)) := mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hL.le)
    _ = (2 * R / L) * A := by
      field_simp [hL.ne']

/-- **Vanishing of the one-dimensional boundary-layer defect.**  Along cube side
lengths `L n → ∞`, the root-window defect of a fixed compactly supported profile
tends to zero. -/
theorem tendsto_cavityRootWindowError_cavitySpatialCube (η : (ι → ℝ) → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hη : Integrable η) (hηm : Measurable η)
    (hηint : ∫ u, η u = 1)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (hRL : ∀ n, R ≤ L n)
    (hLtop : Tendsto L atTop atTop) :
    Tendsto (fun n ↦ cavityRootWindowError η (cavitySpatialCube (ι := ι) (L n)) (L n))
      atTop (𝓝 0) := by
  have hnonneg : ∀ n, 0 ≤
      cavityRootWindowError η (cavitySpatialCube (ι := ι) (L n)) (L n) := by
    intro n
    exact mul_nonneg (inv_nonneg.mpr (hL n).le) (integral_nonneg fun x ↦ abs_nonneg _)
  have hbdd : ∀ n, cavityRootWindowError η (cavitySpatialCube (ι := ι) (L n)) (L n)
      ≤ (2 * R / L n) * ∫ u, |η u| := fun n ↦
    cavityRootWindowError_cavitySpatialCube_le η (L n) R hR (hL n) (hRL n)
      hη hηm hηint hηsupp
  have hupper : Tendsto (fun n ↦ (2 * R / L n) * ∫ u, |η u|) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ 2 * R / L n) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop hLtop (2 * R)
    simpa using h1.mul_const (∫ u, |η u|)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hnonneg hbdd

end GeometricOneDimensional

end OTSelector.Probability
