import OTSelector.Probability.CavityProbeReadoutFinal
import OTSelector.Probability.CavitySemidiscreteActualScene
import OTSelector.Probability.CavitySemidiscreteCountableScene
import OTSelector.Probability.CavityModelTiltSupergradients

/-!
# Bridge from the countable scene readout to the environment-level probe difference

`CavityProbeReadoutFinal` reduces the stochastic input `hscene` of the readout to
the scene-test integral `∫ s, cavitySceneTestFunctional base φ s ∂Q_n`, where
`Q_n` is the countable rooted scene law.  This module supplies the missing
change-of-variables/Fubini bridge identifying that integral with the
environment-level expectation of `cavityRandomSceneTestDifference`, and combines
it with the Portmanteau passage `tendsto_integral_cavitySceneTestFunctional_of_weak`
and the final squeeze `tendsto_expectedProbeDifference_of_sceneTest`.

The module also proves the multivariate (`[Fintype ι]`) cube boundary-layer
estimate used by the vanishing-window-error input, generalizing the
one-dimensional statements of `CavityProbeReadoutAssembly`, and specializes the
opposite-tilt supergradient construction to the mark probe, identifying
`qpos - qneg` with the environment-level probe difference.

## Main results

* `cavitySceneTestFunctional_cavityRootedCountableScene_eq`: on the feasible
  event, the scene test functional is exactly the difference of the two rooted
  plans' compact-test integrals.
* `abs_semidiscreteAllocationCost_markWindow_le`: the allocation cost of a
  windowed mark probe is bounded by `Cη * Cg` (uniform in the window position).
* `integral_cavitySceneTestFunctional_sceneLaw_eq_randomSceneTestDifference`:
  the scene-law integral of the test functional equals the environment integral
  of `cavityRandomSceneTestDifference` (the `hscene` bridge).
* `tendsto_expectedProbeDifference_of_weak_scene`: the environment-level readout
  `∫ ω, cavityRandomProbeDifference … → 0` from weak convergence of the scene
  laws and the a.e. equality of the limit plans.
* `tendsto_cavityMarkProbeAllocationCost_sub_of_weak_scene_of_atomless`: the
  atomless form of the same readout, deriving the limit-plan equality from
  `hatom` through `ae_cavityRootedCountableScene_limit_plans_eq_of_energy`.
* `markProbe_opposite_tilt_supergradient_pair`: the mark-probe specialization of
  `integral_semidiscreteValue_supergradient_of_tilted_optimal` for an explicit
  allocation family, giving the opposite-tilt supergradient inequalities for
  `cavityMarkProbeAllocationCost`.
* `cavityMarkProbeAllocationCost_sub_eq_randomProbeDifference`: the
  change-of-variables identification of `qpos - qneg` with the expectation of
  `cavityRandomProbeDifference` for the induced environment allocations.
* `tendsto_cavityMarkProbeAllocationCost_sub_of_weak_scene`: the resulting
  `qpos n - qneg n → 0` under the weak-scene readout hypotheses.
* `volume_cavitySpatialCube_sdiff_inner_pi`,
  `cavityRootWindowError_cavitySpatialCube_le_pi`,
  `tendsto_cavityRootWindowError_cavitySpatialCube_pi`: the multivariate cube
  boundary-layer estimate.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

section Pointwise

variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [CompactSpace B] [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

open PointProcess PointProcess.LocalConfiguration

local instance bridgeBorelTarget : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance bridgeConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance bridgeConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance bridgeConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance bridgePlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance bridgeCloudPolish : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- **Pointwise scene identity.**  On the event where both allocations are
semidiscrete allocations, the scene test functional of the countable rooted
scene is the difference of the two rooted plans' compact-test integrals.  The
`finitePlanLocalVersion` wrapper is the rooted plan itself there, because the
rooted plans are finite measures. -/
theorem cavitySceneTestFunctional_cavityRootedCountableScene_eq
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsFiniteMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (N : ℝ) (ω : Ω) (z : ι → ℝ)
    {pm : Fin (m + 1) → ℝ}
    (hplus : IsSemidiscreteAllocation μ pm (fun s ↦ aplus (ω, s)))
    (hminus : IsSemidiscreteAllocation μ pm (fun s ↦ aminus (ω, s)))
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ)) :
    cavitySceneTestFunctional base φ
        (cavityRootedCountableScene base μ p aplus aminus Y N (ω, z)) =
      ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) -
        ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) := by
  have hfp : IsFiniteMeasure
      (cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) :=
    hplus.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  have hfm : IsFiniteMeasure
      (cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) :=
    hminus.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  simp only [cavitySceneTestFunctional, cavityRootedCountableScene, cavityRootedLocalScene,
    LocalFiniteMeasure.testIntegral, coe_finitePlanLocalVersion,
    ite_eq_left (measure_lt_top
      (cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) univ),
    ite_eq_left (measure_lt_top
      (cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) univ)]

/-- **Uniform bound for the windowed mark allocation cost.**  For a feasible
allocation, the cost of the windowed mark probe `η (s.1 - z) * gm s.2 (Y j).2`
is bounded by `Cη * Cg`, uniformly in the root `z` and in the target cloud. -/
theorem abs_semidiscreteAllocationCost_markWindow_le {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    {pm : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ pm a)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (z : ι → ℝ) :
    |semidiscreteAllocationCost μ
      (fun s j ↦ η (s.1 - z) * gm s.2 (Y j).2) a| ≤ Cη * Cg := by
  have hc (j : Fin (m + 1)) :
      Integrable (fun s : (ι → ℝ) × A ↦ η (s.1 - z) * gm s.2 (Y j).2) μ :=
    Integrable.of_bound ((hη.comp
        (show Measurable (fun s : (ι → ℝ) × A ↦ s.1 - z) from
          (measurable_fst : Measurable (fun s : (ι → ℝ) × A ↦ s.1)).sub
            measurable_const)).mul
        (measurable_cavityMarkProbeCost gm hgm Y j)).aestronglyMeasurable (Cη * Cg)
      (Eventually.of_forall fun s ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hηb (s.1 - z)) (hgmb s.2 (Y j).2) (abs_nonneg _)
          (le_trans (abs_nonneg _) (hηb (s.1 - z))))
  have hterm (j : Fin (m + 1)) :
      Integrable (fun s ↦ a s j * (η (s.1 - z) * gm s.2 (Y j).2)) μ :=
    ha.integrable_mul _ hc j
  have hsumint : Integrable
      (fun s ↦ ∑ j, a s j * (η (s.1 - z) * gm s.2 (Y j).2)) μ :=
    integrable_finsetSum _ fun j _ ↦ hterm j
  have hbound_ae : ∀ᵐ s ∂μ,
      |∑ j, a s j * (η (s.1 - z) * gm s.2 (Y j).2)| ≤ Cη * Cg := by
    filter_upwards [ha.nonneg, ha.sum_one] with s hn hs
    calc
      |∑ j, a s j * (η (s.1 - z) * gm s.2 (Y j).2)|
          ≤ ∑ j, |a s j * (η (s.1 - z) * gm s.2 (Y j).2)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, a s j * (|η (s.1 - z)| * |gm s.2 (Y j).2|) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul, abs_mul, abs_of_nonneg (hn j)]
      _ ≤ ∑ j, a s j * (Cη * Cg) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul (hηb (s.1 - z)) (hgmb s.2 (Y j).2) (abs_nonneg _)
            (le_trans (abs_nonneg _) (hηb (s.1 - z)))) (hn j)
      _ = Cη * Cg := by rw [← Finset.sum_mul, hs, one_mul]
  unfold semidiscreteAllocationCost
  calc
    |∫ s, ∑ j, a s j * (η (s.1 - z) * gm s.2 (Y j).2) ∂μ|
        ≤ ∫ s, |∑ j, a s j * (η (s.1 - z) * gm s.2 (Y j).2)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _s, Cη * Cg ∂μ :=
      integral_mono_ae hsumint.abs (integrable_const _) hbound_ae
    _ = Cη * Cg := by
      rw [integral_const]
      simp [measureReal_def]

set_option maxHeartbeats 1600000 in
/-- **The `hscene` bridge.**  The scene-law integral of the compact-test
functional equals the environment-level expectation of the root-averaged
random scene-test difference.  The proof is the change-of-variables identity
`integral_cavitySceneTestFunctional_sceneLaw_eq`, Fubini in the root, the
pointwise feasible-event identity, and linearity of the root integral. -/
theorem integral_cavitySceneTestFunctional_sceneLaw_eq_randomSceneTestDifference
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ))
    (hD : volume D = ENNReal.ofReal N)
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)) ∧
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s)))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e) :
    ∫ s, cavitySceneTestFunctional base φ s
        ∂(cavityCountableSceneLawRootMeasure base P μ p hp aplus aminus
          hplusm hminusm Y hY N hN D hD :
          Measure (CavityCountableTargetScene (A := A) base))
      = ∫ ω, cavityRandomSceneTestDifference μ D N η gm Y aplus aminus ω ∂P := by
  let ρ : Measure (ι → ℝ) := cavityRootMeasure volume D N
  haveI hρ : IsProbabilityMeasure ρ :=
    isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  let scene : Ω × (ι → ℝ) → CavityCountableTargetScene (A := A) base :=
    cavityRootedCountableScene base μ p aplus aminus Y N
  have hscene_meas : Measurable scene :=
    measurable_cavityRootedCountableScene base μ p hp aplus aminus hplusm hminusm Y hY N
  let F : CavityCountableTargetScene (A := A) base → ℝ := cavitySceneTestFunctional base φ
  have hFcont : Continuous F := continuous_cavitySceneTestFunctional base φ
  -- Uniform bound on a single rooted plan's test integral.
  have hsingle (ω : Ω) {a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ}
      (ha : IsSemidiscreteAllocation μ (p ω) a) (z : ι → ℝ) :
      |∫ e, φ e ∂(cavitySpatialRootedPlan μ a (Y ω) N z)| ≤ N * (Cη * Cg) := by
    rw [show (fun e ↦ φ e) = (fun e ↦ cavityMarkWindowTest η gm e) from funext hφ,
      integral_cavityMarkWindowTest_cavitySpatialRootedPlan μ gm hgm Cg hgmb (Y ω) a ha
        η hη Cη hηb N hN.le z, abs_mul, abs_of_nonneg hN.le]
    exact mul_le_mul_of_nonneg_left
      (abs_semidiscreteAllocationCost_markWindow_le μ gm hgm Cg hgmb (Y ω) a ha
        η hη Cη hηb z) hN.le
  -- Integrability of the composed scene functional on the product law.
  have hfeas_prod : ∀ᵐ v ∂(P.prod ρ),
      IsSemidiscreteAllocation μ (p v.1) (fun s ↦ aplus (v.1, s)) ∧
      IsSemidiscreteAllocation μ (p v.1) (fun s ↦ aminus (v.1, s)) :=
    (measurePreserving_fst (μ := P) (ν := ρ)).quasiMeasurePreserving.ae hfeas
  have hbound_prod : ∀ᵐ v ∂(P.prod ρ), ‖F (scene v)‖ ≤ 2 * (N * (Cη * Cg)) := by
    filter_upwards [hfeas_prod] with v hv
    obtain ⟨ω, z⟩ := v
    rw [Real.norm_eq_abs, show F (scene (ω, z)) =
        (∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) -
          ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) from
      cavitySceneTestFunctional_cavityRootedCountableScene_eq base μ p Y aplus aminus
        N ω z hv.1 hv.2 φ]
    calc
      |(∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) -
          ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)|
          ≤ |∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)|
            + |∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)| :=
        abs_sub _ _
      _ ≤ N * (Cη * Cg) + N * (Cη * Cg) :=
        add_le_add (hsingle ω hv.1 z) (hsingle ω hv.2 z)
      _ = 2 * (N * (Cη * Cg)) := by ring
  have hFmeas : AEStronglyMeasurable (fun v ↦ F (scene v)) (P.prod ρ) :=
    (hFcont.measurable.comp hscene_meas).aestronglyMeasurable
  have hFint : Integrable (fun v ↦ F (scene v)) (P.prod ρ) :=
    Integrable.of_bound hFmeas _ hbound_prod
  -- Change of variables, then Fubini in the root.
  rw [integral_cavitySceneTestFunctional_sceneLaw_eq base P μ p hp Y hY aplus aminus
    hplusm hminusm N hN D hD φ]
  rw [integral_prod _ hFint]
  apply integral_congr_ae
  filter_upwards [hfeas] with ω hω
  -- Inside a feasible environment, linearity of the root integral.
  have hAwin (z : ι → ℝ) : ∫ e, φ e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) =
      ∫ e, cavityMarkWindowTest η gm e
        ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) :=
    integral_congr_ae (Eventually.of_forall hφ)
  have hBwin (z : ι → ℝ) : ∫ e, φ e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) =
      ∫ e, cavityMarkWindowTest η gm e
        ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) :=
    integral_congr_ae (Eventually.of_forall hφ)
  have hAmeas : AEStronglyMeasurable (fun z : ι → ℝ ↦ ∫ e, φ e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) ρ := by
    have hcostmeas : StronglyMeasurable (fun z : ι → ℝ ↦ semidiscreteAllocationCost μ
        (fun s j ↦ η (s.1 - z) * gm s.2 (Y ω j).2) (fun s ↦ aplus (ω, s))) := by
      have hjoint : StronglyMeasurable
          (fun q : (ι → ℝ) × ((ι → ℝ) × A) ↦
            ∑ j, aplus (ω, q.2) j * (η (q.2.1 - q.1) * gm q.2.2 (Y ω j).2)) := by
        refine Finset.stronglyMeasurable_fun_sum (s := Finset.univ) ?_
        intro j _
        exact ((hplusm j).comp
          (measurable_const.prodMk measurable_snd)).stronglyMeasurable.mul
          (((hη.comp (measurable_snd.fst.sub measurable_fst)).mul
            ((measurable_cavityMarkProbeCost gm hgm (Y ω) j).comp
              measurable_snd)).stronglyMeasurable)
      have := hjoint.integral_prod_right' (ν := μ)
      simpa only [semidiscreteAllocationCost] using this
    have hEq : (fun z : ι → ℝ ↦ ∫ e, φ e
        ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) =
        fun z ↦ N * semidiscreteAllocationCost μ
          (fun s j ↦ η (s.1 - z) * gm s.2 (Y ω j).2) (fun s ↦ aplus (ω, s)) :=
      funext fun z ↦ by
        rw [show (fun e ↦ φ e) = (fun e ↦ cavityMarkWindowTest η gm e) from funext hφ,
          integral_cavityMarkWindowTest_cavitySpatialRootedPlan μ gm hgm Cg hgmb (Y ω)
            (fun s ↦ aplus (ω, s)) hω.1 η hη Cη hηb N hN.le z]
    simpa only [hEq] using (hcostmeas.const_mul N).aestronglyMeasurable
  have hBmeas : AEStronglyMeasurable (fun z : ι → ℝ ↦ ∫ e, φ e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)) ρ := by
    have hcostmeas : StronglyMeasurable (fun z : ι → ℝ ↦ semidiscreteAllocationCost μ
        (fun s j ↦ η (s.1 - z) * gm s.2 (Y ω j).2) (fun s ↦ aminus (ω, s))) := by
      have hjoint : StronglyMeasurable
          (fun q : (ι → ℝ) × ((ι → ℝ) × A) ↦
            ∑ j, aminus (ω, q.2) j * (η (q.2.1 - q.1) * gm q.2.2 (Y ω j).2)) := by
        refine Finset.stronglyMeasurable_fun_sum (s := Finset.univ) ?_
        intro j _
        exact ((hminusm j).comp
          (measurable_const.prodMk measurable_snd)).stronglyMeasurable.mul
          (((hη.comp (measurable_snd.fst.sub measurable_fst)).mul
            ((measurable_cavityMarkProbeCost gm hgm (Y ω) j).comp
              measurable_snd)).stronglyMeasurable)
      have := hjoint.integral_prod_right' (ν := μ)
      simpa only [semidiscreteAllocationCost] using this
    have hEq : (fun z : ι → ℝ ↦ ∫ e, φ e
        ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)) =
        fun z ↦ N * semidiscreteAllocationCost μ
          (fun s j ↦ η (s.1 - z) * gm s.2 (Y ω j).2) (fun s ↦ aminus (ω, s)) :=
      funext fun z ↦ by
        rw [show (fun e ↦ φ e) = (fun e ↦ cavityMarkWindowTest η gm e) from funext hφ,
          integral_cavityMarkWindowTest_cavitySpatialRootedPlan μ gm hgm Cg hgmb (Y ω)
            (fun s ↦ aminus (ω, s)) hω.2 η hη Cη hηb N hN.le z]
    simpa only [hEq] using (hcostmeas.const_mul N).aestronglyMeasurable
  have hAint : Integrable (fun z : ι → ℝ ↦ ∫ e, φ e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) ρ := by
    apply Integrable.of_bound hAmeas (N * (Cη * Cg))
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact hsingle ω hω.1 z
  have hBint : Integrable (fun z : ι → ℝ ↦ ∫ e, φ e
      ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)) ρ := by
    apply Integrable.of_bound hBmeas (N * (Cη * Cg))
    filter_upwards with z
    rw [Real.norm_eq_abs]
    exact hsingle ω hω.2 z
  have hpoint (z : ι → ℝ) : F (scene (ω, z)) =
      (∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) -
        ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) :=
    cavitySceneTestFunctional_cavityRootedCountableScene_eq base μ p Y aplus aminus
      N ω z hω.1 hω.2 φ
  rw [show (fun z ↦ F (scene (ω, z))) = (fun z ↦
      (∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) -
        ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)) from
    funext hpoint,
    integral_sub hAint hBint]
  unfold cavityRandomSceneTestDifference
  rw [show (∫ z, ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)
        ∂cavityRootMeasure volume D N) =
      ∫ z, ∫ e, cavityMarkWindowTest η gm e
        ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)
        ∂cavityRootMeasure volume D N from
    integral_congr_ae (Eventually.of_forall hAwin),
    show (∫ z, ∫ e, φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)
        ∂cavityRootMeasure volume D N) =
      ∫ z, ∫ e, cavityMarkWindowTest η gm e
        ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)
        ∂cavityRootMeasure volume D N from
    integral_congr_ae (Eventually.of_forall hBwin)]

set_option maxHeartbeats 2400000 in
/-- **Environment-level readout from a weakly convergent rooted scene.**  This
closes `hscene`: the weak-scene Portmanteau theorem
`tendsto_integral_cavitySceneTestFunctional_of_weak` gives vanishing of the
scene-test integrals, and the bridge
`integral_cavitySceneTestFunctional_sceneLaw_eq_randomSceneTestDifference`
identifies them with the expected random scene-test differences.  Feeding the
latter into `tendsto_expectedProbeDifference_of_sceneTest` yields the expected
probe-cost difference `q_n^+ - q_n^- → 0`. -/
theorem tendsto_expectedProbeDifference_of_weak_scene
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (hμsrc : ∀ n, μ n = (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ •
      ((volume.restrict (D n)).prod α))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ) (hp : ∀ n, Measurable (p n))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e)
    (hintp : ∀ n, Integrable (fun ω ↦ cavityRandomProbeDifference (μ n) gm
      (Y n) (aplus n) (aminus n) ω) (P n))
    (hints : ∀ n, Integrable (fun ω ↦ cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω) (P n))
    (herror : Tendsto (fun n ↦ 2 * Cg * cavityRootWindowError η (D n)
      ((m n : ℝ) + 1)) atTop (𝓝 0))
    (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P n) (μ n)
      (p n) (hp n) (aplus n) (aminus n) (hplusm n) (hminusm n)
      (Y n) (hY n) ((m n : ℝ) + 1) (by positivity) (D n) (hD n)) atTop (𝓝 Q))
    (hplan : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1) :
    Tendsto (fun n ↦ ∫ ω, cavityRandomProbeDifference (μ n) gm (Y n)
      (aplus n) (aminus n) ω ∂P n) atTop (𝓝 0) := by
  have hscene : Tendsto (fun n ↦ ∫ ω, cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω ∂P n) atTop (𝓝 0) := by
    have h := tendsto_integral_cavitySceneTestFunctional_of_weak (base := base)
      (m := m) P μ α D hD hμsrc p hp Y hY aplus aminus hplusm hminusm hfeas
      gm hgm Cg hgmb η hη Cη hηb hηint R hηsupp φ hφ Q hweak hplan
    refine h.congr' ?_
    filter_upwards with n
    exact integral_cavitySceneTestFunctional_sceneLaw_eq_randomSceneTestDifference
      (base := base) (P := P n) (μ := μ n) (p := p n) (hp := hp n) (Y := Y n)
      (hY := hY n) (aplus := aplus n) (aminus := aminus n) (hplusm := hplusm n)
      (hminusm := hminusm n) ((m n : ℝ) + 1) (by positivity) (D n) (hD n)
      (hfeas n) gm hgm Cg hgmb η hη Cη hηb φ hφ
  exact tendsto_expectedProbeDifference_of_sceneTest (m := m) P μ α D hD hμsrc
    p Y aplus aminus hplusm hminusm hfeas gm hgm Cg hgmb η hη Cη hηb
    hintp hints herror hscene

/-- The allocation induced by a target-cloud allocation family on an
environment `ω` with mass vector `p ω` and target cloud `Y ω`. -/
def cavityEnvironmentAllocation {Ω : Type*} {m : ℕ}
    (alloc : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) ×
      ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (p : Ω → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B)) (ω : Ω) :
    ((ι → ℝ) × A) → Fin (m + 1) → ℝ :=
  fun s ↦ alloc ((Y ω, p ω), s)

/-- **Mark-probe cost bound.**  A feasible allocation's cost against the mark
probe `gm s.2 (Y j).2` is bounded by `Cg`, uniformly in the target cloud. -/
theorem abs_semidiscreteAllocationCost_markProbe_le {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    {pm : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ pm a) :
    |semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) a| ≤ Cg := by
  have h := abs_semidiscreteAllocationCost_markWindow_le (μ := μ) (gm := gm) hgm Cg hgmb
    Y a ha (fun _ ↦ (1 : ℝ)) measurable_const 1 (fun _ ↦ by simp) 0
  show |semidiscreteAllocationCost μ (fun s j ↦ gm s.2 (Y j).2) a| ≤ Cg
  simpa only [one_mul] using h

/-- The expected semidiscrete pressure at tilt `u`, with the mark probe as the
tilt function and the target cloud distributed as `Measure.pi ν`. -/
def cavityMarkProbePressure (m : ℕ) (μ : Measure ((ι → ℝ) × A))
    (ν : Measure ((ι → ℝ) × B)) (k : A → B → (ι → ℝ) → ℝ) (gm : A → B → ℝ)
    (u : ℝ) : ℝ :=
  ∫ z : (Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ),
    semidiscreteValue μ
      (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) + u * gm s.2 ((z.1 j).2)) z.2
    ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)

/-- The expected mark-probe cost of an allocation family on the target-cloud
environment.  This is the `qpos`/`qneg` quantity of the supergradient pair. -/
def cavityMarkProbeAllocationCost {m : ℕ} (μ : Measure ((ι → ℝ) × A))
    (gm : A → B → ℝ) (ν : Measure ((ι → ℝ) × B))
    (A : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) × ((ι → ℝ) × A) →
      Fin (m + 1) → ℝ) : ℝ :=
  ∫ z, semidiscreteAllocationCost μ (fun s j ↦ gm s.2 ((z.1 j).2)) (fun s ↦ A (z, s))
    ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)

set_option maxHeartbeats 1200000 in
/-- **Mark-probe supergradient pair for explicit allocations.**  Specializing
`integral_semidiscreteValue_supergradient_of_tilted_optimal` to the mark probe
`gm s.2 (v j).2` and an explicitly given allocation family, the expected
mark-probe costs of the opposite-tilt optima are supergradients of the expected
pressure at both signs.  Unlike `exists_opposite_tilt_supergradient_pair`, the
allocation family is exposed, so its costs can be matched with the readout. -/
theorem markProbe_opposite_tilt_supergradient_pair
    [StandardBorelSpace ((ι → ℝ) × A)]
    {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (k : A → B → (ι → ℝ) → ℝ)
    (hcost : Continuous (Function.uncurry (cavitySpatialDifferenceCost k)))
    (hcij : ∀ j, Integrable
      (fun z : (Fin (m + 1) → ((ι → ℝ) × B)) × ((ι → ℝ) × A) ↦
        cavitySpatialDifferenceCost k z.2 (z.1 j))
      ((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod μ))
    (hatom : ∀ᵐ v ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)), ∀ j l, j ≠ l →
      NullSingletonClass (μ.map (fun s ↦ cavitySpatialDifferenceCost k s (v j) -
        cavitySpatialDifferenceCost k s (v l))))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ≥0) (hgmb : ∀ a b, |gm a b| ≤ (Cg : ℝ))
    (t : ℕ → ℝ)
    (Aplus Amin : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) ×
      ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hAplusm : ∀ j, Measurable (fun z ↦ Aplus z j))
    (hAminm : ∀ j, Measurable (fun z ↦ Amin z j))
    (hplusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
        (dirichletOne m),
      IsOptimalSemidiscreteAllocation μ z.2
        (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) + t n * gm s.2 ((z.1 j).2))
        (fun s ↦ Aplus (z, s)))
    (hminusopt : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
        (dirichletOne m),
      IsOptimalSemidiscreteAllocation μ z.2
        (fun s j ↦ cavitySpatialDifferenceCost k s (z.1 j) +
          (-t n) * gm s.2 ((z.1 j).2))
        (fun s ↦ Amin (z, s))) :
    (∀ n u, cavityMarkProbePressure m μ ν k gm u ≤
      cavityMarkProbePressure m μ ν k gm (t n) +
        cavityMarkProbeAllocationCost μ gm ν Aplus * (u - t n)) ∧
    (∀ n u, cavityMarkProbePressure m μ ν k gm u ≤
      cavityMarkProbePressure m μ ν k gm (-(t n)) +
        cavityMarkProbeAllocationCost μ gm ν Amin * (u + t n)) := by
  constructor
  · intro n u
    have h := integral_semidiscreteValue_supergradient_of_tilted_optimal
      (m := m) (S := ((ι → ℝ) × A))
      (V := Fin (m + 1) → ((ι → ℝ) × B))
      μ (Measure.pi (fun _ : Fin (m + 1) ↦ ν))
      (fun v j s ↦ cavitySpatialDifferenceCost k s (v j))
      (fun v j s ↦ gm s.2 ((v j).2))
      (fun j ↦ hcost.measurable.comp
        (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)))
      hcij
      (fun j ↦ hgm.comp
        (measurable_snd.snd.prodMk
          (((measurable_pi_apply j).comp measurable_fst).snd)))
      hatom Cg (fun v s j ↦ hgmb s.2 ((v j).2)) Aplus hAplusm
      (t := t n) (hplusopt n)
    simpa only [cavityMarkProbePressure, cavityMarkProbeAllocationCost, mul_comm] using h u
  · intro n u
    have h := integral_semidiscreteValue_supergradient_of_tilted_optimal
      (m := m) (S := ((ι → ℝ) × A))
      (V := Fin (m + 1) → ((ι → ℝ) × B))
      μ (Measure.pi (fun _ : Fin (m + 1) ↦ ν))
      (fun v j s ↦ cavitySpatialDifferenceCost k s (v j))
      (fun v j s ↦ gm s.2 ((v j).2))
      (fun j ↦ hcost.measurable.comp
        (measurable_snd.prodMk ((measurable_pi_apply j).comp measurable_fst)))
      hcij
      (fun j ↦ hgm.comp
        (measurable_snd.snd.prodMk
          (((measurable_pi_apply j).comp measurable_fst).snd)))
      hatom Cg (fun v s j ↦ hgmb s.2 ((v j).2)) Amin hAminm
      (t := -(t n)) (hminusopt n)
    simpa only [cavityMarkProbePressure, cavityMarkProbeAllocationCost,
      sub_neg_eq_add, mul_comm] using h u

/-- **Integrability of the expected mark-probe allocation cost.**  On the
target-cloud environment, a feasible allocation's mark-probe cost is integrable,
because it is bounded by `Cg`. -/
theorem integrable_semidiscreteAllocationCost_markProbe_comp {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (alloc : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) ×
      ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hAm : ∀ j, Measurable (fun z ↦ alloc z j))
    (halloc : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m),
      IsSemidiscreteAllocation μ z.2 (fun s ↦ alloc (z, s))) :
    Integrable (fun z ↦ semidiscreteAllocationCost μ
      (fun s j ↦ gm s.2 ((z.1 j).2)) (fun s ↦ alloc (z, s)))
      ((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)) := by
  have hstrong : StronglyMeasurable
      (fun z : (Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ) ↦
        semidiscreteAllocationCost μ (fun s j ↦ gm s.2 ((z.1 j).2))
          (fun s ↦ alloc (z, s))) := by
    have hjoint : StronglyMeasurable
        (fun q : (((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) ×
          ((ι → ℝ) × A)) ↦
          ∑ j, alloc (q.1, q.2) j * gm q.2.2 ((q.1.1 j).2)) := by
      refine Finset.stronglyMeasurable_fun_sum (s := Finset.univ) ?_
      intro j _
      exact ((hAm j).comp (measurable_fst.prodMk measurable_snd)).stronglyMeasurable.mul
        (hgm.comp (measurable_snd.snd.prodMk
          (((measurable_pi_apply j).comp measurable_fst.fst).snd))).stronglyMeasurable
    have := hjoint.integral_prod_right' (ν := μ)
    simpa only [semidiscreteAllocationCost] using this
  refine Integrable.of_bound hstrong.aestronglyMeasurable Cg ?_
  filter_upwards [halloc] with z hz
  rw [Real.norm_eq_abs]
  exact abs_semidiscreteAllocationCost_markProbe_le (μ := μ) (gm := gm) hgm Cg hgmb
    z.1 (fun s ↦ alloc (z, s)) hz

/-- **Change of variables for the expected probe cost.**  The product-law
expectation of the mark-probe allocation cost equals the environment-law
expectation of the allocation induced on the random target cloud and mass
vector. -/
theorem cavityMarkProbeAllocationCost_eq_environmentIntegral
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (p : Ω → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (henv : MeasurePreserving (fun ω ↦ (Y ω, p ω)) P
      ((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (alloc : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) ×
      ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hAm : ∀ j, Measurable (fun z ↦ alloc z j))
    (halloc : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m),
      IsSemidiscreteAllocation μ z.2 (fun s ↦ alloc (z, s))) :
    cavityMarkProbeAllocationCost μ gm ν alloc =
      ∫ ω, semidiscreteAllocationCost μ (cavityMarkProbeCost gm (Y ω))
        (fun s ↦ cavityEnvironmentAllocation alloc p Y ω s) ∂P := by
  let target : Measure ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) :=
    (Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)
  let Φ : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) → ℝ :=
    fun z ↦ semidiscreteAllocationCost μ (fun s j ↦ gm s.2 ((z.1 j).2))
      (fun s ↦ alloc (z, s))
  have hΦint : Integrable Φ target :=
    integrable_semidiscreteAllocationCost_markProbe_comp μ ν gm hgm Cg hgmb alloc hAm halloc
  have hchange : ∫ z, Φ z ∂target = ∫ ω, Φ ((Y ω, p ω)) ∂P := by
    have hmap : Measure.map (fun ω ↦ (Y ω, p ω)) P = target := henv.map_eq
    rw [← hmap]
    exact integral_map henv.measurable.aemeasurable
      (by simpa only [hmap] using hΦint.aestronglyMeasurable)
  have hmain : cavityMarkProbeAllocationCost μ gm ν alloc = ∫ z, Φ z ∂target := rfl
  rw [hmain, hchange]
  apply integral_congr_ae
  filter_upwards with ω
  rfl

/-- **Identification of `qpos - qneg`.**  The difference of the expected
mark-probe costs of two allocation families is exactly the environment-level
expectation of `cavityRandomProbeDifference` for the induced allocations. -/
theorem cavityMarkProbeAllocationCost_sub_eq_randomProbeDifference
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (ν : Measure ((ι → ℝ) × B)) [IsProbabilityMeasure ν]
    (p : Ω → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (henv : MeasurePreserving (fun ω ↦ (Y ω, p ω)) P
      ((Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (Aplus Amin : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) ×
      ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hAplusm : ∀ j, Measurable (fun z ↦ Aplus z j))
    (hAminm : ∀ j, Measurable (fun z ↦ Amin z j))
    (hplusalloc : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
      (dirichletOne m), IsSemidiscreteAllocation μ z.2 (fun s ↦ Aplus (z, s)))
    (hminusalloc : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod
      (dirichletOne m), IsSemidiscreteAllocation μ z.2 (fun s ↦ Amin (z, s))) :
    cavityMarkProbeAllocationCost μ gm ν Aplus -
        cavityMarkProbeAllocationCost μ gm ν Amin =
      ∫ ω, cavityRandomProbeDifference μ gm Y
        (fun v ↦ cavityEnvironmentAllocation Aplus p Y v.1 v.2)
        (fun v ↦ cavityEnvironmentAllocation Amin p Y v.1 v.2) ω ∂P := by
  let target : Measure ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) :=
    (Measure.pi (fun _ : Fin (m + 1) ↦ ν)).prod (dirichletOne m)
  let Φp : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) → ℝ :=
    fun z ↦ semidiscreteAllocationCost μ (fun s j ↦ gm s.2 ((z.1 j).2))
      (fun s ↦ Aplus (z, s))
  let Φm : ((Fin (m + 1) → ((ι → ℝ) × B)) × (Fin (m + 1) → ℝ)) → ℝ :=
    fun z ↦ semidiscreteAllocationCost μ (fun s j ↦ gm s.2 ((z.1 j).2))
      (fun s ↦ Amin (z, s))
  have hpint : Integrable Φp target :=
    integrable_semidiscreteAllocationCost_markProbe_comp μ ν gm hgm Cg hgmb Aplus
      hAplusm hplusalloc
  have hmint : Integrable Φm target :=
    integrable_semidiscreteAllocationCost_markProbe_comp μ ν gm hgm Cg hgmb Amin
      hAminm hminusalloc
  have hp_prod : cavityMarkProbeAllocationCost μ gm ν Aplus = ∫ z, Φp z ∂target := rfl
  have hm_prod : cavityMarkProbeAllocationCost μ gm ν Amin = ∫ z, Φm z ∂target := rfl
  have hchange : ∫ z, (Φp - Φm) z ∂target =
      ∫ ω, (Φp - Φm) ((Y ω, p ω)) ∂P := by
    have hmap : Measure.map (fun ω ↦ (Y ω, p ω)) P = target := henv.map_eq
    rw [← hmap]
    exact integral_map henv.measurable.aemeasurable
      (by simpa only [hmap] using (hpint.sub hmint).aestronglyMeasurable)
  calc
    cavityMarkProbeAllocationCost μ gm ν Aplus -
        cavityMarkProbeAllocationCost μ gm ν Amin
        = (∫ z, Φp z ∂target) - (∫ z, Φm z ∂target) := by rw [hp_prod, hm_prod]
    _ = ∫ z, (Φp - Φm) z ∂target := (integral_sub hpint hmint).symm
    _ = ∫ ω, (Φp - Φm) ((Y ω, p ω)) ∂P := hchange
    _ = ∫ ω, cavityRandomProbeDifference μ gm Y
          (fun v ↦ cavityEnvironmentAllocation Aplus p Y v.1 v.2)
          (fun v ↦ cavityEnvironmentAllocation Amin p Y v.1 v.2) ω ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      rfl

set_option maxHeartbeats 2400000 in
/-- **Supergradient readout: `qpos - qneg → 0`.**  Combining the explicit
mark-probe supergradient pair with the environment-level readout, the difference
of the expected mark-probe costs of the opposite-tilt optima tends to zero along
a weakly convergent rooted scene whose limit plans coincide.  The allocations
`Aplus`/`Amin` on the target-cloud environment induce the environment
allocations `aplus`/`aminus` through `cavityEnvironmentAllocation`; the
hypotheses `hlinkplus`/`hlinkminus` record this identification. -/
theorem tendsto_cavityMarkProbeAllocationCost_sub_of_weak_scene
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (hμsrc : ∀ n, μ n = (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ •
      ((volume.restrict (D n)).prod α))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ) (hp : ∀ n, Measurable (p n))
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (henv : ∀ n, MeasurePreserving (fun ω ↦ (Y n ω, p n ω)) (P n)
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (dirichletOne (m n))))
    (Aplus Amin : ∀ n, ((Fin (m n + 1) → ((ι → ℝ) × B)) ×
        (Fin (m n + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hAplusm : ∀ n j, Measurable (fun z ↦ Aplus n z j))
    (hAminm : ∀ n j, Measurable (fun z ↦ Amin n z j))
    (hplusalloc : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
      (dirichletOne (m n)),
      IsSemidiscreteAllocation (μ n) z.2 (fun s ↦ Aplus n (z, s)))
    (hminusalloc : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
      (dirichletOne (m n)),
      IsSemidiscreteAllocation (μ n) z.2 (fun s ↦ Amin n (z, s)))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hlinkplus : ∀ n (ω : Ωn n), (fun s ↦ aplus n (ω, s)) =
      fun s ↦ cavityEnvironmentAllocation (Aplus n) (p n) (Y n) ω s)
    (hlinkminus : ∀ n (ω : Ωn n), (fun s ↦ aminus n (ω, s)) =
      fun s ↦ cavityEnvironmentAllocation (Amin n) (p n) (Y n) ω s)
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e)
    (hintp : ∀ n, Integrable (fun ω ↦ cavityRandomProbeDifference (μ n) gm
      (Y n) (aplus n) (aminus n) ω) (P n))
    (hints : ∀ n, Integrable (fun ω ↦ cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω) (P n))
    (herror : Tendsto (fun n ↦ 2 * Cg * cavityRootWindowError η (D n)
      ((m n : ℝ) + 1)) atTop (𝓝 0))
    (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P n) (μ n)
      (p n) (hp n) (aplus n) (aminus n) (hplusm n) (hminusm n)
      (Y n) (hY n) ((m n : ℝ) + 1) (by positivity) (D n) (hD n)) atTop (𝓝 Q))
    (hplan : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1) :
    Tendsto (fun n ↦ cavityMarkProbeAllocationCost (μ n) gm (ν n) (Aplus n) -
      cavityMarkProbeAllocationCost (μ n) gm (ν n) (Amin n)) atTop (𝓝 0) := by
  -- Feasibility of the induced environment allocations.
  have hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)) := by
    intro n
    have hprod : ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
        (dirichletOne (m n)),
        IsSemidiscreteAllocation (μ n) z.2 (fun s ↦ Aplus n (z, s)) ∧
        IsSemidiscreteAllocation (μ n) z.2 (fun s ↦ Amin n (z, s)) :=
      (hplusalloc n).and (hminusalloc n)
    have hback := (henv n).quasiMeasurePreserving.ae hprod
    filter_upwards [hback] with ω hω
    refine ⟨?_, ?_⟩
    · rw [hlinkplus n ω]
      exact hω.1
    · rw [hlinkminus n ω]
      exact hω.2
  -- Identification of `qpos - qneg` with the environment probe difference.
  have hqid : ∀ n, cavityMarkProbeAllocationCost (μ n) gm (ν n) (Aplus n) -
      cavityMarkProbeAllocationCost (μ n) gm (ν n) (Amin n) =
      ∫ ω, cavityRandomProbeDifference (μ n) gm (Y n)
        (fun v ↦ cavityEnvironmentAllocation (Aplus n) (p n) (Y n) v.1 v.2)
        (fun v ↦ cavityEnvironmentAllocation (Amin n) (p n) (Y n) v.1 v.2) ω
        ∂P n := by
    intro n
    exact cavityMarkProbeAllocationCost_sub_eq_randomProbeDifference (P n) (μ n) (ν n)
      (p n) (Y n) (henv n) gm hgm Cg hgmb (Aplus n) (Amin n)
      (hAplusm n) (hAminm n) (hplusalloc n) (hminusalloc n)
  -- The induced allocations give the same environment probe difference.
  have hlink : ∀ n, (∫ ω, cavityRandomProbeDifference (μ n) gm (Y n)
        (fun v ↦ cavityEnvironmentAllocation (Aplus n) (p n) (Y n) v.1 v.2)
        (fun v ↦ cavityEnvironmentAllocation (Amin n) (p n) (Y n) v.1 v.2) ω
        ∂P n) =
      ∫ ω, cavityRandomProbeDifference (μ n) gm (Y n) (aplus n) (aminus n) ω
        ∂P n := by
    intro n
    apply integral_congr_ae
    filter_upwards with ω
    simp only [cavityRandomProbeDifference]
    rw [hlinkplus n ω, hlinkminus n ω]
  -- The environment-level readout.
  have hprobe : Tendsto (fun n ↦ ∫ ω, cavityRandomProbeDifference (μ n) gm
      (Y n) (aplus n) (aminus n) ω ∂P n) atTop (𝓝 0) :=
    tendsto_expectedProbeDifference_of_weak_scene (base := base) (m := m) P μ α D
      hD hμsrc p hp Y hY aplus aminus hplusm hminusm hfeas gm hgm Cg hgmb
      η hη Cη hηb hηint R hηsupp φ hφ hintp hints herror Q hweak hplan
  refine hprobe.congr' ?_
  filter_upwards with n
  exact ((hqid n).trans (hlink n)).symm

set_option maxHeartbeats 4000000 in
/-- **Atomless form of the supergradient readout.**  This is
`tendsto_cavityMarkProbeAllocationCost_sub_of_weak_scene` with the a.e. limit
plan equality derived internally from the atomlessness hypothesis via
`ae_cavityRootedCountableScene_limit_plans_eq_of_energy`.  The optimality,
energy and target-marginal inputs are those of the actual cavity assembly. -/
theorem tendsto_cavityMarkProbeAllocationCost_sub_of_weak_scene_of_atomless
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (ν : ℕ → Measure ((ι → ℝ) × B)) [∀ n, IsProbabilityMeasure (ν n)]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (hμsrc : ∀ n, μ n = (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ •
      ((volume.restrict (D n)).prod α))
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ) (hp : ∀ n, Measurable (p n))
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
    (hν : ∀ n, (ν n).map Prod.fst =
      (ENNReal.ofReal ((m n : ℝ) + 1))⁻¹ • volume.restrict (D n))
    (Aplus Amin : ∀ n, ((Fin (m n + 1) → ((ι → ℝ) × B)) ×
        (Fin (m n + 1) → ℝ)) × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hAplusm : ∀ n j, Measurable (fun z ↦ Aplus n z j))
    (hAminm : ∀ n j, Measurable (fun z ↦ Amin n z j))
    (hplusalloc : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
      (dirichletOne (m n)),
      IsSemidiscreteAllocation (μ n) z.2 (fun s ↦ Aplus n (z, s)))
    (hminusalloc : ∀ n, ∀ᵐ z ∂(Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod
      (dirichletOne (m n)),
      IsSemidiscreteAllocation (μ n) z.2 (fun s ↦ Amin n (z, s)))
    (hlinkplus : ∀ n (ω : Ωn n), (fun s ↦ aplus n (ω, s)) =
      fun s ↦ cavityEnvironmentAllocation (Aplus n) (p n) (Y n) ω s)
    (hlinkminus : ∀ n (ω : Ωn n), (fun s ↦ aminus n (ω, s)) =
      fun s ↦ cavityEnvironmentAllocation (Amin n) (p n) (Y n) ω s)
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
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e)
    (hintp : ∀ n, Integrable (fun ω ↦ cavityRandomProbeDifference (μ n) gm
      (Y n) (aplus n) (aminus n) ω) (P n))
    (hints : ∀ n, Integrable (fun ω ↦ cavityRandomSceneTestDifference (μ n) (D n)
      ((m n : ℝ) + 1) η gm (Y n) (aplus n) (aminus n) ω) (P n))
    (herror : Tendsto (fun n ↦ 2 * Cg * cavityRootWindowError η (D n)
      ((m n : ℝ) + 1)) atTop (𝓝 0))
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
    Tendsto (fun n ↦ cavityMarkProbeAllocationCost (μ n) gm (ν n) (Aplus n) -
      cavityMarkProbeAllocationCost (μ n) gm (ν n) (Amin n)) atTop (𝓝 0) := by
  have hplan := ae_cavityRootedCountableScene_limit_plans_eq_of_energy (base := base)
    (m := m) (P := P) (μ := μ) (ν := ν) p Y hY henv aplus aminus hplusm hminusm
    hfeas D hν hD k g a₀ t ht htzero G hopt hc hk C hC henergyplus henergyminus
    Q hweak hatom
  have henvswap : ∀ n, MeasurePreserving (fun ω ↦ (Y n ω, p n ω)) (P n)
      ((Measure.pi (fun _ : Fin (m n + 1) ↦ ν n)).prod (dirichletOne (m n))) := by
    intro n
    have h := Measure.measurePreserving_swap.comp (henv n)
    have hfun : (Prod.swap ∘ fun ω ↦ (p n ω, Y n ω)) = fun ω ↦ (Y n ω, p n ω) := rfl
    rwa [hfun] at h
  exact tendsto_cavityMarkProbeAllocationCost_sub_of_weak_scene (base := base)
    (m := m) P μ ν α D hD hμsrc p hp Y hY henvswap Aplus Amin hAplusm hAminm
    hplusalloc hminusalloc aplus aminus hplusm hminusm hlinkplus hlinkminus
    gm hgm Cg hgmb η hη Cη hηb hηint R hηsupp φ hφ hintp hints herror Q hweak
    hplan

end Pointwise

section MultivariateCube

open scoped Pointwise

/-- The cube `[0,L]^ι` has volume `L ^ card ι`. -/
theorem volume_cavitySpatialCube_pi (L : ℝ) (hL : 0 ≤ L) :
    volume (cavitySpatialCube (ι := ι) L) =
      ENNReal.ofReal (L ^ Fintype.card ι) := by
  rw [cavitySpatialCube, Real.volume_Icc_pi]
  have hterm : ∀ i : ι,
      ENNReal.ofReal ((fun _ ↦ L) i - (0 : ι → ℝ) i) = ENNReal.ofReal L := by
    intro i
    congr 1
    simp
  rw [Finset.prod_congr rfl (fun i _ ↦ hterm i), Finset.prod_const, Finset.card_univ,
    ← ENNReal.ofReal_pow hL]

/-- The inner cube `[R,L-R]^ι` has volume `(L - 2R) ^ card ι`. -/
theorem volume_cavitySpatialInner_pi {R L : ℝ} (h2R : 0 ≤ L - 2 * R) :
    volume (cavitySpatialInner (ι := ι) R L) =
      ENNReal.ofReal ((L - 2 * R) ^ Fintype.card ι) := by
  rw [cavitySpatialInner, Real.volume_Icc_pi]
  have hterm : ∀ i : ι,
      ENNReal.ofReal ((fun _ ↦ L - R) i - (fun _ ↦ R) i) = ENNReal.ofReal (L - 2 * R) := by
    intro i
    congr 1
    ring
  rw [Finset.prod_congr rfl (fun i _ ↦ hterm i), Finset.prod_const, Finset.card_univ,
    ← ENNReal.ofReal_pow h2R]

/-- The inner cube is contained in the cube when `2R ≤ L`. -/
theorem cavitySpatialInner_subset_cube_pi {R L : ℝ} (hR : 0 ≤ R) :
    cavitySpatialInner (ι := ι) R L ⊆ cavitySpatialCube (ι := ι) L := by
  intro x hx
  obtain ⟨h1, h2⟩ := Set.mem_Icc.mp hx
  refine Set.mem_Icc.mpr ⟨Pi.le_def.mpr fun i ↦ ?_, Pi.le_def.mpr fun i ↦ ?_⟩
  · simpa using le_trans hR (h1 i)
  · simpa using le_trans (h2 i) (by linarith : L - R ≤ L)

/-- **Multivariate boundary layer volume.**  The cube minus its inner cube has
volume `L^d - (L - 2R)^d`, where `d = card ι`. -/
theorem volume_cavitySpatialCube_sdiff_inner_pi {R L : ℝ}
    (hR : 0 ≤ R) (h2R : 2 * R ≤ L) :
    volume (cavitySpatialCube (ι := ι) L \ cavitySpatialInner (ι := ι) R L) =
      ENNReal.ofReal (L ^ Fintype.card ι - (L - 2 * R) ^ Fintype.card ι) := by
  have hL : 0 ≤ L := le_trans (by linarith : (0 : ℝ) ≤ 2 * R) h2R
  have h2R' : 0 ≤ L - 2 * R := by linarith
  have hsub := cavitySpatialInner_subset_cube_pi (ι := ι) (R := R) (L := L) hR
  have hinner_meas : MeasurableSet (cavitySpatialInner (ι := ι) R L) := measurableSet_Icc
  have hfin : volume (cavitySpatialInner (ι := ι) R L) ≠ ⊤ := by
    rw [volume_cavitySpatialInner_pi h2R']
    exact ENNReal.ofReal_ne_top
  rw [measure_sdiff hsub hinner_meas.nullMeasurableSet hfin,
    volume_cavitySpatialCube_pi (ι := ι) L hL, volume_cavitySpatialInner_pi h2R',
    ← ENNReal.ofReal_sub _ (pow_nonneg h2R' _)]

/-- Reflection identifies `{x} - D` with the preimage of `D` under `u ↦ x - u`. -/
theorem cavitySpatialCube_reflect_preimage_pi (L : ℝ) (x : ι → ℝ) :
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
theorem integral_cavitySpatialCube_window_eq_pi (η : (ι → ℝ) → ℝ) (L : ℝ) (x : ι → ℝ) :
    ∫ z in cavitySpatialCube (ι := ι) L, η (x - z) =
      ∫ u in ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L, η u := by
  have hDmeas : MeasurableSet (cavitySpatialCube (ι := ι) L) := measurableSet_Icc
  have hreflect : ({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L =
      (fun u ↦ x - u) ⁻¹' cavitySpatialCube (ι := ι) L :=
    cavitySpatialCube_reflect_preimage_pi L x
  have hreflect_meas : MeasurableSet
      (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L) := by
    rw [hreflect]
    exact hDmeas.preimage (measurable_const.sub measurable_id)
  rw [← integral_indicator hDmeas, ← integral_indicator hreflect_meas]
  have h := integral_sub_left_eq_self
    (f := fun u ↦ (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L).indicator η u)
    (μ := volume) x
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
theorem integral_cavitySpatialCube_window_eq_one_pi (η : (ι → ℝ) → ℝ) (L R : ℝ)
    (x : ι → ℝ) (hηint : ∫ u, η u = 1)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (hx : x ∈ cavitySpatialInner (ι := ι) R L) :
    ∫ z in cavitySpatialCube (ι := ι) L, η (x - z) = 1 := by
  rw [integral_cavitySpatialCube_window_eq_pi]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hηint
  · intro u hu
    apply hηsupp u
    intro huR
    apply hu
    have hu_norm : ‖u‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using huR
    have hu_abs (i : ι) : |u i| ≤ R := by
      rw [← Real.norm_eq_abs]
      exact (norm_le_pi_norm (f := u) i).trans hu_norm
    obtain ⟨hx1, hx2⟩ := Set.mem_Icc.mp hx
    have hmem : x - u ∈ cavitySpatialCube (ι := ι) L := by
      refine Set.mem_Icc.mpr ⟨Pi.le_def.mpr fun i ↦ ?_, Pi.le_def.mpr fun i ↦ ?_⟩
      · simp only [Pi.sub_apply, Pi.zero_apply]
        linarith [(abs_le.mp (hu_abs i)).2, hx1 i]
      · simp only [Pi.sub_apply]
        linarith [(abs_le.mp (hu_abs i)).1, hx2 i]
    exact ⟨x, rfl, x - u, hmem, by simp only [Pi.sub_apply]; rw [sub_sub_cancel]⟩

/-- Pointwise defect bound: the windowed integral differs from one by at most
the total absolute mass of the window. -/
theorem abs_integral_cavitySpatialCube_window_sub_one_le_pi (η : (ι → ℝ) → ℝ)
    (L : ℝ) (x : ι → ℝ) (hη : Integrable η) (hηint : ∫ u, η u = 1) :
    |(∫ z in cavitySpatialCube (ι := ι) L, η (x - z)) - 1| ≤ ∫ u, |η u| := by
  rw [integral_cavitySpatialCube_window_eq_pi, ← hηint]
  have hDmeas : MeasurableSet (cavitySpatialCube (ι := ι) L) := measurableSet_Icc
  have hreflect_meas : MeasurableSet
      (({x} : Set (ι → ℝ)) - cavitySpatialCube (ι := ι) L) := by
    rw [cavitySpatialCube_reflect_preimage_pi]
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

/-- **Multivariate boundary-layer estimate.**  The root-window defect on the
cube `[0,L]^ι` is at most the relative boundary-layer volume
`(L^d - (L-2R)^d) / L^d` times the total absolute mass of the window. -/
theorem cavityRootWindowError_cavitySpatialCube_le_pi (η : (ι → ℝ) → ℝ) (L R : ℝ)
    (hR : 0 ≤ R) (hL : 0 < L) (h2R : 2 * R ≤ L)
    (hη : Integrable η) (hηm : Measurable η)
    (hηint : ∫ u, η u = 1)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0) :
    cavityRootWindowError η (cavitySpatialCube (ι := ι) L) (L ^ Fintype.card ι)
      ≤ ((L ^ Fintype.card ι - (L - 2 * R) ^ Fintype.card ι) /
          L ^ Fintype.card ι) * ∫ u, |η u| := by
  let d := Fintype.card ι
  let N : ℝ := L ^ d
  have hNpos : 0 < N := pow_pos hL d
  let A : ℝ := ∫ u, |η u|
  have hA : 0 ≤ A := integral_nonneg fun u ↦ abs_nonneg (η u)
  have h2R' : 0 ≤ L - 2 * R := by linarith
  let defect : (ι → ℝ) → ℝ :=
    fun x ↦ |(∫ z in cavitySpatialCube (ι := ι) L, η (x - z)) - 1|
  have hdefect_bound : ∀ x, defect x ≤ A := fun x ↦
    abs_integral_cavitySpatialCube_window_sub_one_le_pi η L x hη hηint
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
    rw [Measure.restrict_apply_univ, volume_cavitySpatialCube_pi (ι := ι) L hL.le]
    exact ENNReal.ofReal_lt_top
  have hdefect_int : IntegrableOn defect (cavitySpatialCube (ι := ι) L) volume :=
    Integrable.of_bound hdefect_meas.aestronglyMeasurable A
      (Eventually.of_forall fun x ↦ by
        have hx : 0 ≤ defect x := abs_nonneg _
        rw [Real.norm_eq_abs, abs_of_nonneg hx]
        exact hdefect_bound x)
  have hinner_sub := cavitySpatialInner_subset_cube_pi (ι := ι) (R := R) (L := L) hR
  have hinner_meas : MeasurableSet (cavitySpatialInner (ι := ι) R L) := measurableSet_Icc
  have hdiff_meas : MeasurableSet (cavitySpatialCube (ι := ι) L \
      cavitySpatialInner (ι := ι) R L) := measurableSet_Icc.diff hinner_meas
  haveI hfindiff : IsFiniteMeasure
      (volume.restrict (cavitySpatialCube (ι := ι) L \
        cavitySpatialInner (ι := ι) R L)) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact lt_of_le_of_lt (measure_mono Set.sdiff_subset) (by
      rw [volume_cavitySpatialCube_pi (ι := ι) L hL.le]
      exact ENNReal.ofReal_lt_top)
  have hzero_inner : ∀ x ∈ cavitySpatialInner (ι := ι) R L, defect x = 0 := by
    intro x hx
    dsimp only [defect]
    rw [integral_cavitySpatialCube_window_eq_one_pi η L R x hηint hηsupp hx,
      sub_self, abs_zero]
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
      A * (volume (cavitySpatialCube (ι := ι) L \
        cavitySpatialInner (ι := ι) R L)).toReal := by
    rw [integral_const]
    simp only [Measure.restrict_apply_univ, measureReal_def, smul_eq_mul]
    ring
  have hvol : (volume (cavitySpatialCube (ι := ι) L \
      cavitySpatialInner (ι := ι) R L)).toReal = L ^ d - (L - 2 * R) ^ d := by
    rw [volume_cavitySpatialCube_sdiff_inner_pi (ι := ι) hR h2R,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (pow_le_pow_left₀ h2R' (by linarith : L - 2 * R ≤ L) d))]
  have hmain : ∫ x in cavitySpatialCube (ι := ι) L, defect x ≤ A * (L ^ d - (L - 2 * R) ^ d) := by
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
      _ = A * (L ^ d - (L - 2 * R) ^ d) := by rw [hvol]
  show N⁻¹ * ∫ x in cavitySpatialCube (ι := ι) L, defect x ≤
      ((L ^ d - (L - 2 * R) ^ d) / L ^ d) * A
  calc
    N⁻¹ * ∫ x in cavitySpatialCube (ι := ι) L, defect x
        ≤ N⁻¹ * (A * (L ^ d - (L - 2 * R) ^ d)) :=
      mul_le_mul_of_nonneg_left hmain (inv_nonneg.mpr hNpos.le)
    _ = ((L ^ d - (L - 2 * R) ^ d) / L ^ d) * A := by
      field_simp [hNpos.ne']
      ring

/-- **Vanishing of the multivariate boundary-layer defect.**  Along cube side
lengths `L n → ∞`, the root-window defect of a fixed compactly supported profile
on `[0,L n]^ι` tends to zero. -/
theorem tendsto_cavityRootWindowError_cavitySpatialCube_pi (η : (ι → ℝ) → ℝ) (R : ℝ)
    (hR : 0 ≤ R) (hη : Integrable η) (hηm : Measurable η)
    (hηint : ∫ u, η u = 1)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (L : ℕ → ℝ) (hL : ∀ n, 0 < L n) (h2R : ∀ n, 2 * R ≤ L n)
    (hLtop : Tendsto L atTop atTop) :
    Tendsto (fun n ↦ cavityRootWindowError η (cavitySpatialCube (ι := ι) (L n))
      ((L n) ^ Fintype.card ι)) atTop (𝓝 0) := by
  let d := Fintype.card ι
  let A : ℝ := ∫ u, |η u|
  have hnonneg : ∀ n, 0 ≤ cavityRootWindowError η (cavitySpatialCube (ι := ι) (L n))
      ((L n) ^ d) := by
    intro n
    exact mul_nonneg (inv_nonneg.mpr (pow_nonneg (hL n).le d))
      (integral_nonneg fun x ↦ abs_nonneg _)
  have hbdd : ∀ n, cavityRootWindowError η (cavitySpatialCube (ι := ι) (L n))
      ((L n) ^ d) ≤ ((L n ^ d - (L n - 2 * R) ^ d) / L n ^ d) * A := fun n ↦
    cavityRootWindowError_cavitySpatialCube_le_pi η (L n) R hR (hL n) (h2R n)
      hη hηm hηint hηsupp
  have hratio : Tendsto (fun n ↦ (L n ^ d - (L n - 2 * R) ^ d) / L n ^ d)
      atTop (𝓝 0) := by
    have hc : Tendsto (fun n ↦ 2 * R / L n) atTop (𝓝 0) :=
      Filter.Tendsto.const_div_atTop hLtop (2 * R)
    have h1 : Tendsto (fun n ↦ 1 - 2 * R / L n) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hc
    have h2 : Tendsto (fun n ↦ (1 - 2 * R / L n) ^ d) atTop (𝓝 1) := by
      simpa using h1.pow d
    have h3 : Tendsto (fun n ↦ 1 - (1 - 2 * R / L n) ^ d) atTop (𝓝 0) := by
      have hconst : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
      simpa only [Pi.sub_apply, sub_self] using hconst.sub h2
    refine h3.congr' (Eventually.of_forall fun n ↦ ?_)
    have hL0 : L n ≠ 0 := (hL n).ne'
    have hdiv : (L n - 2 * R) / L n = 1 - 2 * R / L n := by
      rw [sub_div, div_self hL0]
    calc
      1 - (1 - 2 * R / L n) ^ d
          = 1 - ((L n - 2 * R) / L n) ^ d := by rw [hdiv]
      _ = L n ^ d / L n ^ d - (L n - 2 * R) ^ d / L n ^ d := by
        rw [div_self (pow_ne_zero d hL0), ← div_pow]
      _ = (L n ^ d - (L n - 2 * R) ^ d) / L n ^ d :=
        (sub_div _ _ _).symm
  have hupper : Tendsto (fun n ↦ ((L n ^ d - (L n - 2 * R) ^ d) / L n ^ d) * A)
      atTop (𝓝 0) := by
    simpa using hratio.mul_const A
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hnonneg hbdd

end MultivariateCube

end OTSelector.Probability
