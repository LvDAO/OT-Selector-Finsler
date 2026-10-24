import OTSelector.Probability.CavityProbeReadoutAssembly

/-!
# Weak-topology passage for the rooted-scene readout

This module closes the analytic gap left in `CavityProbeReadoutAssembly`: the
scene test integral is shown to vanish along the weakly convergent countable
rooted scenes.

The main steps are:

* `cavitySceneTestFunctional`: the continuous test functional
  `s ↦ ∫ φ d s.1.1 - ∫ φ d s.1.2.1` on the countable target scene, continuous
  for a compactly supported continuous test `φ` by
  `LocalFiniteMeasure.continuous_testIntegral`;
* `abs_cavitySceneTestFunctional_scene_le`: at every actual scene the functional
  is bounded by `2 Cg Cη |B_R|`, uniformly in the scale and the root, using
  `abs_integral_cavityMarkWindowTest_le`;
* `ae_abs_cavitySceneTestFunctional_sceneLaw_le`: the same bound almost surely
  under the countable rooted scene law, by pushing forward along the scene map;
* `tendsto_integral_of_weak_of_uniform_bound`: the abstract bounded-continuous
  Portmanteau passage.  The closed-set inequality
  `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` transfers the uniform
  bound to the weak limit; the continuous functional is replaced by its bounded
  clamp; `ProbabilityMeasure.tendsto_iff_forall_integral_tendsto` then gives
  convergence of the integrals to the limit integral, which vanishes by the a.e.
  plan equality;
* `tendsto_integral_cavitySceneTestFunctional_of_weak`: the instantiation to the
  actual countable scenes, giving
  `∫ s, cavitySceneTestFunctional φ s ∂Q_n → 0` from weak convergence and the
  a.e. plan equality of the limit scene.

## Remaining gap

The final assembly `tendsto_expectedProbeDifference_of_sceneTest` in
`CavityProbeReadoutAssembly` consumes `hscene` in the *root-averaged* form
`∫ ω, cavityRandomSceneTestDifference … ω ∂P n`.  The bridge
`∫ s, cavitySceneTestFunctional φ s ∂Q_n = ∫ ω, cavityRandomSceneTestDifference … ω ∂P n`
is not formalized here.  It is a Fubini/change-of-variables computation:
`Q_n` is the pushforward of `P n × ρ n` along the scene map; the scene's plan
components are the `finitePlanLocalVersion` of the rooted plans, equal to the
rooted plans when the allocation is feasible; `integral_map`,
`integral_congr_ae`, `integral_sub` and `integral_prod` then reduce the scene
integral to the iterated root integral.  All the required measurability
(`measurable_joint_cavitySpatialRootedPlan`, `measurable_finitePlanLocalVersion`)
and the a.e. finiteness (`IsSemidiscreteAllocation.isFiniteMeasure_cavitySpatialRootedPlan`)
are available; the missing work is the bookkeeping of these rewrites, not a new
mathematical input.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

section Portmanteau

variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [CompactSpace B] [BorelSpace B] [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

open PointProcess PointProcess.LocalConfiguration

local instance portmanteauBorelTarget : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance portmanteauConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance portmanteauConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance portmanteauConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance portmanteauPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance portmanteauCloudPolish :
    PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The scene test functional: the difference of the compact-test integrals of
the two plans in the scene. -/
def cavitySceneTestFunctional
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ)) :
    CavityCountableTargetScene (A := A) base → ℝ :=
  fun s ↦ LocalFiniteMeasure.testIntegral s.1.1 φ -
    LocalFiniteMeasure.testIntegral s.1.2.1 φ

/-- The scene test functional is continuous for the vague topology. -/
theorem continuous_cavitySceneTestFunctional
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ)) :
    Continuous (cavitySceneTestFunctional base φ) :=
  ((LocalFiniteMeasure.continuous_testIntegral φ).comp continuous_fst.fst).sub
    ((LocalFiniteMeasure.continuous_testIntegral φ).comp continuous_fst.snd.fst)

/-- **Uniform bound of the scene test functional along the actual scenes.**
For a source law that is the normalized uniform window on `D` times a fixed mark
law, the scene test functional of a mark probe is bounded by
`2 Cg Cη |B_R|` at every actual scene, uniformly in the scale and the root. -/
theorem abs_cavitySceneTestFunctional_scene_le {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N)
    (hD : volume D = ENNReal.ofReal N)
    (hμ : μ = (ENNReal.ofReal N)⁻¹ • ((volume.restrict D).prod α))
    (p : Ω → Fin (m + 1) → ℝ)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)) ∧
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s)))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e) :
    ∀ᵐ ω ∂P, ∀ z : ι → ℝ,
      |cavitySceneTestFunctional base φ
        (cavityRootedCountableScene base μ p aplus aminus Y N (ω, z))|
        ≤ 2 * (Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal) := by
  filter_upwards [hfeas] with ω hω z
  have hK : ∀ e : (((ι → ℝ) × A) × ((ι → ℝ) × B)), φ e = cavityMarkWindowTest η gm e := hφ
  have hbound (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
      (ham : ∀ j, Measurable (fun s ↦ a s j))
      (ha : IsSemidiscreteAllocation μ (p ω) a) :
      |∫ e, φ e ∂(cavitySpatialRootedPlan μ a (Y ω) N z)| ≤
        Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal := by
    rw [show (fun e ↦ φ e) = (fun e ↦ cavityMarkWindowTest η gm e) from funext hK]
    exact abs_integral_cavityMarkWindowTest_le (μ := μ) α D N hN hD hμ gm hgm Cg hgmb
      (Y ω) a ham (p ω) ha η hη Cη hηb hηint R hηsupp z
  have hAp := hbound (fun s ↦ aplus (ω, s))
    (fun j ↦ (hplusm j).comp (measurable_const.prodMk measurable_id))
    hω.1
  have hAm := hbound (fun s ↦ aminus (ω, s))
    (fun j ↦ (hminusm j).comp (measurable_const.prodMk measurable_id))
    hω.2
  have hfinp := hω.1.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  have hfinm := hω.2.isFiniteMeasure_cavitySpatialRootedPlan (Y ω) N z
  simp only [cavitySceneTestFunctional, cavityRootedCountableScene, cavityRootedLocalScene,
    LocalFiniteMeasure.testIntegral, coe_finitePlanLocalVersion,
    ite_eq_left (measure_lt_top
      (cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z) univ),
    ite_eq_left (measure_lt_top
      (cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z) univ)]
  calc
    |(∫ (e : ((ι → ℝ) × A) × ((ι → ℝ) × B)),
          φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)) -
        ∫ (e : ((ι → ℝ) × A) × ((ι → ℝ) × B)),
          φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)|
        ≤ |∫ (e : ((ι → ℝ) × A) × ((ι → ℝ) × B)),
            φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aplus (ω, s)) (Y ω) N z)|
          + |∫ (e : ((ι → ℝ) × A) × ((ι → ℝ) × B)),
            φ e ∂(cavitySpatialRootedPlan μ (fun s ↦ aminus (ω, s)) (Y ω) N z)| :=
      abs_sub _ _
    _ ≤ Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal
          + Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal :=
      add_le_add hAp hAm
    _ = 2 * (Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal) := by ring

/-- The uniform bound of the scene test functional holds almost surely under the
countable rooted scene law. -/
theorem ae_abs_cavitySceneTestFunctional_sceneLaw_le {Ω : Type*} [MeasurableSpace Ω]
    {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (α : Measure A) [IsProbabilityMeasure α]
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N)
    (hD : volume D = ENNReal.ofReal N)
    (hμ : μ = (ENNReal.ofReal N)⁻¹ • ((volume.restrict D).prod α))
    (p : Ω → Fin (m + 1) → ℝ) (hp : Measurable p)
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (hfeas : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aplus (ω, s)) ∧
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ aminus (ω, s)))
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (hηint : Integrable η) (R : ℝ)
    (hηsupp : ∀ u, u ∉ Metric.closedBall (0 : ι → ℝ) R → η u = 0)
    (φ : C_c((((ι → ℝ) × A) × ((ι → ℝ) × B)), ℝ))
    (hφ : ∀ e, φ e = cavityMarkWindowTest η gm e) :
    ∀ᵐ s ∂(cavityCountableSceneLawRootMeasure base P μ p hp aplus aminus
      hplusm hminusm Y hY N hN D hD : Measure (CavityCountableTargetScene (A := A) base)),
      |cavitySceneTestFunctional base φ s|
        ≤ 2 * (Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal) := by
  let ρ : Measure (ι → ℝ) := cavityRootMeasure volume D N
  haveI hρ : IsProbabilityMeasure ρ := isProbabilityMeasure_cavityRootMeasure volume D N hN hD
  have hpoint := abs_cavitySceneTestFunctional_scene_le (base := base) (P := P) (μ := μ)
    α D N hN hD hμ p Y aplus aminus hplusm hminusm hfeas gm hgm Cg hgmb
    η hη Cη hηb hηint R hηsupp φ hφ
  have hae : ∀ᵐ v ∂(P.prod ρ),
      |cavitySceneTestFunctional base φ
        (cavityRootedCountableScene base μ p aplus aminus Y N v)|
        ≤ 2 * (Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal) := by
    have h := (measurePreserving_fst (μ := P) (ν := ρ)).quasiMeasurePreserving.ae hpoint
    filter_upwards [h] with v hv
    simpa only [Prod.mk.eta] using hv v.2
  have hmeas := measurable_cavityRootedCountableScene base μ p hp aplus aminus
    hplusm hminusm Y hY N
  have hset : MeasurableSet {s : CavityCountableTargetScene (A := A) base |
      |cavitySceneTestFunctional base φ s| ≤
        2 * (Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal)} :=
    (isClosed_le (continuous_cavitySceneTestFunctional base φ).abs
      continuous_const).measurableSet
  rw [cavityCountableSceneLawRootMeasure]
  change ∀ᵐ s ∂(Measure.map (cavityRootedCountableScene base μ p aplus aminus Y N)
      (P.prod ρ) : Measure (CavityCountableTargetScene (A := A) base)), _
  exact (ae_map_iff hmeas.aemeasurable hset).mpr hae

/-- **Bounded-continuous Portmanteau passage.**  If a continuous functional is
uniformly bounded along a weakly convergent sequence of probability measures and
vanishes almost surely under the limit, then its integrals tend to zero.  The
bound is transferred to the limit through the closed-set Portmanteau inequality,
and the functional is replaced by its bounded continuous clamp. -/
theorem tendsto_integral_of_weak_of_uniform_bound {S : Type*} [MeasurableSpace S]
    [TopologicalSpace S] [OpensMeasurableSpace S] [HasOuterApproxClosed S]
    (Qn : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto Qn atTop (𝓝 Q))
    (F : S → ℝ) (hFcont : Continuous F) (K : ℝ)
    (hbound : ∀ n, ∀ᵐ s ∂(Qn n : Measure S), |F s| ≤ K)
    (hzero : ∀ᵐ s ∂(Q : Measure S), F s = 0) :
    Tendsto (fun n ↦ ∫ s, F s ∂(Qn n : Measure S)) atTop (𝓝 0) := by
  have hclosed : IsClosed {s : S | |F s| ≤ K} :=
    isClosed_le hFcont.abs continuous_const
  have hsetmeas : MeasurableSet {s : S | |F s| ≤ K} := hclosed.measurableSet
  have hQbound : ∀ᵐ s ∂(Q : Measure S), |F s| ≤ K := by
    have hle := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hweak hclosed
    have hone : ∀ n, (Qn n : Measure S) {s : S | |F s| ≤ K} = 1 := by
      intro n
      have hcompl : (Qn n : Measure S) {s : S | |F s| ≤ K}ᶜ = 0 := by
        simpa only [Set.compl_setOf] using (ae_iff.mp (hbound n))
      have hsum := measure_add_measure_compl (μ := (Qn n : Measure S)) hsetmeas
      rw [hcompl, add_zero, measure_univ] at hsum
      exact hsum
    have hlim : Filter.limsup (fun n ↦ (Qn n : Measure S) {s : S | |F s| ≤ K})
        atTop = 1 := by
      rw [funext hone, Filter.limsup_const]
    have hge : (1 : ℝ≥0∞) ≤ (Q : Measure S) {s : S | |F s| ≤ K} := by
      have := hle
      rwa [hlim] at this
    have hle1 : (Q : Measure S) {s : S | |F s| ≤ K} ≤ 1 :=
      (measure_mono (subset_univ _)).trans (le_of_eq measure_univ)
    have hQ1 : (Q : Measure S) {s : S | |F s| ≤ K} = 1 := le_antisymm hle1 hge
    have hfin : (Q : Measure S) {s : S | |F s| ≤ K} ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top hle1
    rw [ae_iff]
    have hc : (Q : Measure S) {s : S | |F s| ≤ K}ᶜ = 0 := by
      rw [measure_compl hsetmeas hfin, hQ1]
      simp
    simpa only [Set.compl_setOf] using hc
  let M : ℝ := |K|
  let gfun : S → ℝ := fun s ↦ max (-M) (min M (F s))
  have hgcont : Continuous gfun :=
    continuous_const.max (continuous_const.min hFcont)
  have hgM : ∀ s, |gfun s| ≤ M := by
    intro s
    rw [abs_le]
    exact ⟨le_max_left _ _, max_le (by linarith [abs_nonneg K]) (min_le_left _ _)⟩
  have hgdist : ∀ x y, dist (gfun x) (gfun y) ≤ 2 * M := by
    intro x y
    rw [Real.dist_eq]
    calc
      |gfun x - gfun y| ≤ |gfun x| + |gfun y| := abs_sub _ _
      _ ≤ M + M := add_le_add (hgM x) (hgM y)
      _ = 2 * M := by ring
  let g : BoundedContinuousFunction S ℝ :=
    BoundedContinuousFunction.mkOfBound ⟨gfun, hgcont⟩ (2 * M) hgdist
  have hclamp : ∀ s, |F s| ≤ K → g s = F s := by
    intro s hs
    change gfun s = F s
    by_cases hK : 0 ≤ K
    · have hM : M = K := abs_of_nonneg hK
      have hle := (abs_le.mp hs).2
      have hge := (abs_le.mp hs).1
      simp only [gfun, hM]
      rw [min_eq_right hle, max_eq_right hge]
    · exfalso
      have h0 : (0 : ℝ) ≤ |F s| := abs_nonneg _
      linarith
  have hleft : ∀ n, ∫ s, g s ∂(Qn n : Measure S) =
      ∫ s, F s ∂(Qn n : Measure S) := fun n ↦
    integral_congr_ae ((hbound n).mono fun s hs ↦ hclamp s hs)
  have hright : ∫ s, g s ∂(Q : Measure S) = 0 := by
    rw [integral_congr_ae (hQbound.mono fun s hs ↦ hclamp s hs)]
    exact integral_eq_zero_of_ae hzero
  have hconv := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) g
  rw [hright] at hconv
  exact hconv.congr' (Eventually.of_forall fun n ↦ hleft n)

/-- **The scene test integral vanishes along the actual weakly convergent
scenes.**  This is the `hscene` input of
`tendsto_expectedProbeDifference_of_sceneTest`, in scene-functional form: the
uniform bound and the a.e. plan equality feed the bounded-continuous
Portmanteau passage. -/
theorem tendsto_integral_cavitySceneTestFunctional_of_weak
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)] {m : ℕ → ℕ}
    (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
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
    (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hweak : Tendsto (fun n ↦ cavityCountableSceneLawRootMeasure base (P n) (μ n)
      (p n) (hp n) (aplus n) (aminus n) (hplusm n) (hminusm n)
      (Y n) (hY n) ((m n : ℝ) + 1) (by positivity) (D n) (hD n)) atTop (𝓝 Q))
    (hplan : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1) :
    Tendsto (fun n ↦ ∫ s, cavitySceneTestFunctional base φ s
      ∂(cavityCountableSceneLawRootMeasure base (P n) (μ n) (p n) (hp n)
        (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
        ((m n : ℝ) + 1) (by positivity) (D n) (hD n) :
        Measure (CavityCountableTargetScene (A := A) base))) atTop (𝓝 0) := by
  have hzero : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      cavitySceneTestFunctional base φ s = 0 :=
    hplan.mono fun s hs ↦ by
      have hs' : s.1.1 = s.1.2.1 := Subtype.ext hs
      simp only [cavitySceneTestFunctional, hs', sub_self]
  exact tendsto_integral_of_weak_of_uniform_bound
    (fun n ↦ cavityCountableSceneLawRootMeasure base (P n) (μ n) (p n) (hp n)
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
      ((m n : ℝ) + 1) (by positivity) (D n) (hD n))
    Q hweak (cavitySceneTestFunctional base φ)
    (continuous_cavitySceneTestFunctional base φ)
    (2 * (Cg * Cη * (volume (Metric.closedBall (0 : ι → ℝ) R)).toReal))
    (fun n ↦ ae_abs_cavitySceneTestFunctional_sceneLaw_le (base := base)
      (P := P n) (μ := μ n) α (D n) ((m n : ℝ) + 1) (by positivity) (hD n)
      (hμsrc n) (p n) (hp n) (Y n) (hY n) (aplus n) (aminus n)
      (hplusm n) (hminusm n) (hfeas n) gm hgm Cg hgmb η hη Cη hηb hηint R
      hηsupp φ hφ)
    hzero

end Portmanteau

end OTSelector.Probability
