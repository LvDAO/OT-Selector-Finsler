import OTSelector.Probability.CavitySemidiscreteActualCycleLimit
import OTSelector.Probability.CavitySemidiscreteCountablePlanLimit
import OTSelector.Transport.CyclicMonotonicity.AmbientCountableTargetRigidity
import OTSelector.Probability.CavitySemidiscreteEnergyMarginalLimit
import OTSelector.Probability.CavitySemidiscreteExpectedMarginalError
import OTSelector.Probability.CavityModelTiltSupergradients

/-!
# Rooted-scene probe readout for the opposite-tilt cavity optima

The paper's last stochastic input to differentiability is the equality
`qpos n - qneg n → 0` of the two expected probe costs of the opposite-tilt
cavity optima.  The paper proves it by rooting both plans at an independent
uniform spatial root, taking a weak subsequence of the rooted scenes, and using
two-cycle rigidity to identify the two limiting plans.

This module formalizes the model-level readout.  The main outputs are:

* `integral_cavityMarkWindowTest_cavitySpatialRootedPlan`: for a probe depending
  only on the two marks, the compact-window test integral of the rooted plan is
  exactly the scaled probe cost with the translated spatial window;
* `integral_root_average_markWindow_eq`: averaging this identity over the uniform
  root turns the translated window into the averaged window `N^{-1} ∫_D η (x-z)`;
* `abs_rootAverage_markWindowTest_sub_probe_le`: the root-averaged window test
  differs from the probe cost by at most the paper's source boundary-layer
  defect `cavityRootWindowError`;
* `ae_cavityRootedCountableScene_limit_plans_eq`: along a weakly convergent
  actual rooted scene, the two limiting plans coincide almost surely, combining
  the energy source-marginal identity, the common target cloud, actual
  two-cycle monotonicity and countable-target rigidity;
* `tendsto_probeDifference_of_scene_squeeze` and
  `tendsto_probeDifference_of_subseq`: the final readout transfer: an asymptotic
  comparison of the probe difference with a vanishing scene-test difference, and
  the subsequence criterion matching the weak-scene extraction.

Remaining gap.  The file proves (a) the exact readout identity and its
root-averaged boundary-layer error, and (c) the countable-target rigidity
conclusion for a weakly convergent rooted scene from the a.e. energy, cycle and
support inputs.  What is not yet formalized is:

* the assembly of the a.e. inputs of `ae_cavityRootedCountableScene_limit_plans_eq`
  from `ae_actualRootedScene_equal_source_marginals_of_energy`,
  `ae_actualRootedScene_average_support_twoCycle`,
  `ae_actualRootedCountableScene_plans_supported` and the extracted weak scene
  (mechanical projection of the countable scene law onto the pair law);
* the paper's target-cutoff tail estimate showing that the root-averaged
  *untruncated* mark-window test may be replaced by compactly supported plan
  tests with error `O(1/R)` (the long-edge window bound
  `lintegral_original_rootedPlan_longEdgeWindow_le_of_energy` supplies the
  finite-level input), which is what makes `hscene` in
  `tendsto_probeDifference_of_scene_squeeze` provable;
* the geometric estimate `cavityRootWindowError η (D n) (N n) → 0` for a cube
  `D n` of volume `N n` and a fixed compactly supported `η` with integral one.

-/


open MeasureTheory Set Filter Topology TopologicalSpace
open scoped BigOperators ENNReal CompactlySupported

noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]

/-- A probe read only through the source mark and the target mark. -/
def cavityMarkProbeCost {m : ℕ} (gm : A → B → ℝ)
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) :
    ((ι → ℝ) × A) → Fin (m + 1) → ℝ :=
  fun s j ↦ gm s.2 (Y j).2

/-- The mark probe aggregated by an allocation coefficient vector. -/
def cavityMarkProbeAggregate {m : ℕ} (gm : A → B → ℝ)
    (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ) (s : (ι → ℝ) × A) : ℝ :=
  ∑ j, a s j * gm s.2 (Y j).2

/-- The mark probe times a compact source window, as a test on the rooted plan. -/
def cavityMarkWindowTest (η : (ι → ℝ) → ℝ) (gm : A → B → ℝ) :
    (((ι → ℝ) × A) × ((ι → ℝ) × B)) → ℝ :=
  fun e ↦ η e.1.1 * gm e.1.2 e.2.2

omit [Fintype ι] [MeasurableSpace B] in
/-- The probe is exactly the allocation cost of the mark probe. -/
theorem semidiscreteAllocationCost_cavityMarkProbeCost {m : ℕ}
    (μ : Measure ((ι → ℝ) × A))
    (gm : A → B → ℝ) (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ) :
    semidiscreteAllocationCost μ (cavityMarkProbeCost (m := m) gm Y) a =
      ∫ s, cavityMarkProbeAggregate gm Y a s ∂μ := rfl

omit [Fintype ι] in
/-- The mark probe at a fixed target label is measurable. -/
theorem measurable_cavityMarkProbeCost {m : ℕ}
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Y : Fin (m + 1) → ((ι → ℝ) × B)) (j : Fin (m + 1)) :
    Measurable (fun s : (ι → ℝ) × A ↦ gm s.2 (Y j).2) := by
  have hpair : Measurable (fun s : (ι → ℝ) × A ↦ (s.2, (Y j).2)) :=
    measurable_snd.prodMk measurable_const
  have hEq : (Function.uncurry gm) ∘ (fun s : (ι → ℝ) × A ↦ (s.2, (Y j).2))
      = fun s ↦ gm s.2 (Y j).2 := rfl
  have hcomp := hgm.comp hpair
  rw [hEq] at hcomp
  exact hcomp

omit [Fintype ι] in
/-- The windowed mark probe on the rooted source-target product is measurable. -/
theorem measurable_cavityMarkWindowTest
    (η : (ι → ℝ) → ℝ) (hη : Measurable η)
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm)) :
    Measurable (cavityMarkWindowTest (A := A) (B := B) η gm) := by
  unfold cavityMarkWindowTest
  refine (hη.comp measurable_fst.fst).mul ?_
  have hpair : Measurable (fun e : (((ι → ℝ) × A) × ((ι → ℝ) × B)) ↦ (e.1.2, e.2.2)) :=
    measurable_fst.snd.prodMk measurable_snd.snd
  have hEq : (Function.uncurry gm) ∘
      (fun e : (((ι → ℝ) × A) × ((ι → ℝ) × B)) ↦ (e.1.2, e.2.2))
      = fun e ↦ gm e.1.2 e.2.2 := rfl
  have hcomp := hgm.comp hpair
  rw [hEq] at hcomp
  exact hcomp

omit [Fintype ι] in
theorem measurable_cavityMarkProbeAggregate {m : ℕ}
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun s ↦ a s j)) :
    Measurable (cavityMarkProbeAggregate gm Y a) := by
  apply Finset.measurable_sum
  intro j _
  exact (ham j).mul (measurable_cavityMarkProbeCost gm hgm Y j)

omit [Fintype ι] in
/-- **Exact rooted readout identity.**  The windowed mark test against the rooted
plan is exactly the scaled probe cost with the window translated by the root.
Only the marks are seen by `gm`, so the target translation is invisible. -/
theorem integral_cavityMarkWindowTest_cavitySpatialRootedPlan {m : ℕ}
    (μ : Measure ((ι → ℝ) × A)) [IsFiniteMeasure μ]
    (gm : A → B → ℝ) (hgm : Measurable (Function.uncurry gm))
    (Cg : ℝ) (hgmb : ∀ a b, |gm a b| ≤ Cg)
    (Y : Fin (m + 1) → ((ι → ℝ) × B))
    (a : ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (N : ℝ) (hN : 0 ≤ N) (z : ι → ℝ) :
    ∫ e, cavityMarkWindowTest η gm e ∂(cavitySpatialRootedPlan μ a Y N z) =
      N * semidiscreteAllocationCost μ
        (fun s j ↦ η (s.1 - z) * gm s.2 (Y j).2) a := by
  let F : (((ι → ℝ) × A) × Fin (m + 1)) →
      (((ι → ℝ) × A) × ((ι → ℝ) × B)) :=
    Prod.map (cavitySpatialTranslate z) (fun j ↦ cavitySpatialTranslate z (Y j))
  have hF : Measurable F :=
    (measurable_cavitySpatialTranslate.comp
      (measurable_const.prodMk measurable_id)).prodMap (measurable_of_finite _)
  have htest : Measurable (cavityMarkWindowTest (A := A) (B := B) η gm) :=
    measurable_cavityMarkWindowTest η hη gm hgm
  have hbound (e : (((ι → ℝ) × A) × ((ι → ℝ) × B))) :
      ‖cavityMarkWindowTest η gm e‖ ≤ Cη * Cg := by
    rw [Real.norm_eq_abs, cavityMarkWindowTest, abs_mul]
    exact mul_le_mul (hηb e.1.1) (hgmb e.1.2 e.2.2) (abs_nonneg _)
      (le_trans (abs_nonneg _) (hηb e.1.1))
  have hrootfin : IsFiniteMeasure (cavitySpatialRootedPlan μ a Y N z) :=
    ha.isFiniteMeasure_cavitySpatialRootedPlan Y N z
  have hint : Integrable (cavityMarkWindowTest η gm) (cavitySpatialRootedPlan μ a Y N z) :=
    Integrable.of_bound htest.aestronglyMeasurable (Cη * Cg)
      (Eventually.of_forall hbound)
  have hallfin : IsFiniteMeasure (semidiscreteAllocationMeasure μ a) :=
    ha.isFiniteMeasure_allocationMeasure
  have hcomp : Integrable (fun e ↦ cavityMarkWindowTest η gm (F e))
      (semidiscreteAllocationMeasure μ a) :=
    Integrable.of_bound (htest.comp hF).aestronglyMeasurable (Cη * Cg)
      (Eventually.of_forall fun e ↦ hbound (F e))
  have hmeas_c : Measurable (Function.uncurry
      (fun (s : (ι → ℝ) × A) (j : Fin (m + 1)) ↦ η (s.1 - z) * gm s.2 (Y j).2)) := by
    refine (hη.comp ?_).mul ?_
    · exact (measurable_fst.fst.sub measurable_const)
    · have hpair : Measurable
          (fun e : ((ι → ℝ) × A) × Fin (m + 1) ↦ (e.1.2, (Y e.2).2)) :=
        measurable_fst.snd.prodMk ((measurable_of_finite Y).comp measurable_snd).snd
      have hEq : (Function.uncurry gm) ∘
          (fun e : ((ι → ℝ) × A) × Fin (m + 1) ↦ (e.1.2, (Y e.2).2))
          = fun e ↦ gm e.1.2 (Y e.2).2 := rfl
      have hcomp := hgm.comp hpair
      rw [hEq] at hcomp
      exact hcomp
  have hint_c (j : Fin (m + 1)) :
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
  have hstep : ∫ e, cavityMarkWindowTest η gm e ∂(cavitySpatialRootedPlan μ a Y N z) =
      N * ∫ e, cavityMarkWindowTest η gm (F e) ∂semidiscreteAllocationMeasure μ a := by
    rw [cavitySpatialRootedPlan, integral_smul_measure,
      integral_map hF.aemeasurable htest.aestronglyMeasurable, ENNReal.toReal_ofReal hN,
      smul_eq_mul]
  have hstep2 : ∫ e, cavityMarkWindowTest η gm (F e)
      ∂semidiscreteAllocationMeasure μ a =
      semidiscreteAllocationCost μ (fun s j ↦ η (s.1 - z) * gm s.2 (Y j).2) a := by
    have hcongr : (fun e ↦ cavityMarkWindowTest η gm (F e)) =
        Function.uncurry
          (fun (s : (ι → ℝ) × A) (j : Fin (m + 1)) ↦ η (s.1 - z) * gm s.2 (Y j).2) := by
      funext e
      obtain ⟨s, j⟩ := e
      rfl
    rw [hcongr]
    exact ha.integral_allocationMeasure _ hmeas_c hint_c
  rw [hstep, hstep2]

/-- The paper's source boundary-layer defect for a rooted window: after averaging
the window over the uniform root, the mass seen by the source density `1 / N`
is not exactly one.  For a cube `D` of volume `N` and a fixed compactly
supported `η` with integral one this is `O(N^{-1/q})`. -/
def cavityRootWindowError (η : (ι → ℝ) → ℝ) (D : Set (ι → ℝ)) (N : ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∫ x in D, |(∫ z in D, η (x - z)) - 1|

/-- Root averaging of the windowed mark test, before subtracting the probe cost.
The uniform root turns the translated window into the averaged window
`N^{-1} ∫_D η (x - z) dz`. -/
theorem integral_root_average_markWindow_eq
    (α : Measure A) [IsProbabilityMeasure α]
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N)
    (hD : volume D = ENNReal.ofReal N)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη)
    (h : (ι → ℝ) × A → ℝ) (hh : Measurable h) (Ch : ℝ)
    (hhb : ∀ᵐ s ∂((volume.restrict D).prod α), |h s| ≤ Ch) :
    (∫ z, (∫ s, η (s.1 - z) * h s ∂((volume.restrict D).prod α))
        ∂cavityRootMeasure volume D N)
      = ∫ s, h s * ((N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z))
          ∂((volume.restrict D).prod α) := by
  haveI hvol : IsFiniteMeasure (volume.restrict D) := by
    constructor
    rw [Measure.restrict_apply_univ, hD]
    exact ENNReal.ofReal_lt_top
  haveI hlamfin : IsFiniteMeasure ((volume.restrict D).prod α) := inferInstance
  have hmeas : Measurable
      (Function.uncurry (fun z : ι → ℝ => fun s : (ι → ℝ) × A => η (s.1 - z) * h s)) := by
    have h1 : Measurable (fun p : (ι → ℝ) × ((ι → ℝ) × A) => η (p.2.1 - p.1)) :=
      hη.comp ((measurable_snd.fst).sub measurable_fst)
    have h2 : Measurable (fun p : (ι → ℝ) × ((ι → ℝ) × A) => h p.2) :=
      hh.comp measurable_snd
    exact h1.mul h2
  have hbdd : ∀ᵐ p ∂((volume.restrict D).prod ((volume.restrict D).prod α)),
      ‖Function.uncurry (fun z : ι → ℝ => fun s : (ι → ℝ) × A => η (s.1 - z) * h s) p‖
        ≤ Cη * Ch := by
    refine (Measure.ae_prod_iff_ae_ae (p := fun p : ((ι → ℝ) × ((ι → ℝ) × A)) =>
      ‖Function.uncurry (fun z : ι → ℝ => fun s : (ι → ℝ) × A =>
        η (s.1 - z) * h s) p‖ ≤ Cη * Ch) ?_).mpr ?_
    · exact measurableSet_le hmeas.norm measurable_const
    · filter_upwards with z
      filter_upwards [hhb] with s hs
      change |η (s.1 - z) * h s| ≤ Cη * Ch
      rw [abs_mul]
      exact mul_le_mul (hηb (s.1 - z)) hs (abs_nonneg _)
        (le_trans (abs_nonneg _) (hηb (s.1 - z)))
  have hf : Integrable
      (Function.uncurry (fun z : ι → ℝ => fun s : (ι → ℝ) × A => η (s.1 - z) * h s))
      ((volume.restrict D).prod ((volume.restrict D).prod α)) :=
    Integrable.of_bound hmeas.aestronglyMeasurable (Cη * Ch) hbdd
  rw [cavityRootMeasure, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hN.le, smul_eq_mul, integral_integral_swap hf,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with s
  rw [integral_mul_const]
  ring

/-- **Root-averaged probe readout error.**  If the source law is the normalized
volume on a spatial domain `D` of volume `N`, then the root-averaged windowed
mark test differs from the actual probe cost by at most the boundary-layer
defect `cavityRootWindowError`.  This is the paper's estimate
`|q_n^± - E ∫ η g d(τ Γ_n^±)| ≤ C G / L_n`, with the geometric estimate isolated
in the defect. -/
theorem abs_rootAverage_markWindowTest_sub_probe_le {m : ℕ}
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
    {p : Fin (m + 1) → ℝ} (ha : IsSemidiscreteAllocation μ p a)
    (η : (ι → ℝ) → ℝ) (hη : Measurable η) (Cη : ℝ) (hηb : ∀ x, |η x| ≤ Cη) :
    |(∫ z, (∫ e, cavityMarkWindowTest η gm e ∂(cavitySpatialRootedPlan μ a Y N z))
        ∂cavityRootMeasure volume D N)
      - semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) a|
    ≤ Cg * cavityRootWindowError η D N := by
  let h : (ι → ℝ) × A → ℝ := cavityMarkProbeAggregate gm Y a
  have hh : Measurable h := measurable_cavityMarkProbeAggregate gm hgm Y a ham
  have hcne : (ENNReal.ofReal N)⁻¹ ≠ 0 := by
    rw [ENNReal.inv_ne_zero]
    exact ENNReal.ofReal_ne_top
  have hnonneg : ∀ᵐ s ∂((volume.restrict D).prod α), ∀ j, 0 ≤ a s j := by
    rw [← Measure.ae_ennreal_smul_measure_iff (c := (ENNReal.ofReal N)⁻¹) hcne, ← hμ]
    exact ha.nonneg
  have hsum : ∀ᵐ s ∂((volume.restrict D).prod α), ∑ j, a s j = 1 := by
    rw [← Measure.ae_ennreal_smul_measure_iff (c := (ENNReal.ofReal N)⁻¹) hcne, ← hμ]
    exact ha.sum_one
  have hb : ∀ᵐ s ∂((volume.restrict D).prod α), |h s| ≤ Cg := by
    filter_upwards [hnonneg, hsum] with s hn hs
    calc
      |h s| = |∑ j, a s j * gm s.2 (Y j).2| := rfl
      _ ≤ ∑ j, |a s j * gm s.2 (Y j).2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, a s j * Cg := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_of_nonneg (hn j)]
        exact mul_le_mul_of_nonneg_left (hgmb _ _) (hn j)
      _ = Cg := by rw [← Finset.sum_mul, hs, one_mul]
  haveI hvol : IsFiniteMeasure (volume.restrict D) := by
    constructor
    rw [Measure.restrict_apply_univ, hD]
    exact ENNReal.ofReal_lt_top
  have hfinlam : IsFiniteMeasure ((volume.restrict D).prod α) := inferInstance
  have hroot : ∀ z, ∫ e, cavityMarkWindowTest η gm e ∂(cavitySpatialRootedPlan μ a Y N z)
      = ∫ s, η (s.1 - z) * h s ∂((volume.restrict D).prod α) := by
    intro z
    have hcost : semidiscreteAllocationCost ((ENNReal.ofReal N)⁻¹ •
        ((volume.restrict D).prod α))
        (fun s j ↦ η (s.1 - z) * gm s.2 (Y j).2) a
        = (N : ℝ)⁻¹ * ∫ s, η (s.1 - z) * h s ∂((volume.restrict D).prod α) := by
      unfold semidiscreteAllocationCost
      rw [integral_smul_measure, ENNReal.toReal_inv, ENNReal.toReal_ofReal hN.le,
        smul_eq_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with s
      simp only [h, cavityMarkProbeAggregate]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [integral_cavityMarkWindowTest_cavitySpatialRootedPlan μ gm hgm Cg hgmb Y a ha
      η hη Cη hηb N hN.le z, hμ, hcost, ← mul_assoc,
      mul_inv_cancel₀ hN.ne', one_mul]
  have hq : semidiscreteAllocationCost μ (cavityMarkProbeCost gm Y) a
      = (N : ℝ)⁻¹ * ∫ s, h s ∂((volume.restrict D).prod α) := by
    rw [semidiscreteAllocationCost_cavityMarkProbeCost (m := m), hμ, integral_smul_measure,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hN.le, smul_eq_mul]
  have hswap := integral_root_average_markWindow_eq α D N hN hD η hη Cη hηb h hh Cg hb
  have hWmeas : Measurable (fun s : (ι → ℝ) × A ↦ ∫ z in D, η (s.1 - z)) := by
    have hjoint : Measurable (fun p : ((ι → ℝ) × A) × (ι → ℝ) ↦ η (p.1.1 - p.2)) :=
      hη.comp ((measurable_fst.fst).sub measurable_snd)
    exact (hjoint.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict D)).measurable
  have hWb : ∀ s : (ι → ℝ) × A, |∫ z in D, η (s.1 - z)| ≤ Cη * N := by
    intro s
    have hint : Integrable (fun z : ι → ℝ ↦ η (s.1 - z)) (volume.restrict D) :=
      Integrable.of_bound (hη.comp (measurable_const.sub measurable_id)).aestronglyMeasurable Cη
        (Eventually.of_forall fun z ↦ hηb (s.1 - z))
    calc
      |∫ z in D, η (s.1 - z)| ≤ ∫ z in D, |η (s.1 - z)| := abs_integral_le_integral_abs
      _ ≤ ∫ _z in D, Cη :=
        integral_mono_ae hint.abs (integrable_const Cη)
          (Eventually.of_forall fun z ↦ hηb (s.1 - z))
      _ = Cη * N := by
        rw [integral_const]
        change ((volume.restrict D) univ).toReal * Cη = Cη * N
        rw [Measure.restrict_apply_univ, hD, ENNReal.toReal_ofReal hN.le]
        ring
  have hinv : (0 : ℝ) ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr hN.le
  have hint1 : Integrable (fun s : (ι → ℝ) × A ↦
      h s * ((N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z))) ((volume.restrict D).prod α) := by
    apply Integrable.of_bound ((hh.mul (measurable_const.mul hWmeas)).aestronglyMeasurable)
      (Cg * Cη)
    filter_upwards [hb] with s hs
    change ‖h s * ((N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z))‖ ≤ Cg * Cη
    rw [Real.norm_eq_abs, abs_mul]
    have h2 : |(N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z)| ≤ Cη := by
      rw [abs_mul, abs_of_nonneg hinv]
      calc
        (N : ℝ)⁻¹ * |∫ z in D, η (s.1 - z)| ≤ (N : ℝ)⁻¹ * (Cη * N) :=
          mul_le_mul_of_nonneg_left (hWb s) hinv
        _ = Cη := by
          rw [mul_comm Cη N, ← mul_assoc, inv_mul_cancel₀ hN.ne', one_mul]
    exact mul_le_mul_of_nonneg' hs h2 (abs_nonneg _) (le_trans (abs_nonneg _) hs)
  have hint2 : Integrable (fun s : (ι → ℝ) × A ↦ h s * (N : ℝ)⁻¹)
      ((volume.restrict D).prod α) := by
    apply Integrable.of_bound ((hh.mul measurable_const).aestronglyMeasurable) (Cg * (N : ℝ)⁻¹)
    filter_upwards [hb] with s hs
    change ‖h s * (N : ℝ)⁻¹‖ ≤ Cg * (N : ℝ)⁻¹
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hinv]
    exact mul_le_mul_of_nonneg_right hs hinv
  have hsecond : (N : ℝ)⁻¹ * ∫ s, h s ∂((volume.restrict D).prod α) =
      ∫ s, h s * (N : ℝ)⁻¹ ∂((volume.restrict D).prod α) := by
    rw [mul_comm, ← integral_mul_const]
  have hdefect_int : Integrable (fun s : (ι → ℝ) × A ↦
      (N : ℝ)⁻¹ * |(∫ z in D, η (s.1 - z)) - 1|) ((volume.restrict D).prod α) := by
    apply Integrable.of_bound
      ((measurable_const.mul (continuous_abs.measurable.comp
        (hWmeas.sub measurable_const))).aestronglyMeasurable)
      ((N : ℝ)⁻¹ * (Cη * N + 1))
    filter_upwards with s
    change ‖(N : ℝ)⁻¹ * |(∫ z in D, η (s.1 - z)) - 1|‖ ≤ (N : ℝ)⁻¹ * (Cη * N + 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hinv, abs_of_nonneg (abs_nonneg _)]
    apply mul_le_mul_of_nonneg_left _ hinv
    calc
      |(∫ z in D, η (s.1 - z)) - 1| ≤ |∫ z in D, η (s.1 - z)| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ Cη * N + 1 := by rw [abs_one]; linarith [hWb s]
  have hpoint : ∀ᵐ s ∂((volume.restrict D).prod α),
      |h s * ((N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z)) - h s * (N : ℝ)⁻¹|
        ≤ Cg * ((N : ℝ)⁻¹ * |(∫ z in D, η (s.1 - z)) - 1|) := by
    filter_upwards [hb] with s hs
    have hEq : h s * ((N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z)) - h s * (N : ℝ)⁻¹
        = h s * (N : ℝ)⁻¹ * ((∫ z in D, η (s.1 - z)) - 1) := by ring
    rw [hEq, abs_mul, abs_mul, abs_of_nonneg hinv, mul_assoc]
    exact mul_le_mul_of_nonneg_right hs (mul_nonneg hinv (abs_nonneg _))
  simp_rw [hroot]
  rw [hswap, hq, hsecond, ← integral_sub hint1 hint2]
  calc
    |∫ s, (h s * ((N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z)) - h s * (N : ℝ)⁻¹)
        ∂((volume.restrict D).prod α)|
        ≤ ∫ s, |h s * ((N : ℝ)⁻¹ * ∫ z in D, η (s.1 - z)) - h s * (N : ℝ)⁻¹|
            ∂((volume.restrict D).prod α) := abs_integral_le_integral_abs
    _ ≤ ∫ s, Cg * ((N : ℝ)⁻¹ * |(∫ z in D, η (s.1 - z)) - 1|)
          ∂((volume.restrict D).prod α) :=
      integral_mono_ae (hint1.sub hint2).abs (hdefect_int.const_mul Cg) hpoint
    _ = Cg * ∫ s, (N : ℝ)⁻¹ * |(∫ z in D, η (s.1 - z)) - 1|
          ∂((volume.restrict D).prod α) := by
      rw [integral_const_mul]
    _ = Cg * cavityRootWindowError η D N := by
      congr 1
      rw [cavityRootWindowError, integral_prod _ hdefect_int]
      simp only [measure_univ, ENNReal.toReal_one, one_smul, integral_const_mul]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      congr 1
      simp

section LimitRigidity

open PointProcess PointProcess.LocalConfiguration

variable [TopologicalSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [MetricSpace B] [ProperSpace B] [BorelSpace B]
  [SecondCountableTopology B]
  (base : (ι → ℝ) × B)

local instance limitRigidityBorelTarget : StandardBorelSpace ((ι → ℝ) × B) := inferInstance
local instance limitRigidityConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance limitRigidityConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance limitRigidityConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
local instance limitRigidityPlanPolish :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace
local instance limitRigidityCloudPolish : PolishSpace (LocalFiniteMeasure ((ι → ℝ) × B)) :=
  LocalFiniteMeasure.instPolishSpace

/-- **Steps (b)-(c) of the readout: the two limiting plans coincide.**  For a weak
limit of the countable rooted scene, the energy identity gives equal source
marginals, the actual optimizers give two-cycle monotonicity of the average
support, and both plans and the target cloud are supported on the same countable
cloud.  Countable-target rigidity then identifies the two plans. -/
theorem ae_cavityRootedCountableScene_limit_plans_eq
    (k : A → B → (ι → ℝ) → ℝ)
    (hk : ∀ b, Measurable (fun p : A × (ι → ℝ) ↦ k p.1 b p.2))
    (Q : ProbabilityMeasure (CavityCountableTargetScene (A := A) base))
    (hsource : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      ((s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst =
        (s.1.2.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst))
    (hcycle : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      OTSelector.Reconstruction.IsTwoCycleMonotone (cavitySpatialDifferenceCost k)
        ((LocalFiniteMeasure.cavityAverage (s.1.1, s.1.2.1) : Measure _)).support)
    (hsupp₀ : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.1)
    (hsupp₁ : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      SupportedOverConfiguration Prod.snd s.2 s.1.2.1)
    (hatom : ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      ∀ y₁ y₂ : (ι → ℝ) × B, y₁ ≠ y₂ →
        multiplicity s.2 y₁ ≠ 0 → multiplicity s.2 y₂ ≠ 0 →
        NullSingletonClass
          (((s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst).map
            (fun x ↦ cavitySpatialDifferenceCost k x y₁ -
              cavitySpatialDifferenceCost k x y₂))) :
    ∀ᵐ s ∂(Q : Measure (CavityCountableTargetScene (A := A) base)),
      (s.1.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) = s.1.2.1 := by
  filter_upwards [hsource, hcycle, hsupp₀, hsupp₁, hatom] with s hsrc hcyc hsp₀ hsp₁ hat
  let J := {y : (ι → ℝ) × B // multiplicity s.2 y ≠ 0}
  haveI hJcount : Countable J := (countable_multiplicity_support s.2).to_subtype
  haveI hJsing : MeasurableSingletonClass J := inferInstance
  let yemb : J → (ι → ℝ) × B := Subtype.val
  have hyemb : MeasurableEmbedding yemb :=
    MeasurableEmbedding.subtype_coe (isClosed_multiplicity_support s.2).measurableSet
  let π₀ : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)) := s.1.1
  let π₁ : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)) := s.1.2.1
  let avg : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)) :=
    (LocalFiniteMeasure.cavityAverage (s.1.1, s.1.2.1) :
      LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B)))
  have hsrc' : π₀.map Prod.fst = π₁.map Prod.fst := hsrc
  have hsuppavg : ∀ᵐ z ∂(2 : ℝ≥0∞)⁻¹ • (π₀ + π₁), z ∈ avg.support := by
    filter_upwards [(Measure.support_mem_ae (μ := (2 : ℝ≥0∞)⁻¹ • (π₀ + π₁)))] with z hz
    simpa only [avg, π₀, π₁, LocalFiniteMeasure.coe_cavityAverage] using hz
  rw [Measure.ae_ennreal_smul_measure_iff (by norm_num), ae_add_measure_iff] at hsuppavg
  have hcar₀ : ∀ᵐ z ∂π₀, z.2 ∈ Set.range yemb := by
    filter_upwards [(SupportedOverConfiguration.countable_carrier
      continuous_snd hsp₀).2] with z hz
    exact ⟨⟨z.2, hz⟩, rfl⟩
  have hcar₁ : ∀ᵐ z ∂π₁, z.2 ∈ Set.range yemb := by
    filter_upwards [(SupportedOverConfiguration.countable_carrier
      continuous_snd hsp₁).2] with z hz
    exact ⟨⟨z.2, hz⟩, rfl⟩
  have hcyc' : OTSelector.Reconstruction.IsTwoCycleMonotone
      (cavitySpatialDifferenceCost k) avg.support := hcyc
  have hmain : π₀ = π₁ := by
    refine ambient_plan_eq_of_countable_target_twoCycle
      (S := (ι → ℝ) × A) (Y := (ι → ℝ) × B) (J := J)
      π₀.fst π₀ π₁ yemb hyemb rfl hsrc'.symm hcar₀ hcar₁
      (cavitySpatialDifferenceCost k) _ Measure.isClosed_support.measurableSet hcyc'
      hsuppavg.1 hsuppavg.2 ?_ ?_
    · intro j
      have hb : Measurable (fun s : (ι → ℝ) × A ↦ k s.2 j.1.2 (j.1.1 - s.1)) :=
        (hk j.1.2).comp (measurable_snd.prodMk
          ((measurable_const : Measurable (fun _ : (ι → ℝ) × A ↦ j.1.1)).sub
            measurable_fst))
      simpa only [yemb, cavitySpatialDifferenceCost] using hb
    · intro i j hij
      have h := hat i.1 j.1 (fun h ↦ hij (Subtype.ext h)) i.2 j.2
      simpa only [yemb] using h
  simpa only [π₀, π₁] using hmain

end LimitRigidity

/-- **Final readout squeeze.**  If the opposite-tilt probe difference is
asymptotic to a scene-test difference which itself tends to zero, then the probe
difference tends to zero.  In the application `sceneDiff` is the difference of
the two root-averaged window test expectations; `abs_rootAverage_markWindowTest_sub_probe_le`
supplies `hclose` with `ε n = 2 Cg * cavityRootWindowError η (D n) (N n)`, and the
limiting plan equality supplies `hscene` after the paper's target-cutoff tail
estimate. -/
theorem tendsto_probeDifference_of_scene_squeeze
    (u sceneDiff ε : ℕ → ℝ)
    (hε : Tendsto ε atTop (𝓝 0))
    (hscene : Tendsto sceneDiff atTop (𝓝 0))
    (hclose : ∀ᶠ n in atTop, |u n - sceneDiff n| ≤ ε n) :
    Tendsto u atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop, ‖u n‖ ≤ |sceneDiff n| + ε n := by
    filter_upwards [hclose] with n hn
    calc
      ‖u n‖ = |(u n - sceneDiff n) + sceneDiff n| := by
        rw [sub_add_cancel, Real.norm_eq_abs]
      _ ≤ |u n - sceneDiff n| + |sceneDiff n| := abs_add_le _ _
      _ ≤ ε n + |sceneDiff n| := by linarith [hn]
      _ = |sceneDiff n| + ε n := add_comm _ _
  have hlim : Tendsto (fun n ↦ |sceneDiff n| + ε n) atTop (𝓝 0) := by
    simpa using hscene.abs.add hε
  rw [tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun n ↦ norm_nonneg _) hbound hlim

/-- **Subsequence form of the readout.**  If every subsequence of the
opposite-tilt probe differences has a further subsequence along which it tends to
zero, then the full sequence tends to zero.  This matches the actual extraction:
from every subsequence of environments one chooses a weakly convergent rooted
scene, and along it the two limiting plans coincide. -/
theorem tendsto_probeDifference_of_subseq
    (u : ℕ → ℝ)
    (h : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop →
      ∃ ms : ℕ → ℕ, Tendsto (fun n ↦ u (ns (ms n))) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 0) :=
  tendsto_of_subseq_tendsto h

end OTSelector.Probability
