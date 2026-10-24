import OTSelector.Reconstruction.MarkedStationaryValueLegalInputJointStationarity
import OTSelector.MeasureTheory.CompactProductMarginalTests

/-!
# Matching-input domination on the same actual joint weak scene

Compact product tests compare actual retained endpoints with their own full
original colored inputs. The simultaneous inequalities form one closed joint
carrier, so every actual weak limit keeps all these inequalities on one common
almost-everywhere event, including nonproper endpoint projections.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance markedStationaryValueLegalInputJointDominationLocalInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointDominationLocalPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- Immutable color selection is a compact continuous function on the original
finite tag, independent of the physical clock values. -/
def legalInputColorTest (c : Fin 2) : C_c(Fin 2, ℝ) where
  toFun d := if d = c then 1 else 0
  continuous_toFun := continuous_of_discreteTopology
  hasCompactSupport' := HasCompactSupport.of_support_subset_isCompact isCompact_univ (subset_univ _)

/-- Both original endpoint tests dominate the actual retained compact product
readouts of the same legal optimum, with its same original Haar root. -/
def legalMarkedInputTestDomination (q : ℕ) (s : LegalMarkedOptimalInputScene q) : Prop :=
  ∀ (f : C_c(LegalMarkedPhysicalPoint q, ℝ)), (∀ x, 0 ≤ f x) →
    ∀ (g : C_c(LegalMarkedPhysicalPoint q, ℝ)), (∀ x, g x ∈ Icc 0 1) →
      LocalFiniteMeasure.testIntegral s.1.1 (cavityProductTest f g) ≤
        LocalFiniteMeasure.testIntegral s.2 (cavityProductTest f (legalInputColorTest 0)) ∧
      LocalFiniteMeasure.testIntegral s.1.1 (cavityProductTest g f) ≤
        LocalFiniteMeasure.testIntegral s.2 (cavityProductTest f (legalInputColorTest 1))

/-- All compact source and target comparisons are one closed simultaneous
carrier; no uncountable intersection of separate AE statements is used. -/
theorem isClosed_legalMarkedInputTestDomination (q : ℕ) :
    IsClosed {s : LegalMarkedOptimalInputScene q | legalMarkedInputTestDomination q s} := by
  change IsClosed {s : LegalMarkedOptimalInputScene q |
    ∀ (f : C_c(LegalMarkedPhysicalPoint q, ℝ)), ∀ (_ : ∀ x, 0 ≤ f x),
    ∀ (g : C_c(LegalMarkedPhysicalPoint q, ℝ)), ∀ (_ : ∀ x, g x ∈ Icc 0 1), _ ∧ _}
  simp only [ofPred_forall]
  exact isClosed_iInter fun f ↦ isClosed_iInter fun hf ↦ isClosed_iInter fun g ↦
    isClosed_iInter fun hg ↦
      (isClosed_le ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst.fst)
        ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd)).inter
      (isClosed_le ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_fst.fst)
        ((LocalFiniteMeasure.continuous_testIntegral _).comp continuous_snd))

/-- The literal original finite observation belongs to the simultaneous carrier
by its actual matching and actual unused endpoints, without a selected law. -/
theorem legalMarkedInputTestDomination_observation
    (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) :
    legalMarkedInputTestDomination q (legalMarkedOptimalInputObservation q hL kin g t p) := by
  intro f hf χ hχ
  let Γ := legalMarkedNormalizedOptimalPlan q L kin g t p.1
  have : IsFiniteMeasure Γ := isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t p.1
  let μ := physicalSceneRootedPlan Γ (legalMarkedCenteredCoordinate q L) Prod.snd (L ^ q) p.2
  have : IsFiniteMeasure μ := isFiniteMeasure_physicalSceneRootedPlan Γ _ _ _ _
  have hs : Integrable (fun e : LegalMarkedPhysicalEdge q ↦ f e.1) μ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_fst).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (.of_forall (fun e ↦ f.toBoundedContinuousFunction.norm_coe_le_norm _))
  have ht : Integrable (fun e : LegalMarkedPhysicalEdge q ↦ f e.2) μ :=
    Integrable.of_bound (f.continuous.measurable.comp measurable_snd).aestronglyMeasurable
      ‖f.toBoundedContinuousFunction‖ (.of_forall (fun e ↦ f.toBoundedContinuousFunction.norm_coe_le_norm _))
  have hsprod : (∫ e, cavityProductTest f χ e ∂μ) ≤ ∫ e, f e.1 ∂μ :=
    integral_mono (cavityProductTest f χ).integrable hs (fun e ↦
      mul_le_of_le_one_right (hf _) (hχ _).2)
  have htprod : (∫ e, cavityProductTest χ f e ∂μ) ≤ ∫ e, f e.2 ∂μ :=
    integral_mono (cavityProductTest χ f).integrable ht (fun e ↦
      mul_le_of_le_one_left (hf _) (hχ _).2)
  have hsrow : legalMarkedRootedSourceTest q L kin g t f p.1 p.2 ≤
      legalMarkedRootedSourceInputTest q L f p.1 p.2 := by
    have he := legalMarkedRootedSourceTest_sub_input_eq_missing q L kin g t f p.1 p.2
    have hn : (0 : ℝ) ≤ ∫ x, f (legalMarkedCenteredCoordinate q L x - p.2, x.2)
        ∂legalMarkedMissingSourceMeasure q L (L ^ q) kin g t p.1 :=
      integral_nonneg (fun x ↦ hf _)
    linarith
  have htrow : legalMarkedRootedTargetTest q L kin g t f p.1 p.2 ≤
      legalMarkedRootedTargetInputTest q L f p.1 p.2 := by
    have he := legalMarkedRootedTargetTest_sub_input_eq_missing q L kin g t f p.1 p.2
    have hn : (0 : ℝ) ≤ ∫ x, f (legalMarkedCenteredCoordinate q L x - p.2, x.2)
        ∂legalMarkedMissingTargetMeasure q L (L ^ q) kin g t p.1 :=
      integral_nonneg (fun x ↦ hf _)
    linarith
  have hinputsrc : (∫ x, cavityProductTest f (legalInputColorTest 0) x
      ∂legalMarkedRootedColoredInputMeasure q L p) = legalMarkedRootedSourceInputTest q L f p.1 p.2 := by
    rw [integral_legalMarkedRootedColoredInputMeasure q hL]
    have h0 : (fun x ↦ cavityProductTest f (legalInputColorTest 0) (x, 0)) = f := by
      funext x
      change f x * (if (0 : Fin 2) = 0 then 1 else 0) = f x
      simp
    have h1 : (fun x ↦ cavityProductTest f (legalInputColorTest 0) (x, 1)) = fun _ ↦ 0 := by
      funext x
      change f x * (if (1 : Fin 2) = 0 then 1 else 0) = 0
      norm_num
    rw [h0, h1]
    simp only [legalMarkedRootedTargetInputTest, Finset.sum_const_zero, add_zero]
  have hinputtgt : (∫ x, cavityProductTest f (legalInputColorTest 1) x
      ∂legalMarkedRootedColoredInputMeasure q L p) = legalMarkedRootedTargetInputTest q L f p.1 p.2 := by
    rw [integral_legalMarkedRootedColoredInputMeasure q hL]
    have h0 : (fun x ↦ cavityProductTest f (legalInputColorTest 1) (x, 0)) = fun _ ↦ 0 := by
      funext x
      change f x * (if (0 : Fin 2) = 1 then 1 else 0) = 0
      norm_num
    have h1 : (fun x ↦ cavityProductTest f (legalInputColorTest 1) (x, 1)) = f := by
      funext x
      change f x * (if (1 : Fin 2) = 1 then 1 else 0) = f x
      simp
    rw [h0, h1]
    simp only [legalMarkedRootedSourceInputTest, Finset.sum_const_zero, zero_add]
  change (∫ e, cavityProductTest f χ e ∂μ) ≤
      (∫ x, cavityProductTest f (legalInputColorTest 0) x ∂legalMarkedRootedColoredInputMeasure q L p) ∧
    (∫ e, cavityProductTest χ f e ∂μ) ≤
      (∫ x, cavityProductTest f (legalInputColorTest 1) x ∂legalMarkedRootedColoredInputMeasure q L p)
  rw [hinputsrc, hinputtgt]
  have hsread : (∫ e, f e.1 ∂μ) = legalMarkedRootedSourceTest q L kin g t f p.1 p.2 :=
    integral_actualRooted_legalMarkedNormalizedOptimalPlan_source q hL kin g t
      (h := fun x ↦ f x) f.continuous.measurable p.1 p.2
  have htread : (∫ e, f e.2 ∂μ) = legalMarkedRootedTargetTest q L kin g t f p.1 p.2 :=
    integral_actualRooted_legalMarkedNormalizedOptimalPlan_target q hL kin g t
      (h := fun x ↦ f x) f.continuous.measurable p.1 p.2
  rw [hsread] at hsprod
  rw [htread] at htprod
  exact ⟨hsprod.trans hsrow, htprod.trans htrow⟩

/-- One common AE joint weak scene retains every compact source/target
matching-input domination inequality on the same original point measures. -/
theorem ae_legalMarkedInputTestDomination_of_tendsto
    (q : ℕ) (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)), legalMarkedInputTestDomination q s := by
  let K : Set (LegalMarkedOptimalInputScene q) := {s | legalMarkedInputTestDomination q s}
  have hK : IsClosed K := isClosed_legalMarkedInputTestDomination q
  have hn (k : ℕ) : (legalMarkedOptimalInputSceneLaw q α β kin hk g hg t (L k) (hL k) :
      Measure (LegalMarkedOptimalInputScene q)) Kᶜ = 0 := by
    change (∀ᵐ s ∂(legalMarkedOptimalInputSceneLaw q α β kin hk g hg t (L k) (hL k) :
      Measure (LegalMarkedOptimalInputScene q)), s ∈ K)
    apply (ae_map_iff (measurable_legalMarkedOptimalInputObservation q (hL k) hk hg t).aemeasurable
      hK.measurableSet).mpr
    exact .of_forall (legalMarkedInputTestDomination_observation q (hL k) kin g t)
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl
  change (Q : Measure (LegalMarkedOptimalInputScene q)) Kᶜ ≤
    atTop.liminf (fun k ↦ (legalMarkedOptimalInputSceneLaw q α β kin hk g hg t (L k) (hL k) :
      Measure (LegalMarkedOptimalInputScene q)) Kᶜ) at hle
  simp only [hn, liminf_const] at hle
  exact le_antisymm hle bot_le

end OTSelector.Reconstruction
