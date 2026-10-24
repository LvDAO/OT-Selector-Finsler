import OTSelector.Reconstruction.OriginalPoissonSignedInputMoments
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Hilbert-valued centered moments of the unchanged original Poisson input. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal NNReal RealInnerProductSpace
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The actual Hilbert-valued sum of all original points in a finite input block. -/
def originalPoissonHilbertBlockTest (F : X → H) (b : BlockData X) : H := ∑ i, F (b.2 i)

/-- The same actual point sum in the independent original Poisson-prefix model. -/
def originalPoissonHilbertPrefixSum (F : X → H) (z : ℕ × (ℕ → X)) : H :=
  ∑ i : Fin z.1, F (z.2 i)

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The original Hilbert point sum is a genuine measurable random variable. -/
theorem measurable_originalPoissonHilbertPrefixSum {F : X → H} (hF : Measurable F) :
    Measurable (originalPoissonHilbertPrefixSum F) := by
  apply measurable_from_prod_countable_right
  intro n
  change Measurable (fun y : ℕ → X ↦ ∑ i : Fin n, F (y i))
  exact Finset.measurable_sum Finset.univ (fun i _ ↦ hF.comp (measurable_pi_apply (i : ℕ)))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- A bounded Hilbert response has a true square-integrable original Poisson sum. -/
theorem memLp_two_originalPoissonHilbertPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {F : X → H} (hF : Measurable F) {B : ℝ}
    (hbound : ∀ x, ‖F x‖ ≤ B) :
    MemLp (originalPoissonHilbertPrefixSum F) 2
      ((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_originalPoissonHilbertPrefixSum hF).aestronglyMeasurable).mpr
  apply (((integrable_sq_id_poissonMeasure r).comp_fst
    (Measure.infinitePi (fun _ : ℕ ↦ ν))).mul_const (B^2)).mono'
    ((measurable_originalPoissonHilbertPrefixSum hF).norm.pow_const 2).aestronglyMeasurable
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hsum : ‖originalPoissonHilbertPrefixSum F z‖ ≤ (z.1 : ℝ)*B := by
    calc
      _ ≤ ∑ i : Fin z.1, ‖F (z.2 i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin z.1, B := Finset.sum_le_sum (fun _ _ ↦ hbound _)
      _ = _ := by simp
  simpa only [mul_pow] using pow_le_pow_left₀ (norm_nonneg _) hsum 2

omit [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- Parseval's identity remains exact after integrating an actual square-integrable
Hilbert response. The countable basis is geometric data, not a variance premise. -/
theorem hasSum_integral_inner_sq_eq_integral_norm_sq
    {N : Type*} [Countable N] (b : HilbertBasis N ℝ H)
    (P : Measure X) {F : X → H} (hF : AEStronglyMeasurable F P)
    (hFsq : Integrable (fun x ↦ ‖F x‖^2) P) :
    HasSum (fun i ↦ ∫ x, (inner ℝ (b i) (F x))^2 ∂P) (∫ x, ‖F x‖^2 ∂P) := by
  have hparseval (v : H) : HasSum (fun i ↦ (inner ℝ (b i) v)^2) (‖v‖^2) := by
    simpa only [real_inner_comm v, ← pow_two, real_inner_self_eq_norm_sq] using
      b.hasSum_inner_mul_inner v v
  apply hasSum_integral_of_dominated_convergence
    (bound := fun i x ↦ (inner ℝ (b i) (F x))^2)
  · intro i
    exact ((continuous_const.inner continuous_id).comp_aestronglyMeasurable hF).pow 2
  · intro i
    exact Filter.Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)])
  · exact Filter.Eventually.of_forall (fun x ↦ (hparseval (F x)).summable)
  · simpa only [(hparseval _).tsum_eq] using hFsq
  · exact Filter.Eventually.of_forall (fun x ↦ hparseval (F x))


/-- The unchanged original Poisson Hilbert integral has the exact intensity mean. -/
theorem integral_originalPoissonHilbertPrefixSum
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {F : X → H} (hF : Measurable F) {B : ℝ}
    (hbound : ∀ x, ‖F x‖ ≤ B) :
    (∫ z, originalPoissonHilbertPrefixSum F z
      ∂((poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν)))) =
        (r : ℝ) • ∫ x, F x ∂ν := by
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)
  have hYi := (memLp_two_originalPoissonHilbertPrefixSum ν r hF hbound).integrable
    (by norm_num)
  apply ext_inner_left ℝ
  intro v
  rw [← integral_inner hYi v, inner_smul_right, ← integral_inner hFi v]
  have hscalar : Measurable (fun x ↦ inner ℝ v (F x)) := by fun_prop
  have hscalarBound (x : X) : |inner ℝ v (F x)| ≤ ‖v‖*B := by
    simpa only [Real.norm_eq_abs] using
      (norm_inner_le_norm (𝕜 := ℝ) v (F x)).trans
        (mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg v))
  simpa only [originalPoissonHilbertPrefixSum, poissonPrefixSum, inner_sum] using
    integral_poissonPrefixSum ν r hscalar hscalarBound

/-- The actual centered Hilbert Poisson integral is square integrable and has
exactly the intensity integral of the squared response norm as its second moment. -/
theorem centered_originalPoissonHilbertPrefixSum_moments
    {N : Type*} [Countable N] (b : HilbertBasis N ℝ H)
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {F : X → H} (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖F x‖ ≤ B) :
    let P := (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))
    let Y := fun z ↦ originalPoissonHilbertPrefixSum F z-(r : ℝ) • ∫ x, F x ∂ν
    MemLp Y 2 P ∧ (∫ z, ‖Y z‖^2 ∂P) = (r : ℝ)*(∫ x, ‖F x‖^2 ∂ν) := by
  dsimp only
  let P := (poissonMeasure r).prod (Measure.infinitePi (fun _ : ℕ ↦ ν))
  let Y := fun z ↦ originalPoissonHilbertPrefixSum F z-(r : ℝ) • ∫ x, F x ∂ν
  have hFi : Integrable F ν := Integrable.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)
  have hF2 : MemLp F 2 ν := MemLp.of_bound hF.aestronglyMeasurable B
    (Filter.Eventually.of_forall hbound)
  have hY : MemLp Y 2 P := (memLp_two_originalPoissonHilbertPrefixSum ν r hF hbound).sub
    (memLp_const _)
  refine ⟨hY, ?_⟩
  have hcoord (i : N) : (∫ z, (inner ℝ (b i) (Y z))^2 ∂P) =
      (r : ℝ)*(∫ x, (inner ℝ (b i) (F x))^2 ∂ν) := by
    have hm : Measurable (fun x ↦ inner ℝ (b i) (F x)) := by fun_prop
    have hb (x : X) : |inner ℝ (b i) (F x)| ≤ ‖b i‖*B := by
      simpa only [Real.norm_eq_abs] using
        (norm_inner_le_norm (𝕜 := ℝ) (b i) (F x)).trans
          (mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _))
    simpa only [Y, P, originalPoissonHilbertPrefixSum, poissonPrefixSum,
      inner_sub_right, inner_sum, inner_smul_right, ← integral_inner hFi (b i)] using
      integral_sq_centered_poissonPrefixSum ν r hm (mul_nonneg (norm_nonneg _) hB) hb
  have hsumY := hasSum_integral_inner_sq_eq_integral_norm_sq b P hY.aestronglyMeasurable
    ((memLp_two_iff_integrable_sq_norm hY.aestronglyMeasurable).mp hY)
  simp_rw [hcoord] at hsumY
  exact hsumY.unique ((hasSum_integral_inner_sq_eq_integral_norm_sq b ν hF2.aestronglyMeasurable
    ((memLp_two_iff_integrable_sq_norm hF2.aestronglyMeasurable).mp hF2)).mul_left (r : ℝ))


omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- The genuine original finite-block Hilbert sum is measurable. -/
theorem measurable_originalPoissonHilbertBlockTest {F : X → H} (hF : Measurable F) :
    Measurable (originalPoissonHilbertBlockTest F) := by
  intro U hU
  change MeasurableSet[⨅ n : ℕ,
    (inferInstance : MeasurableSpace (Fin n → X)).map (Sigma.mk n)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro n
  exact (Finset.measurable_sum Finset.univ
    (fun i _ ↦ hF.comp (measurable_pi_apply i))) hU

private theorem measurable_originalPoissonHilbertPrefixEncode :
    Measurable (fun z : ℕ × (ℕ → X) ↦
      (⟨z.1, fun i : Fin z.1 ↦ z.2 i⟩ : BlockData X)) := by
  apply measurable_from_prod_countable_right
  intro n
  exact (measurable_sigma_mk n).comp
    (measurable_pi_lambda _ (fun i : Fin n ↦ measurable_pi_apply (i : ℕ)))

/-- All original finite-array points retain their genuine Hilbert Campbell mean. -/
theorem integral_originalPoissonHilbertBlockTest
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {F : X → H} (hF : Measurable F) {B : ℝ} (hbound : ∀ x, ‖F x‖ ≤ B) :
    (∫ b, originalPoissonHilbertBlockTest F b
      ∂blockDataLaw ν (fun n ↦ poissonMeasure r {n})) = (r : ℝ) • ∫ x, F x ∂ν := by
  rw [blockDataLaw_eq_map_cloud,
    integral_map measurable_originalPoissonHilbertPrefixEncode.aemeasurable
      (measurable_originalPoissonHilbertBlockTest hF).aestronglyMeasurable]
  exact integral_originalPoissonHilbertPrefixSum ν r hF hbound

/-- The literal finite-array law has the full centered Hilbert second moment. -/
theorem centered_originalPoissonHilbertBlockTest_moments
    {N : Type*} [Countable N] (b : HilbertBasis N ℝ H)
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0)
    {F : X → H} (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖F x‖ ≤ B) :
    let P := blockDataLaw ν (fun n ↦ poissonMeasure r {n})
    let Y := fun z ↦ originalPoissonHilbertBlockTest F z-(r : ℝ) • ∫ x, F x ∂ν
    MemLp Y 2 P ∧ (∫ z, ‖Y z‖^2 ∂P) = (r : ℝ)*(∫ x, ‖F x‖^2 ∂ν) := by
  dsimp only
  have hm : Measurable (fun z ↦ originalPoissonHilbertBlockTest F z-
      (r : ℝ) • ∫ x, F x ∂ν) := (measurable_originalPoissonHilbertBlockTest hF).sub
        measurable_const
  obtain ⟨hLp, hmoment⟩ := centered_originalPoissonHilbertPrefixSum_moments b ν r hF hB hbound
  rw [blockDataLaw_eq_map_cloud]
  constructor
  · exact (memLp_map_measure_iff hm.aestronglyMeasurable
      measurable_originalPoissonHilbertPrefixEncode.aemeasurable).mpr hLp
  · rw [integral_map measurable_originalPoissonHilbertPrefixEncode.aemeasurable
      (hm.norm.pow_const 2).aestronglyMeasurable]
    exact hmoment

omit [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] in
/-- The Hilbert response is integrated against the actual finite random point
measure, retaining every original multiplicity. -/
theorem integral_legalInputBlockMeasure_hilbert [MeasurableSingletonClass X]
    (b : BlockData X) (F : X → H) :
    (∫ x, F x ∂legalInputBlockMeasure b) = originalPoissonHilbertBlockTest F b := by
  unfold legalInputBlockMeasure
  rw [integral_finsetSum_measure (fun i _ ↦ integrable_dirac (by simp))]
  simp only [integral_dirac, originalPoissonHilbertBlockTest]

/-- The exact-intensity version uses the actual stochastic point measure on
both sides; the supplied intensity identity fixes every normalization. -/
theorem centered_originalPoissonHilbertBlockMeasure_moments
    [MeasurableSingletonClass X] {N : Type*} [Countable N] (b : HilbertBasis N ℝ H)
    (ν : Measure X) [IsProbabilityMeasure ν] (r : ℝ≥0) (intensity : Measure X)
    (hintensity : (r : ℝ≥0∞) • ν = intensity)
    {F : X → H} (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ x, ‖F x‖ ≤ B) :
    let P := blockDataLaw ν (fun n ↦ poissonMeasure r {n})
    let Y := fun z ↦ (∫ x, F x ∂legalInputBlockMeasure z)-(∫ x, F x ∂intensity)
    MemLp Y 2 P ∧ (∫ z, ‖Y z‖^2 ∂P) = ∫ x, ‖F x‖^2 ∂intensity := by
  simpa only [integral_legalInputBlockMeasure_hilbert, ← hintensity,
    integral_smul_measure, ENNReal.coe_toReal, smul_eq_mul] using
      centered_originalPoissonHilbertBlockTest_moments b ν r hF hB hbound

end OTSelector.Reconstruction
