import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral
import OTSelector.MeasureTheory.FixedMarginalWeightedWeak

/-!
## Lemma skeleton

* **Conditions:** A joint weak limit, a fixed first marginal and almost-everywhere kernel weak limits on a measurable root set.
* **Objects:** The restricted joint limit identified with the original marginal times the limiting kernel.
* **Proof detail:** Use bounded test dominated convergence in kernels, the fixed-marginal weighted weak argument and measure extensionality.

## Mathematical sources

* D. H. Fremlin, *Measure Theory, Volume 4*, Section 452A–452F (integration of families and disintegrations), 452M (product disintegration).
  https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18
* D. H. Fremlin, *Measure Theory, Volume 4*, Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation.
  https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini).
  https://measure.axler.net/MIRA.pdf

**Relationship to the sources:** Restriction to a measurable set needs no boundary-null assumption because its first marginal is fixed; this exact combined theorem is locally proved.
-/

/-! Local kernel identification inside the same joint weak limit. A measurable
root set is retained without renormalizing its original first marginal or
requiring a null boundary. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Probability
set_option linter.unusedSectionVars false

variable {W S : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W]
  [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]

private theorem integrable_joint_test (μ : Measure W) [IsFiniteMeasure μ]
    (K : Kernel W S) [IsMarkovKernel K] (Φ : (W × S) →ᵇ ℝ) :
    Integrable (fun p ↦ Φ p) (μ ⊗ₘ K) :=
  Integrable.of_bound Φ.continuous.aestronglyMeasurable ‖Φ‖
    (ae_of_all _ Φ.norm_coe_le_norm)

/-- Almost-everywhere weak kernel convergence passes bounded continuous joint
tests through the same finite root measure, by its Markov probability bound. -/
theorem integral_kernel_tendsto_of_ae_weak
    (μ : Measure W) [IsFiniteMeasure μ]
    (Kn : ℕ → Kernel W S) [∀ n, IsMarkovKernel (Kn n)]
    (K : Kernel W S) [IsMarkovKernel K]
    (hkernel : ∀ᵐ w ∂μ, Tendsto (β := ProbabilityMeasure S)
      (fun n ↦ (⟨Kn n w,inferInstance⟩ : ProbabilityMeasure S)) atTop
      (𝓝 (⟨K w,inferInstance⟩ : ProbabilityMeasure S)))
    (Φ : (W × S) →ᵇ ℝ) :
    Tendsto (fun n ↦ ∫ w, ∫ s, Φ (w,s) ∂Kn n w ∂μ) atTop
      (𝓝 (∫ w, ∫ s, Φ (w,s) ∂K w ∂μ)) := by
  have hbound (L : Kernel W S) [IsMarkovKernel L] (w : W) :
      ‖∫ s, Φ (w,s) ∂L w‖ ≤ ‖Φ‖ := by
    have hb := norm_integral_le_of_norm_le_const (μ := L w)
      (ae_of_all _ fun s ↦ Φ.norm_coe_le_norm (w,s))
    simpa only [measureReal_def,measure_univ,ENNReal.toReal_one,mul_one] using hb
  apply tendsto_integral_of_dominated_convergence (fun _ : W ↦ ‖Φ‖)
  · intro n
    exact (Φ.continuous.measurable.stronglyMeasurable.integral_kernel_prod_right'
      (κ := Kn n)).aestronglyMeasurable
  · exact integrable_const ‖Φ‖
  · intro n
    exact ae_of_all _ fun w ↦ hbound (Kn n) w
  · filter_upwards [hkernel] with w hw
    let test : S →ᵇ ℝ := Φ.compContinuous
      ⟨fun s ↦ (w,s),continuous_const.prodMk continuous_id⟩
    exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hw test

/-- A fixed-first-marginal joint weak limit has the given limiting kernel on
any measurable root set where the actual finite conditional kernels converge.
The restriction keeps its original mass and all original joint correlations. -/
theorem restrict_joint_weak_limit_eq_compProd_of_ae_kernel_weak
    (η : ProbabilityMeasure W)
    (Rn : ℕ → ProbabilityMeasure (W × S)) (R : ProbabilityMeasure (W × S))
    (hweak : Tendsto Rn atTop (𝓝 R))
    (Kn : ℕ → Kernel W S) [∀ n, IsMarkovKernel (Kn n)]
    (K : Kernel W S) [IsMarkovKernel K]
    (hjoint : ∀ n, (Rn n : Measure (W × S)) = (η : Measure W) ⊗ₘ Kn n)
    (A : Set W) (hA : MeasurableSet A)
    (hkernel : ∀ᵐ w ∂(η : Measure W).restrict A, Tendsto (β := ProbabilityMeasure S)
      (fun n ↦ (⟨Kn n w,inferInstance⟩ : ProbabilityMeasure S)) atTop
      (𝓝 (⟨K w,inferInstance⟩ : ProbabilityMeasure S))) :
    (R : Measure (W × S)).restrict (A ×ˢ univ) =
      (η : Measure W).restrict A ⊗ₘ K := by
  have hmarg (n : ℕ) : (Rn n).map measurable_fst.aemeasurable = η := by
    apply ProbabilityMeasure.toMeasure_injective
    change (Rn n : Measure (W × S)).fst = (η : Measure W)
    rw [hjoint n,Measure.fst_compProd]
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro Φ
  let weight : W → ℝ := A.indicator (fun _ ↦ 1)
  have hweight : Integrable weight (η : Measure W) := (integrable_const 1).indicator hA
  have hweighted := (fixed_first_marginal_weighted_integral_tendsto_of_weak
    η Rn R hweak hmarg weight hweight Φ).2
  have hrestrict (T : Measure (W × S)) :
      (∫ p, weight p.1 * Φ p ∂T) = ∫ p, Φ p ∂T.restrict (A ×ˢ univ) := by
    have heq : (fun p : W × S ↦ weight p.1 * Φ p) =
        (A ×ˢ univ).indicator (fun p ↦ Φ p) := by
      funext p
      by_cases hp : p.1 ∈ A <;> simp [weight,hp]
    rw [heq,integral_indicator (hA.prod MeasurableSet.univ)]
  simp_rw [hrestrict] at hweighted
  have hfinite (n : ℕ) :
      (∫ p, Φ p ∂(Rn n : Measure (W × S)).restrict (A ×ˢ univ)) =
        ∫ w in A, ∫ s, Φ (w,s) ∂Kn n w ∂(η : Measure W) := by
    rw [hjoint n]
    simpa only [Measure.restrict_univ] using Measure.setIntegral_compProd
      hA MeasurableSet.univ (integrable_joint_test (η : Measure W) (Kn n) Φ).integrableOn
  have hlim := integral_kernel_tendsto_of_ae_weak
    ((η : Measure W).restrict A) Kn K hkernel Φ
  have hlimit : Tendsto
      (fun n ↦ ∫ p, Φ p ∂(Rn n : Measure (W × S)).restrict (A ×ˢ univ)) atTop
      (𝓝 (∫ p, Φ p ∂((η : Measure W).restrict A ⊗ₘ K))) := by
    simp_rw [hfinite]
    rw [Measure.integral_compProd (integrable_joint_test ((η : Measure W).restrict A) K Φ)]
    exact hlim
  exact tendsto_nhds_unique hweighted hlimit

end OTSelector.Probability
