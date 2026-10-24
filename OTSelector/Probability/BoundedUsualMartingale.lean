import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.Filtration
import OTSelector.Probability.CountingProcess.RectangleExtension
import OTSelector.Probability.CountingProcess.UsualRectangleLift
import OTSelector.Probability.UsualAugmentation

/-!
# Probability.BoundedUsualMartingale

**Conditions:** A finite base measure and uniformly bounded right-continuous process, strongly adapted to the usual augmentation and satisfying raw zero-increment event integrals.

**Objects:** Right-L1 continuity and the martingale on the usual augmented filtration.

**Proof detail:** Dominated convergence turns the pathwise right-continuity into L1 continuity; lift raw event-integral identities through the augmentation, then use conditional-expectation uniqueness.

**Sources:** [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=373), Section 7.2, “Last rites”, p. 365; Appendix A.2, Theorem A.2.3, p. 462; [Rick Durrett, Probability: Theory and Examples, 5th edition (11 January 2019)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=38), Section 1.6.2, Theorems 1.6.5–1.6.7 (Fatou, monotone convergence, dominated convergence), p. 30; [Rick Durrett, Probability: Theory and Examples, fifth edition (2019 author PDF)](https://sites.math.duke.edu/~rtd/PTE/PTE5_011119.pdf#page=213), Section 4.1, conditional-expectation definition and Uniqueness argument, pp. 205–206; Section 4.1.3, Theorems 4.1.16–4.1.18, pp. 214–215.

Source relation (corollary): The cited primary sections give the mathematical principles used here. The exact source statement, endpoint convention, measure generality and finite encoding are local corollaries or Lean adapters rather than a claim that the book states the Lean theorem verbatim.
-/


/-!
# Bounded raw martingales under the usual augmentation

A uniformly bounded right-continuous process has right `L¹` continuity by dominated
convergence. Thus its raw-filtration increment identities pass to the usual augmentation.
This applies to centered finite marked-event sums without duplicating the counting-process lift.
-/

open Filter Set MeasureTheory
open scoped ENNReal NNReal Topology

namespace OTSelector.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bounded, right-continuous process has right `L¹` continuity under a finite measure. -/
theorem bounded_rightContinuous_rightL1 (μ : Measure Ω) [IsFiniteMeasure μ]
    (M : ℝ≥0 → Ω → ℝ) (hM : ∀ t, AEStronglyMeasurable (M t) μ)
    {C : ℝ} (hbound : ∀ t ω, ‖M t ω‖ ≤ C)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    (s : ℝ≥0) {r : ℕ → ℝ≥0} (hr : Tendsto r atTop (𝓝 s))
    (hright : ∀ᶠ n in atTop, s < r n) :
    Tendsto (fun n ↦ ∫⁻ ω, ‖M (r n) ω - M s ω‖ₑ ∂μ) atTop (𝓝 0) := by
  have hwithin : Tendsto r atTop (𝓝[Ici s] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hr, hright.mono fun _ hn ↦ hn.le⟩
  have hmeas : ∀ᶠ n in atTop,
      AEMeasurable (fun ω ↦ ‖M (r n) ω - M s ω‖ₑ) μ :=
    Eventually.of_forall fun n ↦ ((hM (r n)).sub (hM s)).enorm
  have hdom : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ,
      ‖M (r n) ω - M s ω‖ₑ ≤ ENNReal.ofReal (2 * C) := by
    apply Eventually.of_forall
    intro n
    filter_upwards with ω
    have hnorm : ‖M (r n) ω - M s ω‖ ≤ 2 * C := by
      calc
        _ ≤ ‖M (r n) ω‖ + ‖M s ω‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hbound _ _) (hbound _ _)
        _ = 2 * C := (two_mul C).symm
    simpa only [ofReal_norm] using ENNReal.ofReal_le_ofReal hnorm
  have hfinite : (∫⁻ _ : Ω, ENNReal.ofReal (2 * C) ∂μ) ≠ ∞ :=
    (lintegral_const_lt_top (μ := μ) ENNReal.ofReal_ne_top).ne
  have hlim : ∀ᵐ ω ∂μ,
      Tendsto (fun n ↦ ‖M (r n) ω - M s ω‖ₑ) atTop (𝓝 0) := by
    filter_upwards with ω
    have hzero : Tendsto (fun n ↦ M (r n) ω - M s ω) atTop (𝓝 0) := by
      simpa using ((hrc ω s).tendsto.comp hwithin).sub_const (M s ω)
    simpa only [Function.comp_def, enorm_zero] using
      (continuous_enorm.tendsto (0 : ℝ)).comp hzero
  simpa only [lintegral_zero] using tendsto_lintegral_filter_of_dominated_convergence'
    (μ := μ) (l := atTop) (F := fun n ω ↦ ‖M (r n) ω - M s ω‖ₑ)
    (f := fun _ ↦ (0 : ℝ≥0∞)) (fun _ ↦ ENNReal.ofReal (2 * C))
    hmeas hdom hfinite hlim

/-- Raw increment identities suffice for a bounded right-continuous, usually adapted process. -/
theorem martingale_usualAugmentation_of_bounded_raw
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M : ℝ≥0 → Ω → ℝ)
    (hadapted : StronglyAdapted (usualAugmentation F μ) M)
    {C : ℝ} (hbound : ∀ t ω, ‖M t ω‖ ≤ C)
    (hrc : ∀ ω t, ContinuousWithinAt (fun s ↦ M s ω) (Ici t) t)
    (hraw : ∀ s t, s ≤ t → ∀ B : Set Ω, MeasurableSet[F s] B →
      (∫ ω in B, M t ω - M s ω ∂μ) = 0) :
    Martingale M (usualAugmentation F μ) μ := by
  have hmeas (t) : AEStronglyMeasurable (M t) μ :=
    ((hadapted t).mono ((usualAugmentation F μ).le t)).aestronglyMeasurable
  have hint (t) : Integrable (M t) μ :=
    Integrable.of_bound (hmeas t) C (Eventually.of_forall (hbound t))
  apply CountingProcess.martingale_of_all_setIntegral_eq_of_isFiniteMeasure hadapted hint
  intro s t hst B hB
  apply CountingProcess.setIntegral_eq_of_usualAugmentation_of_rightL1 F M hint
    ?_ (fun s _ hr hrgt ↦ bounded_rightContinuous_rightL1 μ M hmeas hbound hrc s hr hrgt)
    hst hB
  intro r u hru A hA
  have h := hraw r u hru A hA
  rw [integral_sub (hint u).integrableOn (hint r).integrableOn] at h
  exact sub_eq_zero.mp h

end OTSelector.Probability
