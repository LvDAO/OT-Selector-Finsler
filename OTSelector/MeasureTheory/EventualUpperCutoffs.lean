import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-!
## Lemma skeleton

* **Conditions:** A finite measure, measurable pressure sequence and reference, and almost-everywhere eventual upper control by reference+every positive epsilon.
* **Objects:** Measurable retained sets with complement mass tending to zero and a fixed-epsilon pointwise pressure bound.
* **Proof detail:** Take the sublevel sets p_n<=pref+epsilon; their bad indicators tend to zero almost everywhere and are bounded by 1, so dominated convergence applies.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3B, Theorem 3.31, p. 92 (Dominated Convergence).
  https://measure.axler.net/MIRA.pdf#page=107

**Relationship to the sources:** DCT on indicators only. No common majorant for the pressure sequence is required.
-/

/-! Deterministic original root cutoffs turn true pointwise pressure upper
limits into vanishing original root loss, without dominating every approximation. -/
open Set Function MeasureTheory Filter
open scoped Topology
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- True original pointwise pressure upper limits produce measurable original
root cutoffs with vanishing actual lost mass. These cutoffs use population
pressures only and can be fixed before all original iid samples. -/
theorem exists_original_pressure_root_cutoffs
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (p : ℕ → X → ℝ) (pref : X → ℝ)
    (hp : ∀ n, Measurable (p n)) (hpref : Measurable pref)
    (hupper : ∀ᵐ x ∂μ, ∀ ε > 0, ∀ᶠ n in atTop, p n x < pref x + ε)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ → Set X, (∀ n, MeasurableSet (K n)) ∧
      Tendsto (fun n ↦ μ.real (K n)ᶜ) atTop (𝓝 0) ∧
      ∀ n x, x ∈ K n → p n x ≤ pref x + ε := by
  let K := fun n ↦ {x | p n x ≤ pref x + ε}
  have hK n : MeasurableSet (K n) := measurableSet_le (hp n) (hpref.add_const ε)
  let loss := fun n ↦ ((K n)ᶜ).indicator (fun _ ↦ (1 : ℝ))
  have hI n : Integrable (loss n) μ := (integrable_const (1 : ℝ)).indicator (hK n).compl
  have hdom n : ∀ x, ‖loss n x‖ ≤ 1 := by
    intro x
    by_cases hx : x ∈ (K n)ᶜ
    · simp only [loss,indicator_of_mem hx,norm_one,le_refl]
    · simp only [loss,indicator_of_notMem hx,norm_zero,zero_le_one]
  have hpoint : ∀ᵐ x ∂μ, Tendsto (fun n ↦ loss n x) atTop (𝓝 0) := by
    filter_upwards [hupper] with x hx
    apply (tendsto_const_nhds : Tendsto (fun _n : ℕ ↦ (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [hx ε hε] with n hn
    simp only [loss,K,indicator_of_notMem (show x ∉ {x | p n x ≤ pref x + ε}ᶜ from by
      simpa only [mem_compl_iff,mem_ofPred_eq,not_not] using hn.le)]
  have hlim : Tendsto (fun n ↦ ∫ x, loss n x ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (fun _ ↦ (1 : ℝ))
      (F := loss) (f := fun _ ↦ (0 : ℝ)) (fun n ↦ (hI n).aestronglyMeasurable)
      (integrable_const _) (fun n ↦ .of_forall (hdom n)) hpoint
    simpa only [integral_zero] using hh
  have heq n : (∫ x, loss n x ∂μ) = μ.real (K n)ᶜ := by
    simp only [loss,integral_indicator (hK n).compl,integral_const,Measure.restrict_apply_univ,
      smul_eq_mul,mul_one,measureReal_def]
  refine ⟨K,hK,?_,fun _ _ hx ↦ hx⟩
  simpa only [heq] using hlim

end OTSelector.Reconstruction
