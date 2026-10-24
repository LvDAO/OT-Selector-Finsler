import OTSelector.Probability.CavitySemidiscreteMarkWindows
import OTSelector.Probability.CavitySemidiscreteRootedWitness
import OTSelector.Probability.CavitySemidiscreteEnergyBridge

/-!
# Mark-window bounds from a scaled slack energy

The mark-window estimate is stated for an arbitrary measurable `ℝ≥0∞`-valued
weight.  This module instantiates it with the scaled slack
`w ω e = ENNReal.ofReal (k * slack ω e.1 e.2)` and threshold
`r = ENNReal.ofReal (k * delta)`.  The positivity of `k` and `delta` makes the
threshold nonzero and finite, while the almost-sure slack gap transfers the mark
implication; the expected scaled slack energy is then the right-hand side.
-/

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section
namespace OTSelector.Probability

variable {ι A B Ω : Type*} [Fintype ι] [MeasurableSpace A] [MeasurableSpace B]
  [MeasurableSpace Ω]

/-- Mark-window mass bound for a scaled slack energy.  With the threshold
`ENNReal.ofReal (k * delta)` and weight `ENNReal.ofReal (k * slack …)`, the
original rooted mark-window estimate yields a bound by the expected scaled slack
energy divided by the scaled threshold. -/
theorem lintegral_rootedPlan_markWindow_le_of_slackEnergy
    {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [IsProbabilityMeasure μ]
    (p : Ω → Fin (m + 1) → ℝ)
    (a : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (ham : ∀ j, Measurable (fun v ↦ a v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (hUf : volume U ≠ ⊤) (E : Set (A × B)) (hE : MeasurableSet E)
    (slack : Ω → ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (k delta : ℝ) (hk : 0 < k) (hdelta : 0 < delta)
    (hslackm : ∀ ω, Measurable (Function.uncurry (slack ω)))
    (hgood : ∀ᵐ ω ∂P,
      IsSemidiscreteAllocation μ (p ω) (fun s ↦ a (ω, s)) ∧
      ∀ᵐ e ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s)),
        (e.1.2, (Y ω e.2).2) ∈ E → delta ≤ slack ω e.1 e.2)
    (C : ℝ≥0∞)
    (henergy : (∫⁻ ω, ∫⁻ e,
      ENNReal.ofReal (k * slack ω e.1 e.2)
      ∂semidiscreteAllocationMeasure μ (fun s ↦ a (ω, s)) ∂P) ≤ C) :
    (∫⁻ v : Ω × (ι → ℝ),
      cavitySpatialRootedPlan μ (fun s ↦ a (v.1, s)) (Y v.1) N v.2
        (cavityMarkWindow U E)
      ∂P.prod (cavityRootMeasure volume D N)) ≤
      volume U * C / ENNReal.ofReal (k * delta) := by
  have hw : ∀ ω, Measurable
      (fun e : ((ι → ℝ) × A) × Fin (m + 1) ↦
        ENNReal.ofReal (k * slack ω e.1 e.2)) := by
    intro ω
    have hm : Measurable (fun e : ((ι → ℝ) × A) × Fin (m + 1) ↦
        slack ω e.1 e.2) := hslackm ω
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul hm)
  have hr0 : ENNReal.ofReal (k * delta) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (mul_pos hk hdelta))
  have hrt : ENNReal.ofReal (k * delta) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine lintegral_original_rootedPlan_markWindow_le P μ p a ham Y hY N hN D U hU
    hUf E hE (fun ω e ↦ ENNReal.ofReal (k * slack ω e.1 e.2)) hw
    (ENNReal.ofReal (k * delta)) hr0 hrt ?_ C henergy
  filter_upwards [hgood] with ω hω
  refine ⟨hω.1, ?_⟩
  filter_upwards [hω.2] with e he hE'
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (he hE') hk.le)

end OTSelector.Probability
