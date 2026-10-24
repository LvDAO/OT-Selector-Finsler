import OTSelector.Probability.CavitySemidiscretePressureComparison
import OTSelector.Probability.CavitySemidiscreteGridPacking

/-!
# Uniform-root cycle witnesses in the original finite environment

Scaling a probability allocation to mass `N` and averaging its bounded witness
against a root measure of density `1 / N` cancel exactly. Opposite-tilt
optimality therefore gives the phase-volume times `t * G` bound independently
of the finite sample size.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal

noncomputable section
namespace OTSelector.Probability

variable {E : Type*} [MeasurableSpace E]

/-- Root averaging with total normalization mass `N`. -/
def cavityRootMeasure (β : Measure E) (D : Set E) (N : ℝ) : Measure E :=
  (ENNReal.ofReal N)⁻¹ • β.restrict D

/-- This is the actual uniform probability root when the domain has volume `N`. -/
theorem isProbabilityMeasure_cavityRootMeasure
    (β : Measure E) (D : Set E) (N : ℝ) (hN : 0 < N) (hD : β D = ENNReal.ofReal N) :
    IsProbabilityMeasure (cavityRootMeasure β D N) := by
  constructor
  simp only [cavityRootMeasure, Measure.smul_apply, Measure.restrict_apply_univ, hD,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hN)) ENNReal.ofReal_ne_top

/-- The increase from probability mass to total mass `N` cancels the independent
uniform-root normalization, including the truncation of a witness at one. -/
theorem lintegral_cavityRoot_capped_scale_le
    (β : Measure E) (D : Set E) (N ε : ℝ) (hN : 0 < N) (hε : 0 ≤ ε)
    (f : E → ℝ) :
    (∫⁻ z, ENNReal.ofReal (ε * min 1 (N * f z)) ∂cavityRootMeasure β D N) ≤
      ∫⁻ z, ENNReal.ofReal (ε * f z) ∂β := by
  rw [cavityRootMeasure, lintegral_smul_measure]
  simp only [smul_eq_mul]
  calc
    _ ≤ (ENNReal.ofReal N)⁻¹ *
        ∫⁻ z in D, ENNReal.ofReal N * ENNReal.ofReal (ε * f z) ∂β := by
      gcongr with z
      rw [← ENNReal.ofReal_mul hN.le]
      apply ENNReal.ofReal_le_ofReal
      calc
        ε * min 1 (N * f z) ≤ ε * (N * f z) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) hε
        _ = N * (ε * f z) := by ring
    _ = ∫⁻ z in D, ENNReal.ofReal (ε * f z) ∂β := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
        ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hN)) ENNReal.ofReal_ne_top,
        one_mul]
    _ ≤ _ := setLIntegral_le_lintegral _ _

variable {m : ℕ} {ι S : Type*} [Fintype ι] [MeasurableSpace S]

/-- On the common finite environment of the actual opposite-tilt optimizers, the
bounded witness of the mass-`N` plans has uniform-root expectation at most
`K ^ q * t * G / ε`, in its division-free form. -/
theorem lintegral_cavityRoot_opposite_tilt_cycle_witness_le
    (μ : Measure S) [IsProbabilityMeasure μ] (p : Fin (m + 1) → ℝ)
    (c g a₀ aplus aminus : S → Fin (m + 1) → ℝ)
    (t G : ℝ) (ht : 0 ≤ t)
    (h₀ : IsOptimalSemidiscreteAllocation μ p c a₀)
    (hplus : IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s j + t * g s j) aplus)
    (hminus : IsOptimalSemidiscreteAllocation μ p (fun s j ↦ c s j + (-t) * g s j) aminus)
    (hc : ∀ j, Integrable (fun s ↦ c s j) μ)
    (hg : ∀ j, Integrable (fun s ↦ g s j) μ)
    (hbound : ∀ᵐ s ∂μ, ∀ j, |g s j| ≤ G)
    (hplusm : ∀ j, Measurable (fun s ↦ aplus s j))
    (hminusm : ∀ j, Measurable (fun s ↦ aminus s j))
    (loc : S → (ι → ℝ)) (K : ℝ) (hK : 0 < K)
    (A B : (ι → ℝ) → Set S)
    (hA : MeasurableSet {x : (ι → ℝ) × S | x.2 ∈ A x.1})
    (hB : MeasurableSet {x : (ι → ℝ) × S | x.2 ∈ B x.1})
    (hAB : ∀ z, Disjoint (A z) (B z))
    (hcell : ∀ z, A z ∪ B z ⊆ loc ⁻¹' cavityGridCube ι K z)
    (J L : (ι → ℝ) → Finset (Fin (m + 1)))
    (hJ : ∀ j, MeasurableSet {z | j ∈ J z})
    (hL : ∀ j, MeasurableSet {z | j ∈ L z})
    (ε : ℝ) (hε : 0 ≤ ε)
    (hgap : ∀ z, ∀ s ∈ A z, ∀ s' ∈ B z, ∀ j ∈ J z, ∀ k ∈ L z,
      ε ≤ c s j + c s' k - c s k - c s' j)
    (D : Set (ι → ℝ)) (N : ℝ) (hN : 0 < N) :
    (∫⁻ z, ENNReal.ofReal (ε * min 1 (N * min
      (semidiscreteBlockMass μ (fun s j ↦ (aplus s j + aminus s j) / 2) (A z) (J z))
      (semidiscreteBlockMass μ (fun s j ↦ (aplus s j + aminus s j) / 2) (B z) (L z))))
      ∂cavityRootMeasure volume D N) ≤
      ENNReal.ofReal (t * G) * ENNReal.ofReal K ^ Fintype.card ι := by
  have hp := lintegral_semidiscrete_grid_cycle_mass_le μ p
    (fun s j ↦ (aplus s j + aminus s j) / 2) a₀ c (hplus.1.average hminus.1)
    (fun j ↦ ((hplusm j).add (hminusm j)).div_const 2)
    h₀ hc loc K hK A B hA hB hAB hcell J L hJ hL ε hε hgap
  have he := semidiscrete_opposite_tilt_excess μ p c g a₀ aplus aminus
    h₀.1 hplus.1 hminus.1 hc hg G hbound t ht h₀.2 hplus.2 hminus.2
  exact (lintegral_cavityRoot_capped_scale_le volume D N ε hN hε _).trans
    (hp.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal
      (he.2.1.trans he.2.2.1)) _))

end OTSelector.Probability
