import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
## Lemma skeleton

* **Conditions:** A finite measurable index type with measurable singletons, a measurable finite quantizer T and an integrable real density f for the readout identities; nonnegativity only needs f>=0 almost everywhere.
* **Objects:** Original density cell weights, their exact weighted readout and total-mass sum, and nonnegative weights.
* **Proof detail:** Integrate f on the literal fibers T^{-1}{i}; write the finite-valued readout as a finite sum of cell indicators, interchange the finite integral sum and use positivity.

## Mathematical sources

* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.11, p. 78 (Monotone Convergence).
  https://measure.axler.net/MIRA.pdf#page=93
* Sheldon Axler, *Measure, Integration & Real Analysis (author PDF, 12 June 2026)*, Section 3A, Theorem 3.23, p. 84; Section 3B, Theorem 3.25, p. 88.
  https://measure.axler.net/MIRA.pdf#page=99

**Relationship to the sources:** Finite indicator integration. Cells are neither renormalized nor required to have positive mass; the nonnegative totalized-integral statement does not require an integrability hypothesis.
-/

/-! Exact finite-cell weights and readouts of the original density, without
normalizing individual cells or discarding zero-mass cells. -/
open MeasureTheory Set
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction
variable {X I : Type*} [MeasurableSpace X] [Fintype I] [MeasurableSpace I]
  [MeasurableSingletonClass I]

/-- A finite quantizer records the original density mass of its literal cell. -/
def originalDensityCellWeight (μ : Measure X) (f : X → ℝ) (T : X → I) (i : I) : ℝ :=
  ∫ x in T ⁻¹' {i}, f x ∂μ

/-- The weighted readout of a finite quantizer equals the original density
integral of that same finite-valued readout. -/
theorem originalDensityCellWeight_readout (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) (T : X → I) (hT : Measurable T) (a : I → ℝ) :
    (∑ i, originalDensityCellWeight μ f T i * a i) = ∫ x, a (T x) * f x ∂μ := by
  classical
  have hcell (i : I) : Integrable ((T ⁻¹' {i}).indicator f) μ :=
    hf.indicator ((measurableSet_singleton i).preimage hT)
  calc
    _ = ∑ i, ∫ x, (T ⁻¹' {i}).indicator f x * a i ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_mul_const, integral_indicator ((measurableSet_singleton i).preimage hT)]
      rfl
    _ = ∫ x, ∑ i, (T ⁻¹' {i}).indicator f x * a i ∂μ :=
      (integral_finsetSum _ (fun i _ ↦ (hcell i).mul_const (a i))).symm
    _ = _ := by
      congr 1
      funext x
      simp [Set.indicator, mul_comm, eq_comm]

/-- Cell masses add to the entire original density mass. -/
theorem sum_originalDensityCellWeight (μ : Measure X) (f : X → ℝ)
    (hf : Integrable f μ) (T : X → I) (hT : Measurable T) :
    (∑ i, originalDensityCellWeight μ f T i) = ∫ x, f x ∂μ := by
  simpa only [mul_one, one_mul] using originalDensityCellWeight_readout μ f hf T hT (fun _ ↦ 1)

omit [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I] in
/-- Nonnegative original densities give nonnegative cell weights, including
cells whose original mass is zero. -/
theorem originalDensityCellWeight_nonneg (μ : Measure X) (f : X → ℝ)
    (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (T : X → I) (i : I) :
    0 ≤ originalDensityCellWeight μ f T i := by
  exact integral_nonneg_of_ae (ae_restrict_of_ae hf0)

end OTSelector.Reconstruction
