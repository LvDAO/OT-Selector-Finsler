import OTSelector.Analysis.Convex.FiniteSoftMinimum
import OTSelector.Analysis.Convex.QuadraticSoftGradientBound
import OTSelector.Analysis.Convex.QuadraticSoftHamiltonJacobi
import OTSelector.Analysis.Convex.TimeDependentSoftTests
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiGridError.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalNeumannTimeDependentHamiltonJacobiGridError`; the selected original proof blocks follow. -/
section

/-!
Conditions: A compactly carried finite measure, nonnegative integrable density, measurable quantizer and actual displacement bound inside a convex domain with bounded node distances.

Objects: Integrability and an explicit quadrature error for the actual time-dependent quadratic soft test.

Proof detail: Bound its actual spatial gradient by node distance divided by positive shifted time, use the mean-value inequality on the convex domain and integrate against the original density.

Sources: Jiří Lebl, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47 (https://www.jirka.org/ra/realanal2.pdf#page=46); Stephen Boyd, Section 3.1.5, pp. 72–74, log-sum-exp example and derivative calculation (https://web.stanford.edu/~boyd/cvxbook/bv_cvxbook.pdf#page=86); Sheldon Axler, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini) (https://measure.axler.net/MIRA.pdf).
Relation: Quantitative gradient/quadrature consequence. It preserves epsilon merely nonzero where that is all the statement needs.
-/

/-! Price-independent finite-grid readout errors for the actual physical soft tests. -/
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option maxHeartbeats 1200000

variable {ι I : Type*} [Fintype ι] [Fintype I] [Nonempty I]

/-- The actual soft test is integrable on the original compactly carried law,
and quantizing that law costs only the original geometric gradient bound. -/
theorem neumannQuadraticSoftTest_grid_error
    (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    {K₀ : Set (ι → ℝ)} (hK₀ : IsCompact K₀) (hsupp : ∀ᵐ x ∂μ, x ∈ K₀)
    (f : (ι → ℝ) → ℝ) (hf : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x)
    (Q : (ι → ℝ) → (ι → ℝ)) (hQ : Measurable Q)
    (ε : ℝ) (hε : ε ≠ 0) (a : I → ℝ) (y : I → EuclideanSpace ℝ ι)
    (δ t D h : ℝ) (hτ : 0 < t+δ) (hD0 : 0 ≤ D) (hh : 0 ≤ h)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : Convex ℝ Ω)
    (hnode : ∀ z ∈ Ω, ∀ i, ‖z-y i‖ ≤ D)
    (hmem : ∀ᵐ x ∂μ, (EuclideanSpace.equiv ι ℝ).symm x ∈ Ω ∧
      (EuclideanSpace.equiv ι ℝ).symm (Q x) ∈ Ω)
    (hdisp : ∀ᵐ x ∂μ,
      ‖(EuclideanSpace.equiv ι ℝ).symm (Q x)-(EuclideanSpace.equiv ι ℝ).symm x‖ ≤ h) :
    Integrable (fun x ↦ neumannQuadraticSoftTest ε a y δ t x*f x) μ ∧
    Integrable (fun x ↦ neumannQuadraticSoftTest ε a y δ t (Q x)*f x) μ ∧
    |(∫ x, neumannQuadraticSoftTest ε a y δ t (Q x)*f x ∂μ)-
      (∫ x, neumannQuadraticSoftTest ε a y δ t x*f x ∂μ)| ≤
        (D/(t+δ)*h)*(∫ x, f x ∂μ) := by
  let ψ := neumannQuadraticSoftTest ε a y δ t
  let L := D/(t+δ)*h
  have hL0 : 0 ≤ L := mul_nonneg (div_nonneg hD0 hτ.le) hh
  have hψ : Continuous ψ := (contDiff_neumannQuadraticSoftTest ε a y δ t hτ.ne').continuous
  obtain ⟨C, hC⟩ := (hK₀.image hψ).isBounded.exists_norm_le
  have horig : Integrable (fun x ↦ ψ x*f x) μ := by
    apply (hf.norm.const_mul C).mono' (hψ.aestronglyMeasurable.mul hf.aestronglyMeasurable)
    filter_upwards [hsupp] with x hx
    simp only [Pi.mul_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hC _ ⟨x, hx, rfl⟩) (norm_nonneg _)
  have herr : ∀ᵐ x ∂μ, ‖ψ (Q x)-ψ x‖ ≤ L := by
    filter_upwards [hmem, hdisp] with x hx hd
    exact (quadraticSoftMinimum_norm_sub_le ε hε a y hτ hΩ hnode hx.1 hx.2).trans
      (mul_le_mul_of_nonneg_left hd (div_nonneg hD0 hτ.le))
  have hmeas : AEStronglyMeasurable (fun x ↦ (ψ (Q x)-ψ x)*f x) μ :=
    ((hψ.measurable.comp hQ).aestronglyMeasurable.sub hψ.aestronglyMeasurable).mul
      hf.aestronglyMeasurable
  have hdiff : Integrable (fun x ↦ (ψ (Q x)-ψ x)*f x) μ := by
    apply (hf.norm.const_mul L).mono' hmeas
    filter_upwards [herr] with x hx
    rw [norm_mul]
    exact mul_le_mul hx le_rfl (norm_nonneg _) hL0
  have hquant : Integrable (fun x ↦ ψ (Q x)*f x) μ := by
    exact (hdiff.add horig).congr (Filter.Eventually.of_forall (fun x ↦ by
      change (ψ (Q x)-ψ x)*f x+ψ x*f x = ψ (Q x)*f x
      ring))
  refine ⟨horig, hquant, ?_⟩
  change |(∫ x, ψ (Q x)*f x ∂μ)-(∫ x, ψ x*f x ∂μ)| ≤ L*(∫ x, f x ∂μ)
  have heq : (∫ x, ψ (Q x)*f x ∂μ)-(∫ x, ψ x*f x ∂μ) =
      ∫ x, (ψ (Q x)-ψ x)*f x ∂μ := by
    rw [← integral_sub hquant horig]
    congr 1
    funext x
    ring
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x, L*f x ∂μ := norm_integral_le_of_norm_le (hf.const_mul L) (by
      filter_upwards [herr, hf0] with x hx hf0x
      rw [norm_mul, Real.norm_of_nonneg hf0x]
      exact mul_le_mul_of_nonneg_right hx hf0x)
    _ = _ := integral_const_mul L f

end OTSelector.Reconstruction

end
end
