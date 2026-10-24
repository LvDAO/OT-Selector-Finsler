import OTSelector.MeasureTheory.Lp.SmoothGradientCoordinates
import OTSelector.Transport.DensityNeumannInterpolation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannTests.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.OriginalLegalScreeningComparatorNeumannTests`; the selected original proof blocks follow. -/
section

/-!
Conditions: A finite measure carried on the set where a real smooth cutoff is locally one, equal endpoint masses and a squared discrepancy bound on mean-zero tests.

Objects: Vanishing gradient of that cutoff and extension of the estimate to every test in the same smooth support space.

Proof detail: Subtract the actual mean times the locally-one cutoff; the gradient is unchanged and equal masses cancel the constant discrepancy, then take square roots.

Sources: Jiří Lebl, Section 8.3, Proposition 8.3.6 and Theorem 8.3.7, pp. 37–38; Section 8.6, pp. 60–61 (https://www.jirka.org/ra/realanal2.pdf#page=37); Terence Tao, Section 1.10.1, Lemma 1.10.1, pp. 134–135, and Exercise 1.10.6, p. 136 (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=143); Sheldon Axler, Section 3A (integration), Theorem 3.31 (dominated convergence); Section 5B, Theorems 5.28/5.32 (Tonelli/Fubini) (https://measure.axler.net/MIRA.pdf).
Relation: Mean-zero extension by an actual cutoff; it does not merely assume a test extension callback.
-/

/-! A real locally constant cutoff extends the actual mean-zero Neumann
estimate to every test in the same compactly supported smooth space. -/

open MeasureTheory Set Filter TopologicalSpace
open scoped Distributions Topology

noncomputable section
namespace OTSelector.Reconstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A cutoff locally equal to one at almost every original point has zero
actual physical gradient in the original L2 measure. -/
theorem smoothPhysicalGradientLtwo_eq_zero_of_locally_one
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (K₀ : Set (ι → ℝ)) (χ : 𝓓_{K}(ι → ℝ, ℝ))
    (hμ : ∀ᵐ z ∂μ, z ∈ K₀)
    (hχ : ∀ z ∈ K₀, (χ : (ι → ℝ) → ℝ) =ᶠ[𝓝 z] fun _ ↦ 1) :
    smoothPhysicalGradientLtwo K μ χ = 0 := by
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [smoothPhysicalGradientLtwo_ae K μ χ, hμ] with z hgrad hz
  have hd : fderiv ℝ χ z = 0 := by
    rw [(hχ z hz).fderiv_eq, fderiv_const_apply]
  rw [hgrad, hd, map_zero]
  rfl

/-- Equal actual density masses eliminate the centering constant. A genuine
cutoff equal to one near the measure's support preserves the same test space
and gradient, giving the all-test norm bound from the mean-zero squared bound. -/
theorem all_test_bound_of_meanZero_squared_bound
    (K : Compacts (ι → ℝ)) (μ : Measure (ι → ℝ)) [IsFiniteMeasure μ]
    (K₀ : Set (ι → ℝ)) (χ : 𝓓_{K}(ι → ℝ, ℝ))
    (hμ : ∀ᵐ z ∂μ, z ∈ K₀)
    (hχ : ∀ z ∈ K₀, (χ : (ι → ℝ) → ℝ) =ᶠ[𝓝 z] fun _ ↦ 1)
    (hmass : 0 < μ.real univ) (f g : (ι → ℝ) → ℝ)
    (hf : Integrable f μ) (hg : Integrable g μ)
    (hmassfg : (∫ z, f z ∂μ) = ∫ z, g z ∂μ)
    {B : ℝ} (hB : 0 ≤ B)
    (hmean : ∀ ψ : 𝓓_{K}(ι → ℝ, ℝ), (∫ z, ψ z ∂μ) = 0 →
      |∫ z, ψ z * (f z - g z) ∂μ| ^ 2 ≤
        B * ‖smoothPhysicalGradientLtwo K μ ψ‖ ^ 2) :
    ∀ φ : 𝓓_{K}(ι → ℝ, ℝ),
      ‖(∫ z, φ z * f z ∂μ) - ∫ z, φ z * g z ∂μ‖ ≤
        Real.sqrt B * ‖smoothPhysicalGradientLtwo K μ φ‖ := by
  have hχae : (χ : (ι → ℝ) → ℝ) =ᵐ[μ] fun _ ↦ 1 :=
    hμ.mono fun z hz ↦ (hχ z hz).eq_of_nhds
  have hχgrad := smoothPhysicalGradientLtwo_eq_zero_of_locally_one K μ K₀ χ hμ hχ
  intro φ
  have hφI : Integrable φ μ := by
    simpa only [mul_one] using
      smoothTest_mul_density_integrable K μ φ (integrable_const (1 : ℝ))
  let a := (∫ z, φ z ∂μ) / μ.real univ
  let ψ : 𝓓_{K}(ι → ℝ, ℝ) := φ - a • χ
  have hψpoint : (ψ : (ι → ℝ) → ℝ) =ᵐ[μ] fun z ↦ φ z - a := by
    filter_upwards [hχae] with z hz
    change φ z - a * χ z = φ z - a
    rw [hz, mul_one]
  have hψmean : (∫ z, ψ z ∂μ) = 0 := by
    rw [integral_congr_ae hψpoint, integral_sub hφI (integrable_const a),
      integral_const, smul_eq_mul]
    dsimp only [a]
    field_simp [hmass.ne']
    ring
  have hψgrad : smoothPhysicalGradientLtwo K μ ψ = smoothPhysicalGradientLtwo K μ φ := by
    simp only [ψ, map_sub, map_smul, hχgrad, smul_zero, sub_zero]
  have hfgI : Integrable (fun z ↦ f z - g z) μ := hf.sub hg
  have hφfgI : Integrable (fun z ↦ φ z * (f z - g z)) μ :=
    smoothTest_mul_density_integrable K μ φ hfgI
  have hpair : (∫ z, ψ z * (f z - g z) ∂μ) = ∫ z, φ z * (f z - g z) ∂μ := by
    calc
      _ = ∫ z, (φ z - a) * (f z - g z) ∂μ :=
        integral_congr_ae (by filter_upwards [hψpoint] with z hz; rw [hz])
      _ = (∫ z, φ z * (f z - g z) ∂μ) - a * ∫ z, (f z - g z) ∂μ := by
        simp only [sub_mul]
        rw [integral_sub hφfgI (hfgI.const_mul a), integral_const_mul]
      _ = _ := by rw [integral_sub hf hg, hmassfg, sub_self, mul_zero, sub_zero]
  have hs := hmean ψ hψmean
  rw [hpair, hψgrad, sq_abs] at hs
  have hread : (∫ z, φ z * (f z - g z) ∂μ) =
      (∫ z, φ z * f z ∂μ) - ∫ z, φ z * g z ∂μ := by
    simp only [mul_sub]
    exact integral_sub (smoothTest_mul_density_integrable K μ φ hf)
      (smoothTest_mul_density_integrable K μ φ hg)
  rw [← hread, Real.norm_eq_abs]
  apply abs_le_of_sq_le_sq _ (mul_nonneg (Real.sqrt_nonneg B) (norm_nonneg _))
  calc
    _ ≤ B * ‖smoothPhysicalGradientLtwo K μ φ‖ ^ 2 := hs
    _ = _ := by rw [mul_pow, Real.sq_sqrt hB]

end OTSelector.Reconstruction

end
end
