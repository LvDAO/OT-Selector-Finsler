import OTSelector.LinearAlgebra.VectorFamilyMatrixRank
import OTSelector.Geometry.FinslerGraphFocalFinite

/-!
# Actual position rank from graph focal expansions

Matching bases identify the position block of the real phase differential with its
square matrix. The inverse-pole conclusion therefore gives injectivity of the actual
position parameter derivative at every sufficiently close distinct central time, and
only finitely many noninjective times on compact parts of the same graph domain.
-/

open Set Filter Matrix Module
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Geometry

variable {W V U ι : Type*}
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [Fintype ι] [DecidableEq ι]

/-- For a differentiable phase, nonsingularity of its position-variation matrix is
exactly injectivity of the actual position derivative, in any matching finite bases. -/
theorem position_variation_matrix_det_ne_zero_iff
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) {f : W → V × U} {w₀ : W}
    (hf : DifferentiableAt ℝ f w₀) :
    (vectorFamilyMatrix bV (fun j ↦ (fderiv ℝ f w₀ (bW j)).1)).det ≠ 0 ↔
      Function.Injective (fderiv ℝ (fun w ↦ (f w).1) w₀) := by
  rw [hf.hasFDerivAt.fst.fderiv]
  exact vectorFamilyMatrix_det_ne_zero_iff_injective bW bV
    ((ContinuousLinearMap.fst ℝ V U).comp (fderiv ℝ f w₀))

/-- A nonsingular actual phase-position matrix implies an injective position derivative.
No separate differentiability assumption is needed: otherwise its phase differential is
zero and its injective position block forces the parameter space to be trivial. -/
theorem position_fderiv_injective_of_matrix_det_ne_zero
    (bW : Basis ι ℝ W) (bV : Basis ι ℝ V) {f : W → V × U} {w₀ : W}
    (hdet : (vectorFamilyMatrix bV (fun j ↦ (fderiv ℝ f w₀ (bW j)).1)).det ≠ 0) :
    Function.Injective (fderiv ℝ (fun w ↦ (f w).1) w₀) := by
  by_cases hf : DifferentiableAt ℝ f w₀
  · exact (position_variation_matrix_det_ne_zero_iff bW bV hf).mp hdet
  · have hinj := (vectorFamilyMatrix_det_ne_zero_iff_injective bW bV
      ((ContinuousLinearMap.fst ℝ V U).comp (fderiv ℝ f w₀))).mp hdet
    intro x y _
    apply hinj
    simp only [fderiv_zero_of_not_differentiableAt hf, ContinuousLinearMap.comp_zero,
      _root_.zero_apply]

variable {bW : Basis ι ℝ W} {bV : Basis ι ℝ V}
  {Ψ : W × ℝ → V × (V →L[ℝ] ℝ)} {D : Set (W × ℝ)} {w₀ : W}

/-- The actual central position parameter derivative is injective at all sufficiently
close distinct times. The output no longer depends on a chosen matrix representation. -/
theorem HasGraphFocalExpansion.eventually_injective_position_fderiv
    (h : HasGraphFocalExpansion bW bV Ψ D w₀) {t : ℝ} (ht : (w₀, t) ∈ D) :
    ∀ᶠ s in 𝓝[≠] t,
      Function.Injective (fderiv ℝ (fun w ↦ (Ψ (w, s)).1) w₀) := by
  filter_upwards [h.eventually_det_ne_zero ht] with s hs
  exact position_fderiv_injective_of_matrix_det_ne_zero bW bV hs

/-- In a compact part of the same central graph domain, the actual position parameter
map has only finitely many times with a noninjective differential. -/
theorem HasGraphFocalExpansion.finite_noninjective_position_times
    (h : HasGraphFocalExpansion bW bV Ψ D w₀) {K : Set ℝ}
    (hK : IsCompact K) (hKD : K ⊆ {t | (w₀, t) ∈ D}) :
    {t ∈ K | ¬Function.Injective (fderiv ℝ (fun w ↦ (Ψ (w, t)).1) w₀)}.Finite := by
  apply (h.finite_singular_times hK hKD).subset
  intro t ht
  refine ⟨ht.1, ?_⟩
  by_contra hdet
  exact ht.2 (position_fderiv_injective_of_matrix_det_ne_zero bW bV hdet)

end OTSelector.Geometry
