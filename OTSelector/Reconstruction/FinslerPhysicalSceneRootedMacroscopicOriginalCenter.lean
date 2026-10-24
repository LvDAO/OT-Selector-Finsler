import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylorPackingCertificate

/-!
# Original macroscopic coefficients and the internally selected Taylor center

The original macro root and the auxiliary Taylor center may differ. Their
actual relative coefficient bound controls the difference of all four model
edge costs, preserving a strict cycle at the original macro coefficient.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- The original macro coefficient and certificate-selected coefficient differ
by at most the original relative cover error on every bounded legal model edge. -/
theorem ActualMacroscopicTaylorCertificate.frozenCost_sub_original_macro_le
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {T : C.TaylorRootCover ε} {K : Set (ℚ → M)} {macroCenter : ℚ → M}
    (A : C.ActualMacroscopicTaylorCertificate T K macroCenter)
    (hε : 0 ≤ ε) (hmacro : macroCenter ∈ C.roots)
    {B R : ℝ}
    (hbound : ∀ z ∈ C.roots, ∀ p ∈ C.window.region,
      ∀ v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
      ‖v‖ ≤ 2 * |R| →
      0 ≤ matrixQuadratic (C.matrix z p) v ∧ matrixQuadratic (C.matrix z p) v ≤ B)
    (x y : (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ)
    (hx : ‖x.1‖ ≤ R) (hy : ‖y.1‖ ≤ R) (hclock : (x.2, y.2) ∈ C.window.region) :
    |C.frozenQuadraticCost A.frozenCenter x y - C.frozenQuadraticCost macroCenter x y| ≤ ε * B := by
  have hrel := T.relative A.frozenCenter A.frozenCenter_mem
    macroCenter ⟨hmacro, A.macroCenter_mem_neighborhood⟩ (x.2, y.2) hclock (y.1 - x.1)
  have hv : ‖y.1 - x.1‖ ≤ 2 * |R| :=
    (norm_sub_le _ _).trans (by nlinarith [le_abs_self R])
  have hb := (hbound A.frozenCenter (T.subset A.frozenCenter_mem)
    (x.2, y.2) hclock (y.1 - x.1) hv).2
  rw [abs_sub_comm]
  exact hrel.trans (mul_le_mul_of_nonneg_left hb hε)

/-- A strict cycle for the original macro coefficient survives the internally
selected Taylor reference. The same four actual clock pairs are retained. -/
theorem ActualMacroscopicTaylorCertificate.strict_cycle_of_original_macro
    {C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ} {ε : ℝ}
    {T : C.TaylorRootCover ε} {K : Set (ℚ → M)} {macroCenter : ℚ → M}
    (A : C.ActualMacroscopicTaylorCertificate T K macroCenter)
    (hε : 0 ≤ ε) (hmacro : macroCenter ∈ C.roots)
    {B R γ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ z ∈ C.roots, ∀ p ∈ C.window.region,
      ∀ v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ,
      ‖v‖ ≤ 2 * |R| →
      0 ≤ matrixQuadratic (C.matrix z p) v ∧ matrixQuadratic (C.matrix z p) v ≤ B)
    (hbudget : 2 * ε * (4 * B) ≤ γ / 2)
    (ξ η : Fin 2 → ((Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) × ℝ))
    (hξ : ∀ i, ‖(ξ i).1‖ ≤ R) (hη : ∀ i, ‖(η i).1‖ ≤ R)
    (hclock : ∀ i j, ((ξ i).2, (η j).2) ∈ C.window.region)
    (hcycle : 2 * γ < C.frozenQuadraticCost macroCenter (ξ 0) (η 0) +
      C.frozenQuadraticCost macroCenter (ξ 1) (η 1) -
      C.frozenQuadraticCost macroCenter (ξ 0) (η 1) -
      C.frozenQuadraticCost macroCenter (ξ 1) (η 0)) :
    γ < C.frozenQuadraticCost A.frozenCenter (ξ 0) (η 0) +
      C.frozenQuadraticCost A.frozenCenter (ξ 1) (η 1) -
      C.frozenQuadraticCost A.frozenCenter (ξ 0) (η 1) -
      C.frozenQuadraticCost A.frozenCenter (ξ 1) (η 0) := by
  have hedge (i j : Fin 2) := A.frozenCost_sub_original_macro_le hε hmacro hbound
    (ξ i) (η j) (hξ i) (hη j) (hclock i j)
  obtain ⟨h00l, h00u⟩ := abs_le.mp (hedge 0 0)
  obtain ⟨h11l, h11u⟩ := abs_le.mp (hedge 1 1)
  obtain ⟨h01l, h01u⟩ := abs_le.mp (hedge 0 1)
  obtain ⟨h10l, h10u⟩ := abs_le.mp (hedge 1 0)
  nlinarith

end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
