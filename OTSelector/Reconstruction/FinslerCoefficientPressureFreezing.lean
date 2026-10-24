import OTSelector.Reconstruction.FinslerFiniteCoefficientCores
import OTSelector.LinearAlgebra.Matrix.CompactPositiveQuadratic
import OTSelector.Reconstruction.RelativeExpectedPressure

/-!
# Actual compact Finsler coefficients control finite pressure freezing

The original coefficient core produces finite open root neighborhoods and one
original reference coefficient on each neighborhood. Their relative quadratic
bounds control the actual assignment pressure for every displacement array.
-/

open Set Matrix MeasureTheory Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] {δ : ℝ≥0∞}

namespace OriginalPopulationCoefficientCore

variable (C : OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ)

/-- The literal original inverse compliance, in the original seed's fixed basis. -/
def matrix (z : Z) (p : ℝ × ℝ) :
    Matrix (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))
      (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) ℝ :=
  populationSeedRootCoefficient (P C.seedIndex).seed a
    (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (z, p)

omit [BorelSpace E] in
/-- One original coefficient core has a uniform quadratic lower bound, produced
from its actual positive coefficient field. -/
theorem exists_quadratic_lower_bound :
    ∃ m > 0, ∀ z ∈ C.roots, ∀ p ∈ C.window.region, ∀ v,
      m * ‖v‖ ^ 2 ≤ matrixQuadratic (C.matrix z p) v := by
  obtain ⟨m, hm, hbound⟩ := exists_uniform_matrixQuadratic_lower_bound
    (C.roots_compact.prod C.window.isCompact_region) C.coefficient_continuous
    (fun q hq ↦ C.coefficient_posDef q.1 hq.1 q.2 hq.2)
  exact ⟨m, hm, fun z hz p hp ↦ hbound (z, p) ⟨hz, hp⟩⟩

/-- Finite original root references and their open neighborhoods, retaining the
whole original scalar pair region and all displacement directions. -/
structure RelativeRootCover (ε : ℝ) where
  lowerBound : ℝ
  lowerBound_pos : 0 < lowerBound
  quadratic_lower_bound : ∀ z ∈ C.roots, ∀ p ∈ C.window.region, ∀ v,
    lowerBound * ‖v‖ ^ 2 ≤ matrixQuadratic (C.matrix z p) v
  centers : Set Z
  finite : centers.Finite
  subset : centers ⊆ C.roots
  neighborhood : Z → Set Z
  covers : C.roots ⊆ ⋃ z ∈ centers, neighborhood z
  open_neighborhood : ∀ z ∈ centers, IsOpen (neighborhood z)
  center_mem : ∀ z ∈ centers, z ∈ neighborhood z
  relative : ∀ z₀ ∈ centers, ∀ z ∈ C.roots ∩ neighborhood z₀,
    ∀ p ∈ C.window.region, ∀ v,
      |matrixQuadratic (C.matrix z p) v - matrixQuadratic (C.matrix z₀ p) v| ≤
        ε * matrixQuadratic (C.matrix z₀ p) v

omit [BorelSpace E] in
/-- Actual compact continuity and positivity construct the relative root cover;
no coercivity or freezing estimate is supplied as a hypothesis. -/
theorem exists_relativeRootCover [TopologicalSpace.MetrizableSpace Z]
    {ε : ℝ} (hε : 0 < ε) : Nonempty (C.RelativeRootCover ε) := by
  obtain ⟨m, hm, hbound⟩ := C.exists_quadratic_lower_bound
  obtain ⟨centers, U, hfinite, hsub, hcover, hrelative⟩ :=
    exists_finite_relative_matrixQuadratic_cover C.roots_compact C.window.isCompact_region
      C.coefficient_continuous C.coefficient_posDef hε
  exact ⟨{
    lowerBound := m
    lowerBound_pos := hm
    quadratic_lower_bound := hbound
    centers := centers
    finite := hfinite
    subset := hsub
    neighborhood := U
    covers := hcover
    open_neighborhood := fun z hz ↦ (hrelative z hz).1
    center_mem := fun z hz ↦ (hrelative z hz).2.1
    relative := fun z hz ↦ (hrelative z hz).2.2 }⟩

namespace RelativeRootCover

variable {C} {ε : ℝ} (D : C.RelativeRootCover ε)

omit [BorelSpace E] in
/-- Freezing one actual root coefficient controls the actual finite normalized
assignment pressure, retaining every scalar pair and arbitrary displacement array. -/
theorem assignment_pressure_comparison {N : ℕ} (hN : 0 < N)
    {z₀ : Z} (hz₀ : z₀ ∈ D.centers)
    (z : Fin N → Fin N → Z) (p : Fin N → Fin N → ℝ × ℝ)
    (v : Fin N → Fin N → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (hz : ∀ i j, z i j ∈ C.roots ∩ D.neighborhood z₀)
    (hp : ∀ i j, p i j ∈ C.window.region)
    (g h : Matrix (Fin N) (Fin N) ℝ) (t G B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hh : ∀ i j, |h i j| ≤ G) (hgh : ∀ i j, |g i j - h i j| ≤ B) :
    let c := fun i j ↦ matrixQuadratic (C.matrix (z i j) (p i j)) (v i j)
    let d := fun i j ↦ matrixQuadratic (C.matrix z₀ (p i j)) (v i j)
    |perturbedAssignmentValue c g t / N - perturbedAssignmentValue d h t / N| ≤
      ε * (perturbedAssignmentValue d h t / N + |t| * G) + |t| * B := by
  exact perturbedAssignmentValue_div_abs_sub_le_relative hN _ g _ h t ε G B hε0 hε1
    (fun i j ↦ D.relative z₀ hz₀ (z i j) (hz i j) (p i j) (hp i j) (v i j)) hh hgh

omit [BorelSpace E] in
/-- The true distance-cost remainder and coefficient freezing combine relatively,
using the lower bound produced from this same actual coefficient core. -/
theorem relative_cost_of_quadratic_remainder (hε : 0 ≤ ε)
    {z₀ z : Z} (hz₀ : z₀ ∈ D.centers) (hz : z ∈ C.roots ∩ D.neighborhood z₀)
    {p : ℝ × ℝ} (hp : p ∈ C.window.region)
    (v : Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ) {cost : ℝ}
    (hcost : |cost - matrixQuadratic (C.matrix z p) v| ≤
      ε * D.lowerBound * ‖v‖ ^ 2) :
    |cost - matrixQuadratic (C.matrix z₀ p) v| ≤
      (2 * ε) * matrixQuadratic (C.matrix z₀ p) v := by
  have hlow := mul_le_mul_of_nonneg_left
    (D.quadratic_lower_bound z₀ (D.subset hz₀) p hp v) hε
  have hfreeze := D.relative z₀ hz₀ z hz p hp v
  have htriangle := abs_sub_le cost (matrixQuadratic (C.matrix z p) v)
    (matrixQuadratic (C.matrix z₀ p) v)
  nlinarith only [hcost, hlow, hfreeze, htriangle]

omit [BorelSpace E] in
/-- The actual distance-cost array is compared to its frozen original quadratic
pressure. The Taylor remainder is the only cost-specific input. -/
theorem distance_assignment_pressure_comparison {N : ℕ} (hN : 0 < N)
    {z₀ : Z} (hz₀ : z₀ ∈ D.centers)
    (z : Fin N → Fin N → Z) (p : Fin N → Fin N → ℝ × ℝ)
    (v : Fin N → Fin N → Fin (finrank ℝ (P C.seedIndex).seed.covector.ker) → ℝ)
    (hz : ∀ i j, z i j ∈ C.roots ∩ D.neighborhood z₀)
    (hp : ∀ i j, p i j ∈ C.window.region)
    (c g h : Matrix (Fin N) (Fin N) ℝ) (t G B : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : 2 * ε ≤ 1)
    (hcost : ∀ i j, |c i j - matrixQuadratic (C.matrix (z i j) (p i j)) (v i j)| ≤
      ε * D.lowerBound * ‖v i j‖ ^ 2)
    (hh : ∀ i j, |h i j| ≤ G) (hgh : ∀ i j, |g i j - h i j| ≤ B) :
    let d := fun i j ↦ matrixQuadratic (C.matrix z₀ (p i j)) (v i j)
    |perturbedAssignmentValue c g t / N - perturbedAssignmentValue d h t / N| ≤
      (2 * ε) * (perturbedAssignmentValue d h t / N + |t| * G) + |t| * B := by
  exact perturbedAssignmentValue_div_abs_sub_le_relative hN c g _ h t (2 * ε) G B
    (mul_nonneg (by norm_num) hε0) hε1
    (fun i j ↦ D.relative_cost_of_quadratic_remainder hε0 hz₀ (hz i j) (hp i j)
      (v i j) (hcost i j)) hh hgh

end RelativeRootCover
end OriginalPopulationCoefficientCore
end OTSelector.Reconstruction
