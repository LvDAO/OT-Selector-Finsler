import OTSelector.Geometry.FinslerQuadraticCoefficients

/-!
# Actual calibrated tube data

A calibrated tube records the supplied smooth coordinates and geometric data for
one central curve segment. Its quadratic coefficient is the actual integrated
restricted-length response. Global metric and potential assumptions remain inputs
to the theorems consuming these data.
-/

open Set Manifold Bundle
open scoped Topology ContDiff

noncomputable section
namespace OTSelector.Geometry.ContinuousFinslerNorm

variable {E W M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M]

/-- A supplied smooth unit-speed tube and its actual calibrated central segment.
The data specify the geometry and the original potential, without assuming any
Taylor expansion or quadratic-coefficient identification. -/
structure CalibratedTube (F : ContinuousFinslerNorm E M)
    (Λ : W → ℝ → M) (a b : ℝ) (u : M → ℝ) where
  toOpenPartialHomeomorph : OpenPartialHomeomorph (ℝ × W) M
  smooth : ContMDiffOn 𝓘(ℝ, ℝ × W) 𝓘(ℝ, E) ∞
    toOpenPartialHomeomorph toOpenPartialHomeomorph.source
  smooth_symm : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ × W) ∞
    toOpenPartialHomeomorph.symm toOpenPartialHomeomorph.target
  coe_eq : (toOpenPartialHomeomorph : ℝ × W → M) = fun q ↦ Λ q.2 q.1
  energy_eq : ∀ q ∈ toOpenPartialHomeomorph.source,
    F.energy (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (Λ q.2) ⟨q.1, (1 : ℝ)⟩) = 1 / 2
  timeOrigin : ℝ
  covector_le : ∀ y ∈ toOpenPartialHomeomorph.target,
    ∀ z : TangentSpace 𝓘(ℝ, E) y,
      @LE.le ℝ _ (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, ℝ)
        (manifoldFlowTimePotential toOpenPartialHomeomorph 1 timeOrigin) y z)
        (F.toFun ⟨y, z⟩ : ℝ)
  ordered : a < b
  stay : ∀ t ∈ Icc a b, (t, (0 : W)) ∈ toOpenPartialHomeomorph.source
  minimizing : letI : ∀ x : M, ENorm (TangentSpace 𝓘(ℝ, E) x) := F.enorm
    F.lengthEDist (Λ 0 a) (Λ 0 b) = Manifold.pathELength 𝓘(ℝ, E) (Λ 0) a b
  saturation : letI : MetricSpace M := F.metricSpace
    u (Λ 0 b) - u (Λ 0 a) = dist (Λ 0 a) (Λ 0 b)
  differentiable : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) u (Λ 0 a)

namespace CalibratedTube

variable {F : ContinuousFinslerNorm E M} {Λ : W → ℝ → M} {a b : ℝ} {u : M → ℝ}

/-- The actual integrated restricted-length coefficient on the central curve of
the supplied calibrated tube. -/
def quadratic (D : F.CalibratedTube Λ a b u) (w : W × W) : ℝ :=
  F.tubeLengthQuadratic D.toOpenPartialHomeomorph (Λ 0) a b w

/-- The actual coefficient of the supplied tube is quadratic in the label increments. -/
theorem quadratic_smul (D : F.CalibratedTube Λ a b u) (s : ℝ) (w : W × W) :
    D.quadratic (s • w) = s ^ 2 * D.quadratic w :=
  F.tubeLengthQuadratic_smul D.toOpenPartialHomeomorph (Λ 0) a b s w

end CalibratedTube
end OTSelector.Geometry.ContinuousFinslerNorm
