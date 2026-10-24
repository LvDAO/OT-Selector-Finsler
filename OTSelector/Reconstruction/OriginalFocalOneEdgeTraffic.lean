import OTSelector.Reconstruction.OriginalFocalPhysicalVelocityCone
import OTSelector.Analysis.Calculus.ConeCurveNonnegativeIntegral
import OTSelector.Reconstruction.OriginalNormalizedCompletePath

/-!
# The actual Finsler one-edge physical traffic bound

Both original focal endpoints supply uniform relative windows on which each
unchanged complete path has bounded physical traffic. Arbitrary pointwise
restrictions are retained in the literal nonnegative edge readout. The min-one
version includes zero momentum and diagonal or clipped clock intervals.
-/

open Set Filter Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- A true original physical cone controls its literal nonnegative per-edge contribution. -/
theorem original_oneEdgeTraffic_le_min_one_of_physicalCone
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (x : Fin (finrank ℝ S.covector.ker) → ℝ)
    (m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))
    (ha : m.1.1 - S.level ∈ Ioo D.lo D.hi)
    {l r R M : ℝ} (hlr : l ≤ r) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hclock : ∀ c ∈ Icc l r, c - S.level ∈ Ioo D.lo D.hi)
    {v : Fin (finrank ℝ S.covector.ker) → ℝ}
    (hcone : ∀ c ∈ Icc l r,
      ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m - v‖ ≤ ‖v‖ / 4)
    {f : ℝ → ℝ≥0∞}
    (hf : ∀ c ∈ Icc l r, f c ≤ ENNReal.ofReal
      (M * ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m‖))
    (hfR : ∀ c ∈ Icc l r, R < ‖originalSeedCompletePath S w x m c‖ → f c = 0) :
    (∫⁻ c in Icc l r, f c) ≤ ENNReal.ofReal
      ((4 * M * (R + 1)) * min 1 ((r - l) * ‖v‖)) :=
  coneCurve_lintegral_le_min_one hlr
    (fun c hc ↦ D.hasDerivAt_originalSeedCompletePath hF hw x m ha (hclock c hc))
    hcone hR hM hf hfR

/-- The actual original left endpoint internally produces the complete physical estimate. -/
theorem exists_original_left_focal_oneEdgeTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ η : ℝ, η > 0 ∧ η < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) η, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |c - S.level - D.lo - a| ≤ σ * a) →
      ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      m.1.1 - S.level ∈ Ioo D.lo D.hi →
      ∀ R M : ℝ, 0 ≤ R → 0 ≤ M → ∀ f : ℝ → ℝ≥0∞,
      (∀ c ∈ Icc l r, f c ≤ ENNReal.ofReal
        (M * ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m‖)) →
      (∀ c ∈ Icc l r, R < ‖originalSeedCompletePath S w x m c‖ → f c = 0) →
      (∫⁻ c in Icc l r, f c) ≤ ENNReal.ofReal
        ((4 * M * (R + 1)) * min 1
          ((r - l) * ‖originalSeedKernel S w (D.lo + a) *ᵥ originalSeedPairMomentum S w m‖)) := by
  obtain ⟨η,hη,hηspan,σ,hσ,hσhalf,hcone⟩ :=
    D.exists_original_left_focal_physicalVelocityCone hF hw
  refine ⟨η / 2,half_pos hη,by linarith,σ,hσ,hσhalf,?_⟩
  intro a ha l r hlr hband x m hm R M hR hM f hf hfR
  have haη : a ∈ Ioo (0 : ℝ) η := ⟨ha.1,by linarith [ha.2]⟩
  have hclock : ∀ c ∈ Icc l r, c - S.level ∈ Ioo D.lo D.hi := by
    intro c hc
    have h := abs_le.mp (hband c hc)
    constructor <;> nlinarith [h.1,h.2,ha.1,ha.2]
  apply D.original_oneEdgeTraffic_le_min_one_of_physicalCone hF hw x m hm hlr hR hM
    hclock ?_ hf hfR
  intro c hc
  have hh := hcone a haη (c - S.level - D.lo) (hband c hc) (originalSeedPairMomentum S w m)
  simpa only [add_sub_cancel] using hh

/-- The actual right endpoint has the same physical bound in its inward clock. -/
theorem exists_original_right_focal_oneEdgeTraffic
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ∃ η : ℝ, η > 0 ∧ η < D.hi - D.lo ∧ ∃ σ : ℝ, σ > 0 ∧ σ ≤ 1 / 2 ∧
      ∀ a ∈ Ioo (0 : ℝ) η, ∀ l r : ℝ, l ≤ r →
      (∀ c ∈ Icc l r, |D.hi - (c - S.level) - a| ≤ σ * a) →
      ∀ x : Fin (finrank ℝ S.covector.ker) → ℝ,
      ∀ m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)),
      m.1.1 - S.level ∈ Ioo D.lo D.hi →
      ∀ R M : ℝ, 0 ≤ R → 0 ≤ M → ∀ f : ℝ → ℝ≥0∞,
      (∀ c ∈ Icc l r, f c ≤ ENNReal.ofReal
        (M * ‖originalSeedKernel S w (c - S.level) *ᵥ originalSeedPairMomentum S w m‖)) →
      (∀ c ∈ Icc l r, R < ‖originalSeedCompletePath S w x m c‖ → f c = 0) →
      (∫⁻ c in Icc l r, f c) ≤ ENNReal.ofReal
        ((4 * M * (R + 1)) * min 1
          ((r - l) * ‖originalSeedKernel S w (D.hi - a) *ᵥ originalSeedPairMomentum S w m‖)) := by
  obtain ⟨η,hη,hηspan,σ,hσ,hσhalf,hcone⟩ :=
    D.exists_original_right_focal_physicalVelocityCone hF hw
  refine ⟨η / 2,half_pos hη,by linarith,σ,hσ,hσhalf,?_⟩
  intro a ha l r hlr hband x m hm R M hR hM f hf hfR
  have haη : a ∈ Ioo (0 : ℝ) η := ⟨ha.1,by linarith [ha.2]⟩
  have hclock : ∀ c ∈ Icc l r, c - S.level ∈ Ioo D.lo D.hi := by
    intro c hc
    have h := abs_le.mp (hband c hc)
    constructor <;> nlinarith [h.1,h.2,ha.1,ha.2]
  apply D.original_oneEdgeTraffic_le_min_one_of_physicalCone hF hw x m hm hlr hR hM
    hclock ?_ hf hfR
  intro c hc
  have hh := hcone a haη (D.hi - (c - S.level)) (hband c hc) (originalSeedPairMomentum S w m)
  simpa only [sub_sub_cancel] using hh

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
