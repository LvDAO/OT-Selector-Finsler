import OTSelector.Reconstruction.OriginalCompactClockWeightedOccupation
import OTSelector.Reconstruction.OriginalCompletePathCountLtwo
import OTSelector.Reconstruction.OriginalCompletePathAbsoluteTraffic

/-! Literal original physical window traffic enters L2 from its geometric
contributor count. Its required weighted occupation moment is produced from
original kinetic energy and the compact clock window, rather than assumed. -/
open Set Function Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ} {S : CalibratedLevelSeedPatch F u}
  {w : S.covector.ker} {μ ν : Measure ℝ}

/-- The actual original masked physical traffic has its good-event L2 bound
from the actual count, bounded single-edge occupation and actual normalized
momentum comparison. All weighted-moment finiteness follows internally. -/
theorem OriginalSeedConditionalMoments.goodEvent_original_compactClock_traffic_memLp_two_of_count
    (D : OriginalSeedConditionalMoments S w μ ν)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter) {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (T : Matrix (Fin (finrank ℝ S.covector.ker)) (Fin (finrank ℝ S.covector.ker)) ℝ)
    {J : Set ℝ} (hJ : IsCompact J) (hclock : ∀ c ∈ J, c - (S.level : ℝ) ∈ Ioo D.lo D.hi)
    {η : (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} (hη : Measurable η)
    (hηI : Integrable η (volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ)))
    (mask : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ → ℝ≥0∞)
    (hmaskM : Measurable mask) (hmask : ∀ z, mask z ≤ 1)
    (hzero : ∀ m c, c ∉ J → mask (m, c) = 0)
    {A : Set (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))} (hA : MeasurableSet A)
    (V : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) →
      Set ((Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))))
    (W : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) → ℝ≥0∞) (hW : ∀ s, W s ≠ (∞ : ℝ≥0∞))
    {B K C : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hC : 0 ≤ C) :
    let d := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      originalSeedPathOffset S w z.2 z.1
    let h := fun x ↦ ENNReal.ofReal (η x)
    let f := fun z : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) × ℝ ↦
      ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
    let p := fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      ENNReal.ofReal ‖T *ᵥ originalSeedPairMomentum S w m‖
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), s ∉ A →
      (fun a : (Fin (finrank ℝ S.covector.ker) → ℝ) × PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
        ∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume).support ⊆ V s) →
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), s ∉ A →
      ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s),
        (∫⁻ r : ℝ, h (a.1 + d (a.2, r)) * f (a.2, r) ∂volume) ≤ ENNReal.ofReal B) →
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), s ∉ A →
      physicalScenePairKernel s.1 (V s) ≤ ENNReal.ofReal K * W s) →
    (∀ᵐ s ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))), s ∉ A →
      ∀ᵐ a ∂(physicalScenePairKernel s.1).restrict (V s), W s ≤ ENNReal.ofReal C * p a.2) →
    MemLp (Aᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f s).toReal)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))) ∧
      (∫ s, (Aᶜ.indicator (fun s ↦ (legalMarkedCompletePathTraffic (finrank ℝ S.covector.ker) d h f s).toReal) s) ^ 2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker)))) ≤ (B * K * C) *
        ((∫⁻ x, h x ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) *
          (∫⁻ m, ∫⁻ c : ℝ, p m * f (m, c) ∂volume ∂legalMarkedJointPalm (finrank ℝ S.covector.ker) Q.law)).toReal := by
  dsimp only
  intro hsupport huB hcount hweight
  have hmomentum : Measurable (fun m : PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      T *ᵥ originalSeedPairMomentum S w m) :=
    (Matrix.toLin' T).continuous_of_finiteDimensional.measurable.comp
      (measurable_originalSeedPairMomentum S hF hw)
  have hocc := D.lintegral_original_compactClock_maskedWeightedOccupation_lt_top
    hF hw hgap hbounds Q T hJ hclock mask hmask hzero
  have hwindow : (∫⁻ x, ENNReal.ofReal (η x)
      ∂(volume : Measure (Fin (finrank ℝ S.covector.ker) → ℝ))) < (∞ : ℝ≥0∞) :=
    (lintegral_ofReal_le_lintegral_enorm _).trans_lt hηI.2
  apply Q.goodEvent_completePath_traffic_memLp_two_of_count
    _ (measurable_originalSeedPathOffset_joint S hF hw) hη.ennreal_ofReal
    ((measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hmaskM)
    _ hmomentum.norm.ennreal_ofReal (fun _ ↦ ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top hwindow.ne hocc.ne) hA V W hW hB hK hC
    hsupport huB hcount hweight

end OTSelector.Reconstruction
