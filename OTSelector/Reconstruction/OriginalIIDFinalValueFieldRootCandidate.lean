import OTSelector.Reconstruction.OriginalIIDFinalValueFieldKinetic
import OTSelector.Reconstruction.FinslerOriginalRootPressure

/-! Exact same-candidate root pressure comparison at the genuine local reverse-pressure frontier. -/
open Set Function Filter MeasureTheory ProbabilityTheory Module Manifold
open scoped ENNReal Topology ContDiff BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {b : Z × ℝ → M}

/-- The same original population seed coefficient and same original candidate value
consume precisely the focal pointwise reverse-pressure theorem. This lemma isolates that
genuine local frontier; it does not assume a final hprob, hvalue or global pressure budget. -/
theorem originalSeedRootPressure_le_same_candidate_of_focal_reverse
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (j : ℕ) {z : Z} (hz : z ∈ populationSeedRootPiece P a κ lambda j)
    (D : OriginalSeedConditionalMoments (P j).seed
      (populationSeedPieceLabel P a κ lambda j ⟨z,hz⟩)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z))
    {gap diameter : ℝ}
    (hbounds : ConditionalClockSupportBounds (condDistrib u a η₀ z) (condDistrib u a η₁ z) gap diameter)
    (f : M × M →ᵇ ℝ)
    (hreverse : ∀ Qf : LegalWeightedStationaryPoissonMatching
        (finrank ℝ (P j).seed.covector.ker) (condDistrib u a η₀ z) (condDistrib u a η₁ z)
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f z),
      ∀ t, limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure
        (finrank ℝ (P j).seed.covector.ker) id id (condDistrib u a η₀ z) (condDistrib u a η₁ z)
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f z) R t) ≤ Qf.value t)
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z)
      (originalSeedRootKinetic (P j).seed a z) (originalPhysicalRootProbe b f z)) (t : ℝ) :
    originalSeedRootPressure (P j).seed a η₀ η₁ b f z t ≤ Q.value t := by
  let w := populationSeedPieceLabel P a κ lambda j ⟨z,hz⟩
  let : IsProbabilityMeasure (condDistrib u a η₀ z) := D.support.source.probability
  let : IsProbabilityMeasure (condDistrib u a η₁ z) := D.support.target.probability
  have hcost : originalSeedRootKinetic (P j).seed a z =
      (fun x y v ↦ matrixQuadratic (originalSeedPairCoefficient (P j).seed w (x,y)) v) := by
    funext x y v
    unfold originalSeedRootKinetic
    rw [populationSeedRootCoefficient_eq_pieceCoefficient P a κ lambda hF hcomplete hu ha hinj j hz]
  have heq : ∀ᵐ m ∂legalMarkedJointPalm (finrank ℝ (P j).seed.covector.ker) Q.law,
      matrixQuadratic (originalSeedPairCoefficient (P j).seed w m.1) m.2 =
        originalSeedRootKinetic (P j).seed a z m.1.1 m.1.2 m.2 :=
    Eventually.of_forall (fun m ↦ by rw [hcost])
  let Qactual : LegalWeightedStationaryPoissonMatching (finrank ℝ (P j).seed.covector.ker)
      (condDistrib u a η₀ z) (condDistrib u a η₁ z)
      (fun x y v ↦ matrixQuadratic (originalSeedPairCoefficient (P j).seed w (x,y)) v)
      (originalPhysicalRootProbe b f z) := Q.withAEEqKinetic heq
  obtain ⟨Qf, _hlaw, hvalue⟩ := D.exists_sameLaw_originalFocalMatching_of_actual_matrix hbounds Qactual
  have hpressure : originalSeedRootPressure (P j).seed a η₀ η₁ b f z t =
      limUnder atTop (fun R : ℝ ↦ legalMarkedScalePressure
        (finrank ℝ (P j).seed.covector.ker) id id (condDistrib u a η₀ z) (condDistrib u a η₁ z)
        (D.originalFocalKinetic gap) (originalPhysicalRootProbe b f z) R t) := by
    unfold originalSeedRootPressure originalSeedRootScalePressure
    rw [hcost]
    congr 1
    funext R
    exact (D.original_focal_scalePressure_eq_actual_coefficient hbounds
      (condDistrib u a η₀ z) (condDistrib u a η₁ z)
      (Measure.AbsolutelyContinuous.refl _) (Measure.AbsolutelyContinuous.refl _)
      (originalPhysicalRootProbe b f z) R t).symm
  rw [hpressure]
  exact (hreverse Qf t).trans_eq ((hvalue t).trans (Q.withAEEqKinetic_value
    (kin' := fun x y v ↦ matrixQuadratic (originalSeedPairCoefficient (P j).seed w (x,y)) v) heq t))

end OTSelector.Reconstruction
