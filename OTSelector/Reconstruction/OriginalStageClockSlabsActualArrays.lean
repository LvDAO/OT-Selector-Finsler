import OTSelector.Reconstruction.OriginalStageClockSlabsSupport
import OTSelector.Reconstruction.OriginalStagePortAtomArrays
import OTSelector.Reconstruction.OriginalStageResidualDensityOriginalReserveLaw

/-! One original scene/reserve event validates every actual atom-array stage label. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal NNReal ContDiff Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- On one actual scene event, every finite endpoint representation of every original edge
restriction keeps the true original source or target clock support. The selected restriction
and its atoms are quantified after the scene, so adaptive port sets require no extra law. -/
theorem LegalWeightedStationaryPoissonMatching.ae_all_originalRestrictedEndpointArrays_clock_support
    {q : ℕ} {μ ν : Measure ℝ}
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q μ ν kin g) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene q)),
      ∀ (B : Set (LegalMarkedPhysicalEdge q)) (n : ℕ) (points : Fin n → LegalMarkedPhysicalPoint q),
      (((scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict B).fst =
        ∑ i, Measure.dirac (points i) → ∀ i, (points i).2 ∈ μ.support) ∧
      (((scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict B).snd =
        ∑ i, Measure.dirac (points i) → ∀ i, (points i).2 ∈ ν.support) := by
  filter_upwards [Q.ae_ae_originalEdges_clock_support] with scene hs
  intro B n points
  have hedge : ∀ᵐ e ∂(scene.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict B,
      e.1.2 ∈ μ.support ∧ e.2.2 ∈ ν.support := ae_restrict_of_ae hs
  constructor
  · intro heq
    apply originalFiniteAtoms_forall_of_ae points (P := fun p ↦ p.2 ∈ μ.support)
    rw [← heq]
    apply (ae_map_iff measurable_fst.aemeasurable
      (μ.isClosed_support.measurableSet.preimage measurable_snd)).mpr
    exact hedge.mono (fun _ h ↦ h.1)
  · intro heq
    apply originalFiniteAtoms_forall_of_ae points (P := fun p ↦ p.2 ∈ ν.support)
    rw [← heq]
    apply (ae_map_iff measurable_snd.aemeasurable
      (ν.isClosed_support.measurableSet.preimage measurable_snd)).mpr
    exact hedge.mono (fun _ h ↦ h.2)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- Every unchanged original reserve mark lies in its true clock support on one event,
including all indices which marks-only excess deletion may keep later. -/
theorem ae_all_originalReserveCloud_clock_support (rate : ℝ≥0) :
    letI : IsProbabilityMeasure μ := D.support.source.probability
    letI : IsProbabilityMeasure ν := D.support.target.probability
    ∀ᵐ reserves ∂twoMarkedCloudLaw (finrank ℝ S.covector.ker) ℝ ℝ μ ν rate,
      (∀ i : ℕ, (reserves.1.2 i).2 ∈ μ.support) ∧
      (∀ i : ℕ, (reserves.2.2 i).2 ∈ ν.support) := by
  let : IsProbabilityMeasure μ := D.support.source.probability
  let : IsProbabilityMeasure ν := D.support.target.probability
  have hp : ∀ᵐ p ∂μ.prod ν, p.1 ∈ μ.support ∧ p.2 ∈ ν.support :=
    (ae_fst_of_ae μ.support_mem_ae).and (ae_snd_of_ae ν.support_mem_ae)
  filter_upwards [ae_all_mMarkPair (finrank ℝ S.covector.ker) μ ν rate
    (P := fun a b ↦ a ∈ μ.support ∧ b ∈ ν.support) hp] with reserves hr
  exact ⟨fun i ↦ (hr i 0).1, fun i ↦ (hr 0 i).2⟩

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
