import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicOriginalCoefficient

/-!
# The actual compact macro carrier of an original retained near-event union

The fixed original seed frame is kept while the auxiliary finite core changes.
Its macro carrier is the finite union of original core label images whose
original seed index equals that frame. Literal retained original source edges
belong to this compact set before any weak limit is taken.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)

/-- The finite original core label union in one fixed original seed frame.
The original seed index filters cores before their label image is taken. -/
def originalRetainedMacroCarrier (j : ℕ) :
    Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) :=
  ⋃ i : Fin D.haar.continuous.count,
    if (D.haar.continuous.coefficient i).seedIndex = j then
      physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
        (D.haar.continuous.coefficient i).roots
    else ∅

/-- All relevant original label images are compact in their common fixed frame. -/
theorem isCompact_originalRetainedMacroCarrier (j : ℕ) :
    IsCompact (D.originalRetainedMacroCarrier j) := by
  apply isCompact_iUnion
  intro i
  by_cases hs : (D.haar.continuous.coefficient i).seedIndex = j
  · rw [ite_eq_left hs]
    have hlabel : ContinuousOn (populationSeedRootLabelValue (P j).seed a)
        (D.haar.continuous.coefficient i).roots := by
      rw [← hs]
      rw [← D.haar.intensity_roots i]
      exact (D.haar.intensity i).continuous_label
    exact (D.haar.continuous.coefficient i).roots_compact.image_of_continuousOn
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.continuous.comp_continuousOn hlabel)
  · rw [ite_eq_right hs]
    exact isCompact_empty

/-- Literal retained near edges in the fixed source piece have their original
unscaled source coordinate in the actual finite compact macro label union. -/
theorem original_retainedNear_source_mem_macroCarrier
    (j : ℕ) (A B : Set M) (nearRadius : ℝ) {e : M × M}
    (he : e ∈ D.retainedNearCarrierEvent A B nearRadius ∩
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ)) :
    physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1 ∈
      D.originalRetainedMacroCarrier j := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he.1.1
  have hseed : (D.haar.continuous.coefficient i).seedIndex = j := by
    by_contra hneq
    exact Set.disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ lambda hneq)
      ((D.haar.continuous.coefficient i).roots_subset_piece hi.1) he.2.1
  apply Set.mem_iUnion.mpr ⟨i, ?_⟩
  rw [ite_eq_left hseed]
  exact ⟨a e.1, hi.1, rfl⟩

/-- The same actually restricted global measure has the original compact
source carrier almost surely, with no assumption about its target columns. -/
theorem ae_original_retainedNear_source_mem_macroCarrier
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) (Γ : Measure (M × M))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B) (nearRadius : ℝ) :
    ∀ᵐ e ∂(Γ.restrict (D.retainedNearCarrierEvent A B nearRadius)).restrict
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ),
      physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1 ∈
        D.originalRetainedMacroCarrier j := by
  have hnear := D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  have hH : MeasurableSet
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ
        (univ : Set M)) :=
    (measurableSet_physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) hF hcomplete hu ha hinj j).prod MeasurableSet.univ
  rw [Measure.restrict_restrict hH, inter_comm]
  filter_upwards [ae_restrict_mem (hnear.inter hH)] with e he
  exact D.original_retainedNear_source_mem_macroCarrier j A B nearRadius he

end PopulationLocalPressureCore
end OTSelector.Reconstruction
