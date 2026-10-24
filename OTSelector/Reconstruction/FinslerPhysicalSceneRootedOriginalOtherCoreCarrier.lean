import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedMacroCarrier

/-! Original bad-window retained edges belong to other compact original macro cores. -/
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

/-- The other original retained macro labels in the SAME original seed frame. -/
def originalRetainedOtherMacroCarrier (j : ℕ) (i : Fin D.haar.continuous.count) :
    Set (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) :=
  ⋃ k : Fin D.haar.continuous.count,
    if (D.haar.continuous.coefficient k).seedIndex = j ∧ k ≠ i then
      physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
        (D.haar.continuous.coefficient k).roots
    else ∅

/-- The complementary original macro carrier is a finite union of compact
label images, all expressed in the SAME fixed original frame. -/
theorem isCompact_originalRetainedOtherMacroCarrier
    (j : ℕ) (i : Fin D.haar.continuous.count) :
    IsCompact (D.originalRetainedOtherMacroCarrier j i) := by
  apply isCompact_iUnion
  intro k
  by_cases hs : (D.haar.continuous.coefficient k).seedIndex = j ∧ k ≠ i
  · rw [ite_eq_left hs]
    have hlabel : ContinuousOn (populationSeedRootLabelValue (P j).seed a)
        (D.haar.continuous.coefficient k).roots := by
      rw [← hs.1, ← D.haar.intensity_roots k]
      exact (D.haar.intensity k).continuous_label
    exact (D.haar.continuous.coefficient k).roots_compact.image_of_continuousOn
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.continuous.comp_continuousOn hlabel)
  · rw [ite_eq_right hs]
    exact isCompact_empty

/-- Original labels remain injective on one actual seed piece. Hence selected
core labels and the union of other same-seed core labels are disjoint. -/
theorem disjoint_originalMacroLabel_otherCarrier
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) (i : Fin D.haar.continuous.count)
    (hi : (D.haar.continuous.coefficient i).seedIndex = j) :
    Disjoint (physicalSceneOriginalMacroLabel (P := P) (a := a) j ''
      (D.haar.continuous.coefficient i).roots) (D.originalRetainedOtherMacroCarrier j i) := by
  apply Set.disjoint_left.mpr
  intro w hw hother
  obtain ⟨z, hz, rfl⟩ := hw
  obtain ⟨k, hk⟩ := mem_iUnion.mp hother
  by_cases hs : (D.haar.continuous.coefficient k).seedIndex = j ∧ k ≠ i
  · rw [ite_eq_left hs] at hk
    obtain ⟨z', hz', heq⟩ := hk
    have hzpiece : z ∈ populationSeedRootPiece P a κ lambda j := by
      rw [← hi]
      exact (D.haar.continuous.coefficient i).roots_subset_piece hz
    have hzpiece' : z' ∈ populationSeedRootPiece P a κ lambda j := by
      rw [← hs.1]
      exact (D.haar.continuous.coefficient k).roots_subset_piece hz'
    have hlabels : populationSeedRootLabelValue (P j).seed a z' =
        populationSeedRootLabelValue (P j).seed a z :=
      (Module.finBasis ℝ (P j).seed.covector.ker).equivFun.injective heq
    have heqz := fixed_seed_rootLabel_injOn hF hcomplete hu ha hinj j hzpiece' hzpiece hlabels
    exact Set.disjoint_left.mp (D.haar.continuous.disjoint hs.2) hz' (heqz.symm ▸ hz)
  · rw [ite_eq_right hs] at hk
    exact hk

/-- A literal retained near edge whose original clock pair is outside the
selected core's closed pair window necessarily belongs to another original core. -/
theorem original_retainedNear_badClock_source_mem_otherMacroCarrier
    (j : ℕ) (i : Fin D.haar.continuous.count) (A B : Set M) (nearRadius : ℝ)
    {e : M × M}
    (he : e ∈ D.retainedNearCarrierEvent A B nearRadius ∩
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ))
    (hclock : (u e.1, u e.2) ∉ (D.haar.continuous.coefficient i).window.region) :
    physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1 ∈
      D.originalRetainedOtherMacroCarrier j i := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp he.1.1
  have hseed : (D.haar.continuous.coefficient k).seedIndex = j := by
    by_contra hneq
    exact Set.disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ lambda hneq)
      ((D.haar.continuous.coefficient k).roots_subset_piece hk.1) he.2.1
  have hki : k ≠ i := by
    intro h
    subst k
    exact hclock hk.2.2.1
  apply Set.mem_iUnion.mpr ⟨k, ?_⟩
  rw [ite_eq_left ⟨hseed, hki⟩]
  exact ⟨a e.1, hk.1, rfl⟩

/-- The actual source-restricted original plan carries this conditional other-core
relation before any rooting or weak limit is introduced. -/
theorem ae_original_retainedNear_badClock_source_mem_otherMacroCarrier
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (j : ℕ) (i : Fin D.haar.continuous.count) (Γ : Measure (M × M))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B) (nearRadius : ℝ) :
    ∀ᵐ e ∂(Γ.restrict (D.retainedNearCarrierEvent A B nearRadius)).restrict
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ univ),
      (u e.1, u e.2) ∉ (D.haar.continuous.coefficient i).window.region →
        physicalSceneOriginalSeedBasisPosition (P := P) (a := a) j e.1 ∈
          D.originalRetainedOtherMacroCarrier j i := by
  have hnear := D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius
  have hH : MeasurableSet
      (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := lambda) j ×ˢ
        (univ : Set M)) :=
    (measurableSet_physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) hF hcomplete hu ha hinj j).prod MeasurableSet.univ
  rw [Measure.restrict_restrict hH, inter_comm]
  filter_upwards [ae_restrict_mem (hnear.inter hH)] with e he hclock
  exact D.original_retainedNear_badClock_source_mem_otherMacroCarrier j i A B nearRadius he hclock
end PopulationLocalPressureCore
end OTSelector.Reconstruction
