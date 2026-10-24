import OTSelector.Reconstruction.FinslerOriginalClosedWindowPairKernel

/-! Every later fine physical class model observes the same preselected
original closed-window pair law. Its original mass remains in the Haar weight. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- Exact physical class observation of one fixed original closed-window law.
The scalar-range lift is fixed BEFORE all fine bins; every full endpoint
partition gives the same normalized joint law and the exact retained mass. -/
theorem PopulationLocalPressureCore.originalClosedWindow_class_observation
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] {gap : ℝ}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    (π : Measure (range × range))
    (hmap : π.map (Prod.map Subtype.val Subtype.val) = γ ref.val)
    {width : ℝ} (Q : FiniteScalarBins range width)
    (hwindowGap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap)
    (hfull : ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed Q j k →
      ∀ x ∈ Q.cell j, ∀ y ∈ Q.cell k,
        x ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        y ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧ x < y)
    {η : ℝ} (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    let C := D.haar.continuous.coefficient i
    let χ := π.restrict ((Prod.map Subtype.val Subtype.val) ⁻¹' C.window.region)
    IsProbabilityMeasure π ∧
      χ.map (Prod.map Subtype.val Subtype.val) = (γ ref.val).restrict C.window.region ∧
      1 - δ.toReal ≤ χ.real univ ∧
      IsProbabilityMeasure (normalizedFiniteLaw χ) ∧
      (normalizedFiniteLaw χ).map (Prod.map Q.rangeClassify Q.rangeClassify) =
        normalizedClockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ref Q η) ∧
      (∑ j, ∑ k, D.originalWindowReferenceWeights γ gap range i ref Q η j k) =
        ((1 - η) * D.rootIntensity i ref.val) * χ.real univ := by
  let C := D.haar.continuous.coefficient i
  let read : range × range → ℝ × ℝ := Prod.map Subtype.val Subtype.val
  have hread : Measurable read := measurable_subtype_coe.prodMap measurable_subtype_coe
  have hemb : MeasurableEmbedding read :=
    (MeasurableEmbedding.subtype_coe hrange).prodMap (MeasurableEmbedding.subtype_coe hrange)
  obtain ⟨π',hπ',hmap',hlower,hlaw,hobserve,hmass⟩ :=
    D.exists_original_window_continuous_clock_law hrange γ gap i ref Q hη hgap hδ hδ1
  have hsame : π' = π := hemb.map_injective (hmap'.trans hmap.symm)
  subst π'
  letI : IsProbabilityMeasure π := hπ'
  have hz : ref.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,ref.property⟩
  have hgood := (D.haar.continuous.population.good ref.val hz).1
  have hreal := C.original_full_mask_restrict_eq_window Q (γ ref.val)
    (D.original_pair_range_support hrange γ gap i ref)
    (hgood.2.1.mono (fun _ h ↦ hwindowGap.trans h)) hfull
  have hraw : π.restrict {p | C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2)} =
      π.restrict (read ⁻¹' C.window.region) := by
    apply hemb.map_injective
    rw [← Q.preimage_originalClockMaskSet (C.clockClassAllowed Q),
      ← Measure.restrict_map hread (Q.measurableSet_originalClockMaskSet _),
      ← Measure.restrict_map hread C.window.isCompact_region.measurableSet,hmap]
    exact hreal
  have hreadclosed : (π.restrict (read ⁻¹' C.window.region)).map read =
      (γ ref.val).restrict C.window.region := by
    rw [← Measure.restrict_map hread C.window.isCompact_region.measurableSet,hmap]
  rw [hraw] at hlower hlaw hobserve hmass
  exact ⟨hπ',hreadclosed,hlower,hlaw,hobserve,hmass⟩

end OTSelector.Reconstruction
