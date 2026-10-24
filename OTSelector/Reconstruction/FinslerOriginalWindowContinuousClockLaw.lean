import OTSelector.Reconstruction.FinslerOriginalRetainedClockLaw
import OTSelector.Transport.EmpiricalSelector.CompactSupport

/-! The original conditional clock coupling itself produces the retained
continuous clock law used by the physical pressure comparison. Its class law
and full retained mass are exact original quantities. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker}
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {r : ℝ} {δ loss : ℝ≥0∞}

/-- The original reference conditional clock coupling gives one actual
continuous law on the original scalar range. Its retained mass is at least
one minus the stored original window loss; its normalized finite observation
is exactly the current physical reference class law. -/
theorem PopulationLocalPressureCore.exists_original_window_continuous_clock_law
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width)
    {η : ℝ} (hη : η < 1) (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    ∃ π : Measure (range × range), IsProbabilityMeasure π ∧
      π.map (Prod.map Subtype.val Subtype.val) = γ ref.val ∧
      let C := D.haar.continuous.coefficient i
      let retained := π.restrict
        {p | C.clockClassAllowed Q (Q.rangeClassify p.1) (Q.rangeClassify p.2)}
      1 - δ.toReal ≤ retained.real univ ∧
      IsProbabilityMeasure (normalizedFiniteLaw retained) ∧
      (normalizedFiniteLaw retained).map (Prod.map Q.rangeClassify Q.rangeClassify) =
        normalizedClockClassPairMeasure (D.originalWindowReferenceWeights γ gap range i ref Q η) ∧
      (∑ j, ∑ k, D.originalWindowReferenceWeights γ gap range i ref Q η j k) =
        ((1 - η) * D.rootIntensity i ref.val) * retained.real univ := by
  let C := D.haar.continuous.coefficient i
  have href : ref.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,ref.property⟩
  have hgood := (D.haar.continuous.population.good ref.val href).1
  obtain ⟨π,⟨_hπ,hmap⟩,_⟩ := existsUnique_subtype_coupling_lift hrange hrange
    hgood.2.2.1 hgood.2.2.2 hgood.1
  haveI : IsProbabilityMeasure (π.map (Prod.map Subtype.val Subtype.val)) := by
    rw [hmap]
    infer_instance
  haveI : IsProbabilityMeasure π := Measure.isProbabilityMeasure_of_map
    (Prod.map Subtype.val Subtype.val)
  let allowed := C.clockClassAllowed Q
  let A := maskedClockFlow allowed (actualClockClassFlow (γ ref.val) Q.cell Q.cell)
  let retained := π.restrict {p | allowed (Q.rangeClassify p.1) (Q.rangeClassify p.2)}
  have hmass : (∑ j, ∑ k, A j k) = retained.real univ := by
    simpa only [hmap] using Q.masked_clock_mass_eq_original_retained_mass π allowed
  have hentry (j k : Fin Q.count) :
      D.originalWindowReferenceWeights γ gap range i ref Q η j k =
      ((1 - η) * D.rootIntensity i ref.val) * A j k := by
    dsimp only [PopulationLocalPressureCore.originalWindowReferenceWeights,A,allowed,C,maskedClockFlow]
    split_ifs <;> ring
  have htotal : (∑ j, ∑ k, D.originalWindowReferenceWeights γ gap range i ref Q η j k) =
      ((1 - η) * D.rootIntensity i ref.val) * retained.real univ := by
    simp_rw [hentry,← Finset.mul_sum]
    rw [hmass]
  have hrefI : ref.val ∈ (D.haar.intensity i).roots := by
    rw [D.haar.intensity_roots]
    exact ref.property
  have hd : 0 < D.rootIntensity i ref.val := (D.haar.intensity i).lower_pos.trans_le
    ((D.haar.intensity i).bounds _ (mem_image_of_mem _ hrefI)).1
  have hc : 0 < (1 - η) * D.rootIntensity i ref.val := mul_pos (sub_pos.mpr hη) hd
  have hweights := D.originalWindowReferenceWeights_mass γ gap range i ref Q hη hgap hδ hδ1
  have hlower : 1 - δ.toReal ≤ retained.real univ := by
    have hb := hweights.2.2.1
    rw [htotal] at hb
    exact (mul_le_mul_iff_right₀ hc).mp hb
  have hpos : 0 < retained.real univ := (sub_pos.mpr hδ1).trans_le hlower
  refine ⟨π,inferInstance,hmap,hlower,normalizedFiniteLaw_probability retained hpos,?_,htotal⟩
  symm
  have heq : D.originalWindowReferenceWeights γ gap range i ref Q η =
      fun j k ↦ ((1 - η) * D.rootIntensity i ref.val) * A j k := funext fun j ↦ funext (hentry j)
  rw [heq]
  simpa only [hmap] using Q.normalized_scaled_masked_weights_eq_original_observation π allowed hpos hc

end OTSelector.Reconstruction
