import OTSelector.Reconstruction.FinslerOriginalWindowContinuousClockLaw
import OTSelector.MeasureTheory.RetainedLawVariation

/-! The actual original retained-window loss gives quantitative convergence
of its unchanged continuous original conditional clock law. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
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


/-- The original window mass bound holds on every exact lift of the same
original conditional clock law. Thus one original lift may be fixed before
all subsequent windows and bins. -/
theorem PopulationLocalPressureCore.original_window_retained_mass_of_map
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (range × range))
    (hmap : π.map (Prod.map Subtype.val Subtype.val) = γ ref.val)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    1 - δ.toReal ≤ (π.restrict
      {p | (D.haar.continuous.coefficient i).clockClassAllowed Q
        (Q.rangeClassify p.1) (Q.rangeClassify p.2)}).real univ := by
  obtain ⟨π',_,hmap',hlower,_⟩ := D.exists_original_window_continuous_clock_law
    hrange γ gap i ref Q (by norm_num : (0 : ℝ) < 1) hgap hδ hδ1
  have heq : π' = π := ((MeasurableEmbedding.subtype_coe hrange).prodMap
    (MeasurableEmbedding.subtype_coe hrange)).map_injective (hmap'.trans hmap.symm)
  simpa only [heq] using hlower

/-- The current original window loss controls the normalized retained
conditional clock law, on one unchanged original probability space. -/
theorem PopulationLocalPressureCore.original_window_retained_law_variation_le
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width)
    (π : Measure (range × range)) [IsProbabilityMeasure π]
    (hmap : π.map (Prod.map Subtype.val Subtype.val) = γ ref.val)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    let retained := π.restrict
      {p | (D.haar.continuous.coefficient i).clockClassAllowed Q
        (Q.rangeClassify p.1) (Q.rangeClassify p.2)}
    ((normalizedFiniteLaw retained).toSignedMeasure - π.toSignedMeasure).totalVariation.real univ ≤
      2 * δ.toReal / (1 - δ.toReal) := by
  apply totalVariation_normalized_submeasure_le_of_mass π _ Measure.restrict_le_self
    ENNReal.toReal_nonneg hδ1
  exact D.original_window_retained_mass_of_map hrange γ gap i ref Q π hmap hgap hδ hδ1


/-- Along arbitrary actual original window/core refinements at one original
root, the normalized retained continuous laws converge in variation to the
same unchanged original conditional law. Bins and stored coefficient cores
may vary at every stage; only their actual lost masses must tend to zero. -/
theorem exists_original_refined_window_law_tendsto
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ) (hgap : 0 ≤ gap)
    (δn lossn : ℕ → ℝ≥0∞) (rn : ℕ → ℝ)
    (D : ∀ n, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range)
      (rn n) (δn n) (lossn n))
    (i : ∀ n, Fin (D n).haar.continuous.count)
    (ref : ∀ n, ((D n).haar.continuous.coefficient (i n)).roots)
    (z : ℚ → M) (href : ∀ n, (ref n).val = z)
    (width : ℕ → ℝ) (Q : ∀ n, FiniteScalarBins range (width n))
    (hδ : ∀ n, δn n ≠ ⊤) (hδ1 : ∀ n, (δn n).toReal < 1)
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0)) :
    ∃ π : ProbabilityMeasure (range × range),
      (π : Measure (range × range)).map (Prod.map Subtype.val Subtype.val) = γ z ∧
      Tendsto (fun n ↦
        ((normalizedFiniteLaw ((π : Measure (range × range)).restrict
          {p | ((D n).haar.continuous.coefficient (i n)).clockClassAllowed (Q n)
            ((Q n).rangeClassify p.1) ((Q n).rangeClassify p.2)})).toSignedMeasure -
          (π : Measure (range × range)).toSignedMeasure).totalVariation.real univ) atTop (𝓝 0) := by
  obtain ⟨π,hπ,hmap,_⟩ := (D 0).exists_original_window_continuous_clock_law
    hrange γ gap (i 0) (ref 0) (Q 0) (by norm_num : (0 : ℝ) < 1) hgap (hδ 0) (hδ1 0)
  haveI : IsProbabilityMeasure π := hπ
  have hmapz : π.map (Prod.map Subtype.val Subtype.val) = γ z := by
    simpa only [href 0] using hmap
  refine ⟨⟨π,hπ⟩,hmapz,?_⟩
  apply tendsto_totalVariation_normalized_submeasure_of_mass π _ atTop
    (fun n ↦ (δn n).toReal) hδlim
  apply Filter.Eventually.of_forall
  intro n
  refine ⟨Measure.restrict_le_self,ENNReal.toReal_nonneg,hδ1 n,?_⟩
  apply (D n).original_window_retained_mass_of_map hrange γ gap (i n) (ref n) (Q n)
    π _ hgap (hδ n) (hδ1 n)
  simpa only [href n] using hmapz

end OTSelector.Reconstruction
