import OTSelector.Reconstruction.OriginalFineClockMaskLawVariation
import OTSelector.Reconstruction.FinslerOriginalWindowContinuousClockLaw

/-! Actual Finsler original cores give a fixed positive closed-window law.
Every fine physical mask converges to this same original law, before and after
normalization; conditional clocks and boundary atoms remain unchanged. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical
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

/-- The original Finsler core supplies both scalar support conditions of its
unchanged conditional joint law, at every actual retained root. -/
theorem PopulationLocalPressureCore.original_pair_range_support
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (z : (D.haar.continuous.coefficient i).roots) :
    ∀ᵐ p ∂γ z.val, p.1 ∈ range ∧ p.2 ∈ range := by
  have hz : z.val ∈ D.haar.continuous.population.roots :=
    D.haar.continuous.union_eq ▸ mem_iUnion.mpr ⟨i,z.property⟩
  have hgood := (D.haar.continuous.population.good z.val hz).1
  have hs : ∀ᵐ p ∂γ z.val, p.1 ∈ range := by
    apply (ae_map_iff measurable_fst.aemeasurable hrange).mp
    rw [hgood.1.1]
    change ∀ᵐ s ∂condDistrib u a μ z.val, s ∈ range
    exact hgood.2.2.1
  have ht : ∀ᵐ p ∂γ z.val, p.2 ∈ range := by
    apply (ae_map_iff measurable_snd.aemeasurable hrange).mp
    rw [hgood.1.2]
    change ∀ᵐ s ∂condDistrib u a ν z.val, s ∈ range
    exact hgood.2.2.2
  exact hs.and ht

/-- The actual original core internally gives a positive closed-window
retained mass. All fine literal masks converge to that SAME original joint
law in raw and normalized variation, irrespective of the fine bin choices.
No window-gap comparison or boundary non-atomicity is imposed. -/
theorem PopulationLocalPressureCore.original_fine_window_laws_converge
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (z : (D.haar.continuous.coefficient i).roots)
    {width : ℕ → ℝ} (Q : ∀ n, FiniteScalarBins range (width n))
    (hwidth : Tendsto width atTop (𝓝 0))
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    let C := D.haar.continuous.coefficient i
    let χ := fun n ↦ (γ z.val).restrict ((Q n).originalClockMaskSet (C.clockClassAllowed (Q n)))
    let χwindow := (γ z.val).restrict C.window.region
    1 - δ.toReal ≤ χwindow.real univ ∧
      0 < χwindow.real univ ∧
      Tendsto (fun n ↦ (χ n).real univ) atTop (𝓝 (χwindow.real univ)) ∧
      Tendsto (fun n ↦ ((χ n).toSignedMeasure - χwindow.toSignedMeasure).totalVariation.real univ)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ((normalizedFiniteLaw (χ n)).toSignedMeasure -
        (normalizedFiniteLaw χwindow).toSignedMeasure).totalVariation.real univ) atTop (𝓝 0) := by
  dsimp only
  let C := D.haar.continuous.coefficient i
  have hs := D.original_pair_range_support hrange γ gap i z
  have hclosed : IsClosed C.window.region := C.window.isCompact_region.isClosed
  have hallowed n : C.clockClassAllowed (Q n) = (Q n).regionClockAllowed C.window.region := rfl
  have hm := tendsto_originalFineClockMask_mass Q hwidth hclosed (γ z.val) hs
  have hmreal : Tendsto (fun n ↦ ((γ z.val).restrict
      ((Q n).originalClockMaskSet (C.clockClassAllowed (Q n)))).real univ)
      atTop (𝓝 (((γ z.val).restrict C.window.region).real univ)) := by
    simpa only [hallowed,measureReal_def,Measure.restrict_apply_univ,Function.comp_def] using
      (ENNReal.tendsto_toReal (measure_ne_top (γ z.val) C.window.region)).comp hm
  have hlower n : 1 - δ.toReal ≤ ((γ z.val).restrict
      ((Q n).originalClockMaskSet (C.clockClassAllowed (Q n)))).real univ := by
    obtain ⟨π,hπ,hmap,hbound,_⟩ := D.exists_original_window_continuous_clock_law
      hrange γ gap i z (Q n) (by norm_num : (0:ℝ) < 1) hgap hδ hδ1
    have hh := (Q n).real_restrict_originalClockMaskSet_eq (C.clockClassAllowed (Q n)) π
    rw [hmap] at hh
    rw [hh]
    exact hbound
  have hmass : 1 - δ.toReal ≤ ((γ z.val).restrict C.window.region).real univ :=
    ge_of_tendsto hmreal (Filter.Eventually.of_forall hlower)
  have hpos := (sub_pos.mpr hδ1).trans_le hmass
  refine ⟨hmass,hpos,hmreal,?_,?_⟩
  · convert tendsto_originalFineClockMask_raw_variation Q hwidth hclosed (γ z.val) hs using 1
    rfl
  · convert tendsto_originalFineClockMask_normalized_variation
      Q hwidth hclosed (γ z.val) hs
      (by simpa only [measureReal_def,Measure.restrict_apply_univ,Function.comp_def] using hpos) using 1
    rfl

end OTSelector.Reconstruction
