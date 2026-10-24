import OTSelector.Reconstruction.FinslerOriginalWindowLawVariation

/-! Auxiliary window/core refinement preserves the actual original Haar
intensity at every retained original root. Full retained class masses recover
that intensity as the recorded original losses vanish. -/
open Set Function MeasureTheory ProbabilityTheory Filter Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
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



/-- Two original auxiliary cores containing one original root use the same
original selected seed and therefore the same literal Haar intensity. -/
theorem PopulationLocalPressureCore.rootIntensity_eq_of_common_root
    {Good : (ℚ → M) → Prop} {r' : ℝ} {δ' loss' : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (D' : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r' δ' loss')
    (i : Fin D.haar.continuous.count) (i' : Fin D'.haar.continuous.count)
    (z : ℚ → M) (hz : z ∈ (D.haar.continuous.coefficient i).roots)
    (hz' : z ∈ (D'.haar.continuous.coefficient i').roots) :
    D.rootIntensity i z = D'.rootIntensity i' z := by
  have hseed : (D.haar.continuous.coefficient i).seedIndex =
      (D'.haar.continuous.coefficient i').seedIndex := by
    by_contra hne
    exact disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ (μ.map a) hne)
      ((D.haar.continuous.coefficient i).roots_subset_piece hz)
      ((D'.haar.continuous.coefficient i').roots_subset_piece hz')
  dsimp only [PopulationLocalPressureCore.rootIntensity]
  rw [hseed]

/-- The full physical retained class mass is identified on every exact lift
of the unchanged original conditional clock law. The equality keeps both the
scalar retention and actual original window loss. -/
theorem PopulationLocalPressureCore.original_window_weights_mass_of_map
    {range : Set ℝ} (hrange : MeasurableSet range)
    (γ : Kernel (ℚ → M) (ℝ × ℝ)) [IsMarkovKernel γ] (gap : ℝ)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b
      (originalClockPairGood γ (condDistrib u a μ) (condDistrib u a ν) gap range) r δ loss)
    (i : Fin D.haar.continuous.count) (ref : (D.haar.continuous.coefficient i).roots)
    {width : ℝ} (Q : FiniteScalarBins range width) {η : ℝ} (hη : η < 1)
    (π : Measure (range × range))
    (hmap : π.map (Prod.map Subtype.val Subtype.val) = γ ref.val)
    (hgap : 0 ≤ gap) (hδ : δ ≠ ⊤) (hδ1 : δ.toReal < 1) :
    (∑ j, ∑ k, D.originalWindowReferenceWeights γ gap range i ref Q η j k) =
      ((1 - η) * D.rootIntensity i ref.val) * (π.restrict
        {p | (D.haar.continuous.coefficient i).clockClassAllowed Q
          (Q.rangeClassify p.1) (Q.rangeClassify p.2)}).real univ := by
  obtain ⟨π',_,hmap',_,_,_,hmass⟩ := D.exists_original_window_continuous_clock_law
    hrange γ gap i ref Q hη hgap hδ hδ1
  have heq : π' = π := ((MeasurableEmbedding.subtype_coe hrange).prodMap
    (MeasurableEmbedding.subtype_coe hrange)).map_injective (hmap'.trans hmap.symm)
  simpa only [heq] using hmass


/-- Actual original window/core refinement recovers both the full conditional
clock law and its full original Haar intensity. No prescribed class balance,
fixed seed, or pointwise density lower bound is assumed. -/
theorem exists_original_refined_window_law_and_intensity_tendsto
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
    (hδlim : Tendsto (fun n ↦ (δn n).toReal) atTop (𝓝 0))
    (η : ℕ → ℝ) (hη : ∀ n, 0 ≤ η n ∧ η n < 1) (hηlim : Tendsto η atTop (𝓝 0)) :
    ∃ π : ProbabilityMeasure (range × range),
      (π : Measure (range × range)).map (Prod.map Subtype.val Subtype.val) = γ z ∧
      Tendsto (fun n ↦
        ((normalizedFiniteLaw ((π : Measure (range × range)).restrict
          {p | ((D n).haar.continuous.coefficient (i n)).clockClassAllowed (Q n)
            ((Q n).rangeClassify p.1) ((Q n).rangeClassify p.2)})).toSignedMeasure -
          (π : Measure (range × range)).toSignedMeasure).totalVariation.real univ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∑ j, ∑ k,
        (D n).originalWindowReferenceWeights γ gap range (i n) (ref n) (Q n) (η n) j k)
        atTop (𝓝 ((D 0).rootIntensity (i 0) (ref 0).val)) := by
  obtain ⟨π,hmap,hTV⟩ := exists_original_refined_window_law_tendsto hrange γ gap hgap
    δn lossn rn D i ref z href width Q hδ hδ1 hδlim
  let retained := fun n ↦ (π : Measure (range × range)).restrict
    {p | ((D n).haar.continuous.coefficient (i n)).clockClassAllowed (Q n)
      ((Q n).rangeClassify p.1) ((Q n).rangeClassify p.2)}
  have hmapn n : (π : Measure (range × range)).map (Prod.map Subtype.val Subtype.val) =
      γ (ref n).val := by simpa only [href n] using hmap
  have hm : Tendsto (fun n ↦ (retained n).real univ) atTop (𝓝 1) := by
    apply tendsto_submeasure_mass_of_lost_mass (π : Measure _) retained atTop
      (fun n ↦ (δn n).toReal) hδlim
    apply Filter.Eventually.of_forall
    intro n
    exact ⟨Measure.restrict_le_self,(D n).original_window_retained_mass_of_map hrange γ gap
      (i n) (ref n) (Q n) (π : Measure _) (hmapn n) hgap (hδ n) (hδ1 n)⟩
  let theta := (D 0).rootIntensity (i 0) (ref 0).val
  have htheta n : (D n).rootIntensity (i n) (ref n).val = theta := by
    change (D n).rootIntensity (i n) (ref n).val = (D 0).rootIntensity (i 0) (ref 0).val
    rw [href n,href 0]
    exact (D n).rootIntensity_eq_of_common_root (D 0) (i n) (i 0) z
      (href n ▸ (ref n).property) (href 0 ▸ (ref 0).property)
  have heq n : (∑ j, ∑ k,
        (D n).originalWindowReferenceWeights γ gap range (i n) (ref n) (Q n) (η n) j k) =
      ((1 - η n) * theta) * (retained n).real univ := by
    rw [(D n).original_window_weights_mass_of_map hrange γ gap (i n) (ref n) (Q n)
      (hη n).2 (π : Measure _) (hmapn n) hgap (hδ n) (hδ1 n),htheta n]
  have hc : Continuous (fun x : ℝ × ℝ ↦ ((1 - x.1) * theta) * x.2) := by fun_prop
  have ht : Tendsto (fun n ↦ ((1 - η n) * theta) * (retained n).real univ) atTop (𝓝 theta) := by
    have h := hc.continuousAt.tendsto.comp (hηlim.prodMk_nhds hm)
    change Tendsto (fun n ↦ ((1 - η n) * theta) * (retained n).real univ)
      atTop (𝓝 (((1 - 0) * theta) * 1)) at h
    simpa only [sub_zero,one_mul,mul_one] using h
  refine ⟨π,hmap,hTV,?_⟩
  convert ht using 1
  funext n
  exact heq n

end OTSelector.Reconstruction
