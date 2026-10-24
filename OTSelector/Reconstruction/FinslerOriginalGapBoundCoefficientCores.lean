import OTSelector.Reconstruction.FinslerFiniteCoefficientCores

/-! Preserve the original support-gap certificate already used by the rational
window construction, through actual finite coefficient cores and restrictions. -/
open Set Function MeasureTheory ProbabilityTheory Matrix Module Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

variable {E M Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  [MeasurableSpace M] [TopologicalSpace Z] [MeasurableSpace Z]

variable [T2Space M] [PreconnectedSpace M] [BorelSpace M]
  [MeasurableSpace.CountablySeparated Z] [PolishSpace Z] [BorelSpace Z]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → Z}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure Z} [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]

/-- Finite disjoint compact coefficient cores are produced from the original
moment law and physical support gap, uniformly over all legal conditional pairings. -/
theorem PopulationSeedPieceMomentLaw.exists_finite_coefficient_cores_with_original_gap
    (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFiniteCoefficientMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    {Good : Z → Prop} (hgood : ∀ᵐ z ∂lambda, Good z)
    {δ ε : ℝ≥0∞} (hδ : δ ≠ 0) (hε : ε ≠ 0) :
    ∃ (N : ℕ) (C : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ),
      Pairwise (fun i j ↦ Disjoint (C i).roots (C j).roots) ∧
      lambda (⋃ i, (C i).roots)ᶜ < ε ∧
      (∀ i, ∀ z ∈ (C i).roots, Good z) ∧
      ∀ i, (C i).roots.Nonempty → ((C i).window.val.2.2 : ℝ) ≤ gap := by
  classical
  let : Nonempty RationalScalarPairWindow := ⟨⟨(0, 1, 1), by norm_num⟩⟩
  obtain ⟨e, he⟩ := exists_surjective_nat (ℕ × RationalScalarPairWindow)
  let R := populationCoefficientWindowRoots P a κ lambda η₀ η₁ gap δ
  let s : ℕ → Set Z := disjointed (fun n ↦ R (e n))
  have hsm : ∀ n, MeasurableSet (s n) := MeasurableSet.disjointed (fun n ↦
    measurableSet_populationCoefficientWindowRoots hF hcomplete hu ha hinj gap δ (e n))
  have hsub (n : ℕ) : s n ⊆ R (e n) := disjointed_subset _ n
  have hscover : ∀ᵐ z ∂lambda, z ∈ ⋃ n, s n := by
    filter_upwards [hlaw.ae_mem_coefficientWindowRoots hcover hgap hsep hδ] with z hz
    change z ∈ ⋃ n, disjointed (fun n ↦ R (e n)) n
    rw [iUnion_disjointed, he.iUnion_comp]
    exact hz
  let CoreProperty : ℕ → Set Z → Prop := fun n K ↦
    ContinuousOn (populationSeedRootCoefficient (P (e n).1).seed a
      (Module.finBasis ℝ (P (e n).1).seed.covector.ker)) (K ×ˢ (e n).2.region) ∧
    ∀ z ∈ K, HasOriginalSeedPairWindow (P (e n).1).seed a
      (condDistrib u a η₀) (condDistrib u a η₁) (e n).2.val.1 (e n).2.val.2.1 z ∧
      ConditionalClockSupportBounds (condDistrib u a η₀ z) (condDistrib u a η₁ z) gap diam ∧
      Good z
  have hcore (n : ℕ) (τ : ℝ≥0∞) (hτ : τ ≠ 0) :
      ∃ K ⊆ s n, IsCompact K ∧ lambda (s n \ K) < τ ∧ CoreProperty n K := by
    have hqorder : ((e n).2.val.1 : ℝ) ≤ (e n).2.val.2.1 := by
      exact_mod_cast (e n).2.property.1.le
    have hdata := hlaw.ae_pair_window_on_piece hF hcomplete hu ha hinj (e n).1 hqorder
    have hss : s n ⊆ populationSeedRootPiece P a κ lambda (e n).1 ∩
        scalarSupportInteriorWindow (condDistrib u a η₀) (condDistrib u a η₁)
          (e n).2.val.1 (e n).2.val.2.1 := fun z hz ↦
      ⟨(hsub n hz).1, (hsub n hz).2.1⟩
    have hfull := (ae_restrict_of_ae_restrict_of_subset hss hdata).and
      (ae_restrict_of_ae (hsep.and hgood))
    exact exists_populationSeedRootCoefficient_compact_core (P (e n).1).seed
      hF hcomplete hu ha hinj (hsm n) (measure_ne_top _ _) hqorder
      (e n).2.isCompact_region (e n).2.region_subset hfull hτ
  obtain ⟨N, K, hmass, hK⟩ :=
    exists_finite_compact_root_cores lambda s hsm hscover CoreProperty hcore hε
  let C : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ := fun n ↦ {
    seedIndex := (e n).1
    window := (e n).2
    roots := K n
    roots_compact := (hK n).2.1
    roots_subset_piece := fun z hz ↦ (hsub n ((hK n).1 hz)).1
    coefficient_continuous := (hK n).2.2.1
    original_window := fun z hz ↦ ((hK n).2.2.2 z hz).1
    coefficient_posDef := fun z hz p hp ↦
      (((hK n).2.2.2 z hz).1).posDef_rootCoefficient (P (e n).1).seed
        hF hcomplete hu ha hinj ((e n).2.region_subset hp)
    coupling_loss := fun z hz π hπ horder ↦
      rationalScalarWindowRoots.uniform_coupling_loss (hsub n ((hK n).1 hz)).2
        ((hK n).2.2.2 z hz).2.1 hπ horder }
  refine ⟨N, C, ?_, hmass, (fun n z hz ↦ ((hK n).2.2.2 z hz).2.2),?_⟩
  · intro i j hij
    exact ((disjoint_disjointed (fun n ↦ R (e n)))
      (fun h ↦ hij (Fin.ext h))).mono (hK i).1 (hK j).1
  · intro i ⟨z,hz⟩
    exact (hsub i ((hK i).1 hz)).2.2.1

/-- The same finite coefficient construction can refine any existing compact original-root
core, with explicit additional and total mass loss and unchanged conditional laws. -/
theorem PopulationSeedPieceMomentLaw.exists_finite_coefficient_cores_within_original_gap
    (hlaw : PopulationSeedPieceMomentLaw P a κ lambda η₀ η₁)
    (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, populationSeedRootPiece P a κ lambda j)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFiniteCoefficientMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    {gap diam : ℝ} (hgap : 0 < gap)
    (hsep : PopulationConditionalSeparationLaw u a lambda η₀ η₁ gap diam)
    {Good : Z → Prop} (hgood : ∀ᵐ z ∂lambda, Good z)
    {δ ε : ℝ≥0∞} (hδ : δ ≠ 0) (hε : ε ≠ 0)
    {H : Set Z} (hH : IsCompact H) :
    ∃ (N : ℕ) (C : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ),
      Pairwise (fun i j ↦ Disjoint (C i).roots (C j).roots) ∧
      IsCompact (⋃ i, (C i).roots) ∧ (⋃ i, (C i).roots) ⊆ H ∧
      lambda (H \ ⋃ i, (C i).roots) < ε ∧
      lambda (⋃ i, (C i).roots)ᶜ < lambda Hᶜ + ε ∧
      (∀ i, ∀ z ∈ (C i).roots, Good z) ∧
      ∀ i, (C i).roots.Nonempty → ((C i).window.val.2.2 : ℝ) ≤ gap := by
  obtain ⟨N, C, hd, hsmall, hgoodC,hgapC⟩ := hlaw.exists_finite_coefficient_cores_with_original_gap
    hcover hF hcomplete hu ha hinj hgap hsep hgood hδ hε
  let D : Fin N → OriginalPopulationCoefficientCore P a κ lambda η₀ η₁ δ :=
    fun i ↦ (C i).restrictRoots ((C i).roots_compact.inter hH) inter_subset_left
  have hDsub : (⋃ i, (D i).roots) ⊆ H :=
    iUnion_subset fun _ ↦ inter_subset_right
  have hdiff : H \ ⋃ i, (D i).roots ⊆ (⋃ i, (C i).roots)ᶜ := by
    intro z hz hmem
    obtain ⟨i, hi⟩ := mem_iUnion.mp hmem
    exact hz.2 (mem_iUnion.mpr ⟨i, hi, hz.1⟩)
  have hcompl : (⋃ i, (D i).roots)ᶜ ⊆ Hᶜ ∪ (⋃ i, (C i).roots)ᶜ := by
    intro z hz
    by_cases hzh : z ∈ H
    · exact Or.inr (hdiff ⟨hzh, hz⟩)
    · exact Or.inl hzh
  refine ⟨N, D, ?_, isCompact_iUnion (fun i ↦ (D i).roots_compact), hDsub,
    (measure_mono hdiff).trans_lt hsmall, ?_, ?_,?_⟩
  · intro i j hij
    exact (hd hij).mono inter_subset_left inter_subset_left
  · exact ((measure_mono hcompl).trans (measure_union_le _ _)).trans_lt
      (ENNReal.add_lt_add_left (measure_ne_top _ _) hsmall)
  · exact fun i z hz ↦ hgoodC i z hz.1
  · intro i ⟨z,hz⟩
    exact hgapC i ⟨z,hz.1⟩

end OTSelector.Reconstruction
