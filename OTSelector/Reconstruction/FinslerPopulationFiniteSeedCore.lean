import OTSelector.Reconstruction.FinslerPopulationCompactCore
import OTSelector.Reconstruction.FinslerSeedRootPartition

/-!
# Finite original seed cores of the common physical label law

The original disjoint seed pieces cover almost every common label. Finite initial
segments therefore lose arbitrarily little mass. The same actual conditional
densities provide a common compact total-variation core inside that finite union,
while retaining any specified almost-everywhere property.
-/

open Set MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false

/-- A countable measurable cover of a finite measure has finite initial segments
whose complements have arbitrarily small measure. -/
theorem exists_initial_cover_measure_compl_lt {Z : Type*} [MeasurableSpace Z]
    (lambda : Measure Z) [IsFiniteMeasure lambda] (s : ℕ → Set Z)
    (hs : ∀ j, MeasurableSet (s j)) (hcover : ∀ᵐ z ∂lambda, z ∈ ⋃ j, s j)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ N : ℕ, lambda (⋃ j < N, s j)ᶜ < ε := by
  have hm (N : ℕ) : MeasurableSet (⋃ j < N, s j)ᶜ :=
    (MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ hs j).compl
  have hanti : Antitone (fun N : ℕ ↦ (⋃ j < N, s j)ᶜ) := by
    intro N L hNL z hz hzN
    apply hz
    obtain ⟨j, hj, hzj⟩ := mem_iUnion₂.mp hzN
    exact mem_iUnion₂.mpr ⟨j, hj.trans_le hNL, hzj⟩
  have hzero : lambda (⋂ N : ℕ, (⋃ j < N, s j)ᶜ) = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hcover] with z hz
    obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
    intro hzall
    exact (mem_iInter.mp hzall (j + 1))
      (mem_iUnion₂.mpr ⟨j, Nat.lt_succ_self j, hzj⟩)
  rw [hanti.measure_iInter (fun N ↦ (hm N).nullMeasurableSet)
    ⟨0, measure_ne_top _ _⟩] at hzero
  exact iInf_lt_iff.mp (hzero ▸ pos_iff_ne_zero.mpr hε)

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- A common compact core of both original conditional laws is carried by finitely
many of the original selected seed pieces, with arbitrarily small total lost mass. -/
def PopulationFiniteSeedCompactCoreLaw (P : ℕ → F.CalibratedSeedWindow u)
    (a : M → (ℚ → M)) (κ : ∀ j, Measure (P j).seed.covector.ker)
    (lambda : Measure (ℚ → M)) (η₀ η₁ : Measure M)
    [IsFiniteMeasure η₀] [IsFiniteMeasure η₁] (ρ₀ ρ₁ : M → ℝ) (v : ℕ → E → ℝ) : Prop :=
  let H := populationTwoColorDensity P a κ lambda ρ₀ ρ₁ v
  let k := populationTwoColorClockKernel u a η₀ η₁
  ∀ (Good : (ℚ → M) → Prop), (∀ᵐ z ∂lambda, Good z) →
    ∀ ε : ℝ≥0∞, ε ≠ 0 →
      ∃ (N : ℕ) (L : Fin 2 → (ℚ → M) → Lp ℝ 1 (volume : Measure ℝ))
        (K : Set (ℚ → M)),
        (∀ i, @Measurable _ _ _ (borel _) (L i)) ∧
        K ⊆ ⋃ j < N, populationSeedRootPiece P a κ lambda j ∧ IsCompact K ∧
        lambda Kᶜ < ε ∧ (∀ j, IsCompact (K ∩ populationSeedRootPiece P a κ lambda j)) ∧
        ContinuousOn (fun z i ↦ L i z) K ∧
        (∀ z ∈ K, Good z ∧ ∀ i,
          (∫⁻ t, H i (z, t)) = 1 ∧
          (volume : Measure ℝ).withDensity (fun t ↦ H i (z, t)) = k i z ∧
          (⇑(L i z)) =ᵐ[volume] (fun t ↦ (H i (z, t)).toReal)) ∧
        (∀ i, ∀ z ∈ K, ∀ z' ∈ K,
          ((k i z).toSignedMeasure - (k i z').toSignedMeasure).totalVariation univ =
            ENNReal.ofReal ‖L i z - L i z'‖) ∧
        ∀ i, ContinuousOn (fun p : (ℚ → M) × (ℚ → M) ↦
          ((k i p.1).toSignedMeasure - (k i p.2).toSignedMeasure).totalVariation univ)
          (K ×ˢ K)

/-- The original normalized atlas and its shared label reference construct finite
seed compact cores without a supplied finite-cover or good-label selection. -/
theorem PopulationConditionalWindowLaw.finite_seed_compact_core
    {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
    {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
    {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
    {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ}
    (hsource : PopulationConditionalWindowLaw P a κ lambda η₀ ρ₀ v)
    (htarget : PopulationConditionalWindowLaw P a κ lambda η₁ ρ₁ v)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _instFiniteSeedMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Function.Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _instFiniteSeedOrder : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hκ : ∀ j, SigmaFinite (κ j)) :
    PopulationFiniteSeedCompactCoreLaw P a κ lambda η₀ η₁ ρ₀ ρ₁ v := by
  classical
  let _instFiniteCoreMetric : MetricSpace M := F.metricSpace
  let _instFiniteCoreProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instFiniteCorePolish : PolishSpace M := inferInstance
  let _instFiniteCoreLabelsBorel : BorelSpace (ℚ → M) := inferInstance
  have hfinite : IsFiniteMeasure lambda := hsource.label_law ▸ inferInstance
  have hm := measurableSet_populationSeedRootPiece P a κ lambda hF hcomplete hu ha hinj
  have hcover := hsource.ae_mem_populationSeedRootPieces P a κ lambda
    hF hcomplete hu ha hinj horder hκ
  intro Good hGood ε hε
  obtain ⟨N, hN⟩ := exists_initial_cover_measure_compl_lt lambda _ hm hcover
    (ENNReal.half_pos hε).ne'
  let s := ⋃ j < N, populationSeedRootPiece P a κ lambda j
  have hs : MeasurableSet s :=
    MeasurableSet.iUnion fun j ↦ MeasurableSet.iUnion fun _ ↦ hm j
  let f : (ℚ → M) → ℕ → ℝ := fun z j ↦
    (populationSeedRootPiece P a κ lambda j).indicator (fun _ ↦ 1) z
  have hf : Measurable f := measurable_pi_lambda _ fun j ↦
    measurable_const.indicator (hm j)
  obtain ⟨K₀, hK₀s, hK₀, hsmall₀, hfK₀⟩ :=
    Geometry.exists_lusin_compact_core (μ := lambda) hs (measure_ne_top lambda s) hf
      (ENNReal.half_pos (ENNReal.half_pos hε).ne').ne'
  obtain ⟨L, K, hLm, hKs, hK, hsmall, hLc, hGoodK, hTV, hTVc⟩ :=
    hsource.compact_core htarget hcomplete Good hGood K₀ hK₀.measurableSet
      ((ε / 2) / 2) (ENNReal.half_pos (ENNReal.half_pos hε).ne').ne'
  have hsmallTotal : lambda (s \ K) < ε / 2 := by
    calc
      lambda (s \ K) ≤ lambda ((s \ K₀) ∪ (K₀ \ K)) := measure_mono (by
        intro z hz
        by_cases hz₀ : z ∈ K₀
        · exact Or.inr ⟨hz₀, hz.2⟩
        · exact Or.inl ⟨hz.1, hz₀⟩)
      _ ≤ lambda (s \ K₀) + lambda (K₀ \ K) := measure_union_le _ _
      _ < (ε / 2) / 2 + (ε / 2) / 2 := ENNReal.add_lt_add hsmall₀ hsmall
      _ = ε / 2 := ENNReal.add_halves _
  refine ⟨N, L, K, hLm, hKs.trans hK₀s, hK, ?_, ?_, hLc, hGoodK, hTV, hTVc⟩
  · have hsub : Kᶜ ⊆ sᶜ ∪ (s \ K) := by
      intro z hz
      by_cases hzs : z ∈ s
      · exact Or.inr ⟨hzs, hz⟩
      · exact Or.inl hzs
    calc
      lambda Kᶜ ≤ lambda sᶜ + lambda (s \ K) :=
        (measure_mono hsub).trans (measure_union_le _ _)
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add hN hsmallTotal
      _ = ε := ENNReal.add_halves ε
  · intro j
    have hc : ContinuousOn (fun z ↦ f z j) K :=
      (continuous_apply j).comp_continuousOn (hfK₀.mono hKs)
    have hcompact := hc.upperSemicontinuousOn.isCompact_inter_preimage_Ici hK 1
    convert hcompact using 1
    ext z
    simp only [mem_inter_iff, mem_preimage, mem_Ici, f]
    by_cases hz : z ∈ populationSeedRootPiece P a κ lambda j <;> simp [hz]

end OTSelector.Reconstruction
