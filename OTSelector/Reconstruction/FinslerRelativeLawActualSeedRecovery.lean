import OTSelector.Probability.ConditionalEndpointRecovery
import OTSelector.Reconstruction.FinslerRelativeLawActualHaarRetainedLaw
import OTSelector.Reconstruction.FinslerRelativeLawFixedInversePopulation

/-!
The given original physical inverse agrees almost everywhere with the actual
seed map on original conditional clocks. Deterministic retained pair kernels
inherit both endpoint identities through their dominated original marginals,
so original physical and seed-coordinate pair laws agree exactly.
-/

open Set Function MeasureTheory ProbabilityTheory Filter Manifold OTSelector.Geometry
open scoped Topology ContDiff ENNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000





/-- A deterministic retained part of an original conditional pair split has
dominated original conditional marginals. -/
theorem clockPair_marginals_le_of_original_split
    (P Q : Measure (ℝ × ℝ)) (μ ν : Measure ℝ)
    (hwhole : Vlasov.IsCoupling (P + Q) μ ν) :
    P.map Prod.fst ≤ μ ∧ P.map Prod.snd ≤ ν := by
  constructor
  · simpa only [hwhole.1] using
      Measure.map_mono (show P ≤ P + Q from Measure.le_add_right le_rfl) measurable_fst
  · simpa only [hwhole.2] using
      Measure.map_mono (show P ≤ P + Q from Measure.le_add_right le_rfl) measurable_snd





/-- Any retained clock-pair kernel with dominated original marginals uses the
same two actual physical endpoint fields almost everywhere. -/
theorem compProd_pairPhysicalMap_eq_of_dominated_original_marginals
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y] [MeasurableEq Y]
    (r : Measure Z) [SFinite r] (K : Kernel Z (ℝ × ℝ)) [IsSFiniteKernel K]
    (κ₀ κ₁ : Kernel Z ℝ)
    (b c : Z × ℝ → Y) (hb : Measurable b) (hc : Measurable c)
    (hmarginals : ∀ᵐ z ∂r, (K z).map Prod.fst ≤ κ₀ z ∧ (K z).map Prod.snd ≤ κ₁ z)
    (hfields : ∀ᵐ z ∂r,
      (∀ᵐ s ∂κ₀ z, b (z, s) = c (z, s)) ∧
      (∀ᵐ t ∂κ₁ z, b (z, t) = c (z, t))) :
    (r ⊗ₘ K).map (labelClockPairPhysicalMap b) =
      (r ⊗ₘ K).map (labelClockPairPhysicalMap c) := by
  apply Measure.map_congr
  apply Measure.ae_compProd_of_ae_ae
  · have heqSet : {p | labelClockPairPhysicalMap b p = labelClockPairPhysicalMap c p} =
        {p : Z × (ℝ × ℝ) | b (p.1, p.2.1) = c (p.1, p.2.1)} ∩
        {p : Z × (ℝ × ℝ) | b (p.1, p.2.2) = c (p.1, p.2.2)} := by
      ext p
      exact Prod.ext_iff
    rw [heqSet]
    exact (measurableSet_eq_fun
      (hb.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      (hc.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).inter
      (measurableSet_eq_fun
        (hb.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
        (hc.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))))
  · filter_upwards [hmarginals, hfields] with z hm hf
    exact (ae_pair_endpoints_of_dominated_original_marginals (K z) (κ₀ z) (κ₁ z)
      hm.1 hm.2 (fun t ↦ b (z, t)) (fun t ↦ c (z, t)) hf.1 hf.2).mono
        (fun p hp ↦ Prod.ext hp.1 hp.2)



variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda]
  {η₀ η₁ : Measure M} [IsProbabilityMeasure η₀] [IsProbabilityMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

omit [IsFiniteMeasure lambda] in
/-- The given original inverse needs only original almost-everywhere recovery.
An auxiliary exact inverse is chosen internally from original injectivity; the
literal original conditional laws identify the given map with each actual seed
curve on almost every retained original label. -/
theorem PopulationHaarPressureCore.original_inverse_ae_of_ae_recovery
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ y ∂η₁, y ∈ F.potentialRegularDomain u)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x)
    (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (i : Fin D.continuous.count) :
    let Seed := (P (D.continuous.coefficient i).seedIndex).seed
    let R := populationSeedRootLabelValue Seed a
    ∀ᵐ z ∂lambda.restrict (D.continuous.coefficient i).roots,
      (∀ᵐ t ∂condDistrib u a η₀ z, b (z, t) = Seed.curve (R z) (t - Seed.level)) ∧
      (∀ᵐ t ∂condDistrib u a η₁ z, b (z, t) = Seed.curve (R z) (t - Seed.level)) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure η₀
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨c, hc, hinvc, _⟩ := exists_measurable_labelClock_inverse
    (hF.measurableSet_potentialRegularDomain hcomplete u) ha hu.continuous.measurable hinj
  have hη₀eq : ∀ᵐ x ∂η₀, b (a x, u x) = c (a x, u x) := by
    filter_upwards [hη₀reg, hη₀inv] with x hx hi
    rw [hi, hinvc x hx]
  have hη₁eq : ∀ᵐ y ∂η₁, b (a y, u y) = c (a y, u y) := by
    filter_upwards [hη₁reg, hη₁inv] with y hy hi
    rw [hi, hinvc y hy]
  have hs := ae_condDistrib_recovery_eq η₀ a u ha hu.continuous.measurable b c hb hc hη₀eq
  have ht := ae_condDistrib_recovery_eq η₁ a u ha hu.continuous.measurable b c hb hc hη₁eq
  rw [hlabel0] at hs
  rw [hlabel1] at ht
  have hcurve (z) (hz : z ∈ (D.continuous.coefficient i).roots) :
      let Seed := (P (D.continuous.coefficient i).seedIndex).seed
      let R := populationSeedRootLabelValue Seed a
      (∀ᵐ t ∂condDistrib u a η₀ z, c (z, t) = Seed.curve (R z) (t - Seed.level)) ∧
      (∀ᵐ t ∂condDistrib u a η₁ z, c (z, t) = Seed.curve (R z) (t - Seed.level)) := by
    let j := (D.continuous.coefficient i).seedIndex
    have hzpiece := (D.continuous.coefficient i).roots_subset_piece hz
    have hzpop : z ∈ D.continuous.population.roots := D.continuous.union_eq ▸ mem_iUnion.mpr ⟨i, hz⟩
    obtain ⟨W⟩ := ((D.continuous.population.good z hzpop).2 j hzpiece).1
    have h := W.support.original_inverse_ae hF hcomplete hu horder hinvc
      (populationSeedPieceLabel P a κ lambda j ⟨z, hzpiece⟩).property
    rw [populationSeedPieceLabel_root P a κ lambda j ⟨z, hzpiece⟩] at h
    dsimp only
    rw [populationSeedRootLabelValue_on_piece hF hcomplete hu ha hinj j ⟨z, hzpiece⟩]
    exact h
  have hK : MeasurableSet (D.continuous.coefficient i).roots :=
    (D.continuous.coefficient i).roots_compact.measurableSet
  filter_upwards [ae_restrict_mem hK, ae_restrict_of_ae hs, ae_restrict_of_ae ht] with z hz hs ht
  obtain ⟨hcs, hct⟩ := hcurve z hz
  constructor
  · filter_upwards [hs, hcs] with t h₁ h₂
    exact h₁.trans h₂
  · filter_upwards [ht, hct] with t h₁ h₂
    exact h₁.trans h₂

/-- Every actual retained pair kernel with dominated original clock
marginals uses the given original recovery map and the actual seed physical map
interchangeably. Only original almost-everywhere recovery is assumed. -/
theorem PopulationHaarPressureCore.original_retained_pair_physical_law_eq_seed
    (D : PopulationHaarPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hb : Measurable b)
    (hη₀reg : ∀ᵐ x ∂η₀, x ∈ F.potentialRegularDomain u)
    (hη₁reg : ∀ᵐ y ∂η₁, y ∈ F.potentialRegularDomain u)
    (hη₀inv : ∀ᵐ x ∂η₀, b (a x, u x) = x)
    (hη₁inv : ∀ᵐ y ∂η₁, b (a y, u y) = y)
    (hlabel0 : η₀.map a = lambda) (hlabel1 : η₁.map a = lambda)
    (i : Fin D.continuous.count) {L : Set (ℚ → M)} (hL : MeasurableSet L)
    (hsub : L ⊆ (D.continuous.coefficient i).roots)
    (K : Kernel (ℚ → M) (ℝ × ℝ)) [IsSFiniteKernel K]
    (hmarginals : ∀ᵐ z ∂lambda.restrict L,
      (K z).map Prod.fst ≤ condDistrib u a η₀ z ∧
      (K z).map Prod.snd ≤ condDistrib u a η₁ z) :
    let Seed := (P (D.continuous.coefficient i).seedIndex).seed
    let R := populationSeedRootLabelValue Seed a
    ((lambda.restrict L) ⊗ₘ K).map (labelClockPairPhysicalMap b) =
      (((lambda.restrict L) ⊗ₘ K).map (Prod.map R id)).map
        (labelClockPairPhysicalMap (populationSeedPhysicalMap Seed)) := by
  let _instMetric : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let _instRootBorel : BorelSpace (ℚ → M) := inferInstance
  let C := D.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue Seed a
  have hR : Measurable R := measurable_populationSeedRootLabelValue Seed hF hcomplete hu ha hinj
  have hphysical := measurable_populationSeedPhysicalMap Seed
  let c := fun q : (ℚ → M) × ℝ ↦ populationSeedPhysicalMap Seed (R q.1, q.2)
  have hc : Measurable c := hphysical.comp ((hR.comp measurable_fst).prodMk measurable_snd)
  have hcurve := D.original_inverse_ae_of_ae_recovery hF hcomplete hu ha hinj horder hb
    hη₀reg hη₁reg hη₀inv hη₁inv hlabel0 hlabel1 i
  have hfields : ∀ᵐ z ∂lambda.restrict L,
      (∀ᵐ s ∂condDistrib u a η₀ z, b (z, s) = c (z, s)) ∧
      (∀ᵐ t ∂condDistrib u a η₁ z, b (z, t) = c (z, t)) := by
    filter_upwards [ae_restrict_mem hL, ae_restrict_of_ae_restrict_of_subset hsub hcurve] with z hz he
    have hzI : z ∈ (D.intensity i).roots := by
      rw [D.intensity_roots]
      exact hsub hz
    let w : Seed.labels := ⟨R z, (D.intensity i).labels_subset (mem_image_of_mem R hzI)⟩
    have hseed (t : ℝ) : c (z, t) = Seed.curve (R z) (t - Seed.level) :=
      populationSeedPhysicalMap_at_label Seed w t
    constructor
    · filter_upwards [he.1] with t ht
      exact ht.trans (hseed t).symm
    · filter_upwards [he.2] with t ht
      exact ht.trans (hseed t).symm
  have hmap := compProd_pairPhysicalMap_eq_of_dominated_original_marginals
    (lambda.restrict L) K (condDistrib u a η₀) (condDistrib u a η₁) b c hb hc hmarginals hfields
  change ((lambda.restrict L) ⊗ₘ K).map (labelClockPairPhysicalMap b) =
    (((lambda.restrict L) ⊗ₘ K).map (Prod.map R id)).map
      (labelClockPairPhysicalMap (populationSeedPhysicalMap Seed))
  rw [Measure.map_map (measurable_labelClockPairPhysicalMap hphysical) (hR.prodMap measurable_id)]
  exact hmap

end OTSelector.Reconstruction
