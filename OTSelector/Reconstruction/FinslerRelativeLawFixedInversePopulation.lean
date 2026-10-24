import OTSelector.Probability.CellwisePopulation

/-!
Retained and residual original populations use one given original physical
recovery inverse. Exact original marginals, calibration and residual mass are
preserved without choosing a second inverse for the coefficient comparison.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- The given original recovery inverse transports both retained and residual
clock populations to the same actual physical coefficient field. -/
theorem original_calibrated_coupling_of_labelClock_inverse
    {M Z : Type*} [MetricSpace M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] [StandardBorelSpace M] [Nonempty M] [MeasurableSpace Z]
    [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    {N : Set M} (hN : MeasurableSet N)
    {a : M → Z} {u : M → ℝ} (ha : Measurable a) (hu : Measurable u)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure M) (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (b : Z × ℝ → M) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (Λ : Measure ((Z × ℝ) × (Z × ℝ)))
    (hΛ : Vlasov.IsCoupling Λ (μ.map (fun x ↦ (a x, u x)))
      (ν.map (fun y ↦ (a y, u y))))
    (hforward : ∀ᵐ p ∂Λ, p.1.1 = p.2.1 ∧ p.1.2 ≤ p.2.2) :
    Vlasov.IsCoupling (Λ.map (Prod.map b b)) μ ν ∧
      (∀ᵐ p ∂Λ.map (Prod.map b b), u p.2 - u p.1 = dist p.1 p.2) ∧
      ∀ ξ : Measure ((Z × ℝ) × (Z × ℝ)), ξ ≤ Λ →
        ξ.map (Prod.map b b) ≤ Λ.map (Prod.map b b) ∧
        ξ.map (Prod.map b b) Set.univ = ξ Set.univ := by
  let c : M → Z × ℝ := fun x ↦ (a x, u x)
  have hc : Measurable c := ha.prodMk hu
  have hμback : (μ.map c).map b = μ := by
    rw [Measure.map_map hb hc]
    calc
      μ.map (b ∘ c) = μ.map id := Measure.map_congr hμinv
      _ = μ := Measure.map_id
  have hνback : (ν.map c).map b = ν := by
    rw [Measure.map_map hb hc]
    calc
      ν.map (b ∘ c) = ν.map id := Measure.map_congr hνinv
      _ = ν := Measure.map_id
  have hphysical : Vlasov.IsCoupling (Λ.map (Prod.map b b)) μ ν := by
    have h := hΛ.map b b hb hb
    change Vlasov.IsCoupling (Λ.map (Prod.map b b)) ((μ.map c).map b) ((ν.map c).map b) at h
    rwa [hμback, hνback] at h
  have hMeas : MeasurableSet {z : Z × ℝ | b z ∈ N ∧ c (b z) = z} := by
    convert (hb hN).inter ((measurableSet_eq_fun (ha.comp hb) measurable_fst).inter
      (measurableSet_eq_fun (hu.comp hb) measurable_snd)) using 1
    ext z
    rcases z with ⟨z, t⟩
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Function.comp_apply, c, Prod.mk.injEq]
  have hclockμ : ∀ᵐ z ∂μ.map c, b z ∈ N ∧ c (b z) = z := by
    apply (ae_map_iff hc.aemeasurable hMeas).mpr
    filter_upwards [hμN, hμinv] with x hx hinv
    change b (a x, u x) ∈ N ∧ c (b (a x, u x)) = c x
    rw [hinv]
    exact ⟨hx, rfl⟩
  have hclockν : ∀ᵐ z ∂ν.map c, b z ∈ N ∧ c (b z) = z := by
    apply (ae_map_iff hc.aemeasurable hMeas).mpr
    filter_upwards [hνN, hνinv] with x hx hinv
    change b (a x, u x) ∈ N ∧ c (b (a x, u x)) = c x
    rw [hinv]
    exact ⟨hx, rfl⟩
  have hleft : ∀ᵐ p ∂Λ, b p.1 ∈ N ∧ c (b p.1) = p.1 :=
    ae_of_ae_map measurable_fst.aemeasurable (hΛ.1.symm ▸ hclockμ)
  have hright : ∀ᵐ p ∂Λ, b p.2 ∈ N ∧ c (b p.2) = p.2 :=
    ae_of_ae_map measurable_snd.aemeasurable (hΛ.2.symm ▸ hclockν)
  refine ⟨hphysical, ?_, ?_⟩
  · apply (ae_map_iff (hb.prodMap hb).aemeasurable
      (measurableSet_eq_fun ((hu.comp measurable_snd).sub (hu.comp measurable_fst))
        (continuous_fst.dist continuous_snd).measurable)).mpr
    filter_upwards [hleft, hright, hforward] with p hx hy hf
    apply (horder (b p.1) hx.1 (b p.2) hy.1).mp
    have hax : a (b p.1) = p.1.1 := congrArg Prod.fst hx.2
    have hay : a (b p.2) = p.2.1 := congrArg Prod.fst hy.2
    have hux : u (b p.1) = p.1.2 := congrArg Prod.snd hx.2
    have huy : u (b p.2) = p.2.2 := congrArg Prod.snd hy.2
    exact ⟨hax.trans (hf.1.trans hay.symm), by simpa only [hux, huy] using hf.2⟩
  · intro ξ hξ
    exact ⟨Measure.map_mono hξ (hb.prodMap hb),
      by rw [Measure.map_apply (hb.prodMap hb) MeasurableSet.univ, Set.preimage_univ]⟩


/-- Continuous cellwise pair kernels rebuild the original population through
its given original inverse, with both retained and residual parts using that map. -/
theorem exists_original_cellwise_residual_population_with_inverse
    {X Z C : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    [Fintype C] {N : Set X} (hN : MeasurableSet N)
    {a : X → Z} {u : X → ℝ} (ha : Measurable a) (hu : Measurable u)
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (b : Z × ℝ → X) (hb : Measurable b)
    (hμinv : ∀ᵐ x ∂μ, b (a x, u x) = x) (hνinv : ∀ᵐ y ∂ν, b (a y, u y) = y)
    (π : Measure (X × X)) (hπ : Vlasov.IsCoupling π μ ν)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (hforward : ∀ᵐ p ∂π, u p.1 ≤ u p.2)
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (P Q : C → Kernel Z (ℝ × ℝ))
    [∀ c, IsSFiniteKernel (P c)] [∀ c, IsSFiniteKernel (Q c)]
    (hlocal : ∀ᵐ z ∂μ.map a, ∀ c, z ∈ cell c →
      Vlasov.IsCoupling (P c z + Q c z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
      ∀ᵐ p ∂P c z + Q c z, p.1 ≤ p.2)
    (B : ℝ) (hmass : ∀ᵐ z ∂μ.map a, ∀ c, z ∈ cell c → Q c z univ ≤ ENNReal.ofReal B) :
    let χ := ((μ.map a) ⊗ₘ finiteCellPairKernel cell hcell P).map sameLabelPopulationPair
    ∃ ξ : Measure (X × X),
      Vlasov.IsCoupling (χ.map (Prod.map b b) + ξ) μ ν ∧
      (∀ᵐ p ∂χ.map (Prod.map b b) + ξ, u p.2 - u p.1 = dist p.1 p.2) ∧
      ξ ≤ χ.map (Prod.map b b) + ξ ∧
      ξ univ ≤ ENNReal.ofReal B + (μ.map a) (⋃ c, cell c)ᶜ := by
  classical
  obtain ⟨γ, hγ, _, hsource, htarget, hactual⟩ := exists_original_clockPair_kernel
    μ ν π hπ a u ha hu hlabel 0 (hforward.mono fun p hp ↦ sub_nonneg.mpr hp)
  let _instPairMarkov : IsMarkovKernel γ := hγ
  let _instLabelProbability : IsProbabilityMeasure (μ.map a) :=
    Measure.isProbabilityMeasure_map ha.aemeasurable
  let r := μ.map a
  let G := ⋃ c, cell c
  have hG : MeasurableSet G := MeasurableSet.iUnion hcell
  let P' := finiteCellPairKernel cell hcell P
  let Q' := finiteCellPairKernel cell hcell Q + cellComplementKernel G hG γ
  let W := P' + Q'
  have hγlegal : ∀ᵐ z ∂r,
      Vlasov.IsCoupling (γ z) (condDistrib u a μ z) (condDistrib u a ν z) ∧
      ∀ᵐ p ∂γ z, p.1 ≤ p.2 := by
    filter_upwards [hactual] with z hz
    exact ⟨hz.1, hz.2.mono fun p hp ↦ sub_nonneg.mp hp⟩
  have hwhole := finiteCellPairKernel_glue r cell hcell hdisj P Q γ
    (condDistrib u a μ) (condDistrib u a ν) hγlegal hlocal
  let Λ := (r ⊗ₘ W).map sameLabelPopulationPair
  have hΛ : Vlasov.IsCoupling Λ (μ.map (fun x ↦ (a x, u x)))
      (ν.map (fun y ↦ (a y, u y))) := by
    constructor
    · rw [show Λ = (r ⊗ₘ W).map sameLabelPopulationPair from rfl,
        Measure.map_map measurable_fst measurable_sameLabelPopulationPair]
      change (r ⊗ₘ W).map (Prod.map id Prod.fst) = _
      rw [← Measure.compProd_map measurable_fst, ← hsource]
      apply Measure.compProd_congr
      filter_upwards [hwhole] with z hz
      rw [Kernel.map_apply _ measurable_fst]
      exact hz.1.1
    · rw [show Λ = (r ⊗ₘ W).map sameLabelPopulationPair from rfl,
        Measure.map_map measurable_snd measurable_sameLabelPopulationPair]
      change (r ⊗ₘ W).map (Prod.map id Prod.snd) = _
      rw [← Measure.compProd_map measurable_snd, ← htarget]
      apply Measure.compProd_congr
      filter_upwards [hwhole] with z hz
      rw [Kernel.map_apply _ measurable_snd]
      exact hz.1.2
  have hΛforward : ∀ᵐ p ∂Λ, p.1.1 = p.2.1 ∧ p.1.2 ≤ p.2.2 := by
    apply (ae_map_iff measurable_sameLabelPopulationPair.aemeasurable
      ((measurableSet_eq_fun (measurable_fst.comp measurable_fst)
        (measurable_fst.comp measurable_snd)).inter
        (measurableSet_le (measurable_snd.comp measurable_fst)
          (measurable_snd.comp measurable_snd)))).mpr
    apply Measure.ae_compProd_of_ae_ae
      (measurable_sameLabelPopulationPair
        ((measurableSet_eq_fun (measurable_fst.comp measurable_fst)
          (measurable_fst.comp measurable_snd)).inter
          (measurableSet_le (measurable_snd.comp measurable_fst)
            (measurable_snd.comp measurable_snd))))
    filter_upwards [hwhole] with z hz
    exact hz.2.mono fun p hp ↦ ⟨rfl, hp⟩
  obtain ⟨hcoupling, hcal, _⟩ := original_calibrated_coupling_of_labelClock_inverse
    hN ha hu horder μ ν hμN hνN b hb hμinv hνinv Λ hΛ hΛforward
  let ΛQ := (r ⊗ₘ Q').map sameLabelPopulationPair
  let ξ := ΛQ.map (Prod.map b b)
  have heq : Λ.map (Prod.map b b) =
      (((r ⊗ₘ P').map sameLabelPopulationPair).map (Prod.map b b)) + ξ := by
    rw [show Λ = (r ⊗ₘ (P' + Q')).map sameLabelPopulationPair from rfl,
      Measure.compProd_add_right, Measure.map_add _ _ measurable_sameLabelPopulationPair,
      Measure.map_add _ _ (hb.prodMap hb)]
  refine ⟨ξ, ?_, ?_, Measure.le_add_left le_rfl, ?_⟩
  · rwa [← heq]
  · rwa [← heq]
  · change ((r ⊗ₘ Q').map sameLabelPopulationPair).map (Prod.map b b) univ ≤ _
    rw [Measure.map_apply (hb.prodMap hb) MeasurableSet.univ, preimage_univ,
      Measure.map_apply measurable_sameLabelPopulationPair MeasurableSet.univ, preimage_univ]
    exact finiteCellPairKernel_residual_mass_le r cell hcell hdisj Q γ B hmass


end OTSelector.Reconstruction
