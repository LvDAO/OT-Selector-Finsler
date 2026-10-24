import OTSelector.Probability.ConditionalClockClassCoupling
import OTSelector.Transport.Calibration.FiniteClassPopulation
import OTSelector.Transport.Coupling.FiniteClockMixture

/-!
Conditions: Finite disjoint measurable label cells, actual ordered original pair kernels and local ordered pair decompositions with the same original conditional marginals; the physical reconstruction uses its displayed full-carrier inverse/order hypotheses.

Objects: Measurable cellwise pair kernels glued to the original kernel outside the cells, an exact calibrated original coupling and residual mass≤local error plus original outside-cell mass.

Proof detail: Piecewise-sum kernels on disjoint cells and retain the original kernel on their complement. Check marginals and order label by label, integrate the explicit residual mass bound and reconstruct physical coordinates through the original inverse.

References: D. H. Fremlin: 452B(b), p. 18: integrating a measurable family on a product; 452E–452F, pp. 20–21: disintegration and its integral formula; D. H. Fremlin: 452M–452N, pp. 25–26: product disintegration and the standard Borel target corollary.
Relation: A local kernel gluing and reconstruction theorem. Cells may use different finite bin types, and the missing outside-cell label mass is charged explicitly rather than discarded.
-/

/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerRelativeLawCellwisePopulation.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerRelativeLawCellwisePopulation`; the selected original proof blocks follow. -/
section

/-!
Original cells may use different finite clock-bin types. Their continuous pair
kernels glue on the unchanged original label law, with the original pair law
outside. The rebuilt physical coupling has exactly the original marginals,
and its explicit residual has mass bounded by the local split error plus the
original label mass outside the cells.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Local continuous clock kernels can use different finite class types in
separate original cells. Only their resulting pair kernels are combined. -/
def finiteCellPairKernel
    {C Z Y : Type*} [Fintype C] [MeasurableSpace Z] [MeasurableSpace Y]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Kernel Z Y) : Kernel Z Y := by
  classical
  exact ∑ c, Kernel.piecewise (hcell c) (K c) 0

instance finiteCellPairKernel_isSFinite
    {C Z Y : Type*} [Fintype C] [MeasurableSpace Z] [MeasurableSpace Y]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Kernel Z Y) [∀ c, IsSFiniteKernel (K c)] :
    IsSFiniteKernel (finiteCellPairKernel cell hcell K) := by
  classical
  unfold finiteCellPairKernel
  exact Kernel.IsSFiniteKernel.finsetSum _ fun c hc ↦ inferInstance

theorem finiteCellPairKernel_eq
    {C Z Y : Type*} [Fintype C] [MeasurableSpace Z] [MeasurableSpace Y]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell)) (K : C → Kernel Z Y)
    (c : C) {z : Z} (hz : z ∈ cell c) :
    finiteCellPairKernel cell hcell K z = K c z := by
  classical
  simp only [finiteCellPairKernel, sum_apply]
  rw [Finset.sum_eq_single c]
  · rw [Kernel.piecewise_apply, ite_eq_left hz]
  · intro c' hc' hne
    rw [Kernel.piecewise_apply, ite_eq_right
      (fun hz' ↦ disjoint_left.mp (hdisj hne) hz' hz)]
    rfl
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ c))

theorem finiteCellPairKernel_eq_zero
    {C Z Y : Type*} [Fintype C] [MeasurableSpace Z] [MeasurableSpace Y]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (K : C → Kernel Z Y) {z : Z} (hz : z ∉ ⋃ c, cell c) :
    finiteCellPairKernel cell hcell K z = 0 := by
  classical
  simp only [finiteCellPairKernel, sum_apply]
  apply Finset.sum_eq_zero
  intro c hc
  rw [Kernel.piecewise_apply, ite_eq_right (fun hzc ↦ hz (mem_iUnion.mpr ⟨c, hzc⟩))]
  rfl

/-- Keep the unchanged original pair law outside the chosen labels. -/
def cellComplementKernel {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (G : Set Z) (hG : MeasurableSet G) (γ : Kernel Z Y) : Kernel Z Y := by
  classical
  exact Kernel.piecewise hG 0 γ

instance cellComplementKernel_isSFinite
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (G : Set Z) (hG : MeasurableSet G) (γ : Kernel Z Y) [IsSFiniteKernel γ] :
    IsSFiniteKernel (cellComplementKernel G hG γ) := by
  classical
  unfold cellComplementKernel
  infer_instance

theorem cellComplementKernel_eq_zero
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (G : Set Z) (hG : MeasurableSet G) (γ : Kernel Z Y) {z : Z} (hz : z ∈ G) :
    cellComplementKernel G hG γ z = 0 := by
  classical
  exact ite_eq_left hz

theorem cellComplementKernel_eq
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    (G : Set Z) (hG : MeasurableSet G) (γ : Kernel Z Y) {z : Z} (hz : z ∉ G) :
    cellComplementKernel G hG γ z = γ z := by
  classical
  exact ite_eq_right hz

/-- Finite cell kernels with exact original conditional marginals glue with
the original pair kernel outside. No common class index or mesh is required. -/
theorem finiteCellPairKernel_glue
    {C Z : Type*} [Fintype C] [MeasurableSpace Z]
    (r : Measure Z) (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (P Q : C → Kernel Z (ℝ × ℝ))
    (γ : Kernel Z (ℝ × ℝ)) (α β : Kernel Z ℝ)
    (hγ : ∀ᵐ z ∂r, Vlasov.IsCoupling (γ z) (α z) (β z) ∧
      ∀ᵐ p ∂γ z, p.1 ≤ p.2)
    (hlocal : ∀ᵐ z ∂r, ∀ c, z ∈ cell c →
      Vlasov.IsCoupling (P c z + Q c z) (α z) (β z) ∧
      ∀ᵐ p ∂P c z + Q c z, p.1 ≤ p.2) :
    let G := ⋃ c, cell c
    let hG : MeasurableSet G := MeasurableSet.iUnion hcell
    let P' := finiteCellPairKernel cell hcell P
    let Q' := finiteCellPairKernel cell hcell Q + cellComplementKernel G hG γ
    ∀ᵐ z ∂r, Vlasov.IsCoupling ((P' + Q') z) (α z) (β z) ∧
      ∀ᵐ p ∂(P' + Q') z, p.1 ≤ p.2 := by
  classical
  dsimp only
  filter_upwards [hγ, hlocal] with z hγz hl
  by_cases hz : z ∈ ⋃ c, cell c
  · obtain ⟨c, hc⟩ := mem_iUnion.mp hz
    simpa only [add_apply, finiteCellPairKernel_eq cell hcell hdisj P c hc,
      finiteCellPairKernel_eq cell hcell hdisj Q c hc,
      cellComplementKernel_eq_zero _ _ _ hz, add_zero] using hl c hc
  · simpa only [add_apply, finiteCellPairKernel_eq_zero cell hcell P hz,
      finiteCellPairKernel_eq_zero cell hcell Q hz,
      cellComplementKernel_eq _ _ _ hz, zero_add] using hγz

/-- Residual pair mass is charged to the same original label measure. -/
theorem finiteCellPairKernel_residual_mass_le
    {C Z : Type*} [Fintype C] [MeasurableSpace Z]
    (r : Measure Z) [IsProbabilityMeasure r]
    (cell : C → Set Z) (hcell : ∀ c, MeasurableSet (cell c))
    (hdisj : Pairwise (Disjoint on cell))
    (Q : C → Kernel Z (ℝ × ℝ)) [∀ c, IsSFiniteKernel (Q c)]
    (γ : Kernel Z (ℝ × ℝ)) [IsMarkovKernel γ]
    (B : ℝ) (hmass : ∀ᵐ z ∂r, ∀ c, z ∈ cell c → Q c z univ ≤ ENNReal.ofReal B) :
    let G := ⋃ c, cell c
    let hG : MeasurableSet G := MeasurableSet.iUnion hcell
    let Q' := finiteCellPairKernel cell hcell Q + cellComplementKernel G hG γ
    (r ⊗ₘ Q') univ ≤ ENNReal.ofReal B + r Gᶜ := by
  classical
  dsimp only
  let G := ⋃ c, cell c
  have hG : MeasurableSet G := MeasurableSet.iUnion hcell
  let Q' := finiteCellPairKernel cell hcell Q + cellComplementKernel G hG γ
  change (r ⊗ₘ Q') univ ≤ ENNReal.ofReal B + r Gᶜ
  rw [Measure.compProd_apply MeasurableSet.univ]
  change (∫⁻ z, Q' z univ ∂r) ≤ _
  rw [← lintegral_add_compl (fun z ↦ Q' z univ) hG]
  have hon : ∫⁻ z in G, Q' z univ ∂r ≤ ∫⁻ _z in G, ENNReal.ofReal B ∂r := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hG, ae_restrict_of_ae hmass] with z hz hm
    obtain ⟨c, hc⟩ := mem_iUnion.mp hz
    have he : Q' z = Q c z := by
      simp only [Q', add_apply, finiteCellPairKernel_eq cell hcell hdisj Q c hc,
        cellComplementKernel_eq_zero _ _ _ hz, add_zero]
    rw [he]
    exact hm c hc
  have hoff : ∫⁻ z in Gᶜ, Q' z univ ∂r ≤ ∫⁻ _z in Gᶜ, (1 : ℝ≥0∞) ∂r := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hG.compl] with z hz
    have he : Q' z = γ z := by
      simp only [Q', add_apply, finiteCellPairKernel_eq_zero cell hcell Q hz,
        cellComplementKernel_eq _ _ _ hz, zero_add]
    rw [he, measure_univ]
  apply (add_le_add hon hoff).trans
  simp only [setLIntegral_const, one_mul]
  exact add_le_add_left (mul_le_of_le_one_right' (prob_le_one (μ := r) (s := G))) _

/-- Different original cells may use independent finite bin types and meshes.
Their actual continuous retained kernels combine to a calibrated original
physical population. The residual is an explicit submeasure of that population,
with small mass on the same original label law. -/
theorem exists_original_cellwise_residual_population
    {X Z C : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    [Fintype C] {N : Set X} (hN : MeasurableSet N)
    {a : X → Z} {u : X → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)))
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
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
    ∃ (b : Z × ℝ → X) (ξ : Measure (X × X)), Measurable b ∧
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
  obtain ⟨b, hb, hcoupling, hcal, _⟩ := exists_original_calibrated_coupling_of_labelClock
    hN ha hu hinj horder μ ν hμN hνN Λ hΛ hΛforward
  let ΛQ := (r ⊗ₘ Q').map sameLabelPopulationPair
  let ξ := ΛQ.map (Prod.map b b)
  have heq : Λ.map (Prod.map b b) =
      (((r ⊗ₘ P').map sameLabelPopulationPair).map (Prod.map b b)) + ξ := by
    rw [show Λ = (r ⊗ₘ (P' + Q')).map sameLabelPopulationPair from rfl,
      Measure.compProd_add_right, Measure.map_add _ _ measurable_sameLabelPopulationPair,
      Measure.map_add _ _ (hb.prodMap hb)]
  refine ⟨b, ξ, hb, ?_, ?_, Measure.le_add_left le_rfl, ?_⟩
  · rwa [← heq]
  · rwa [← heq]
  · change ((r ⊗ₘ Q').map sameLabelPopulationPair).map (Prod.map b b) univ ≤ _
    rw [Measure.map_apply (hb.prodMap hb) MeasurableSet.univ, preimage_univ,
      Measure.map_apply measurable_sameLabelPopulationPair MeasurableSet.univ, preimage_univ]
    exact finiteCellPairKernel_residual_mass_le r cell hcell hdisj Q γ B hmass

end OTSelector.Reconstruction

end
end
