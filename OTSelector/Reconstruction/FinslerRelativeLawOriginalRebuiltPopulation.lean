import OTSelector.Transport.Coupling.PopulationClassFlow
import OTSelector.Probability.BinnedPopulation
import OTSelector.Probability.KernelClassFlowGluing

/-!
Rebuild the original calibrated physical population from retained and residual
class flows on chosen original labels. Outside flow is derived from the literal
original population coupling; original physical marginal identities and the
quantitative residual mass bound are proved in the construction.
-/

open Set Function MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false

/-- Good-label class replacement rebuilds a whole original calibrated
population and an actual deterministic residual subplan. The original outside
population supplies its own feasible class flow, rather than a Hall oracle. -/
theorem exists_original_glued_residual_population
    {X Z : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    [SecondCountableTopology X] [StandardBorelSpace X] [Nonempty X]
    [MeasurableSpace Z] [MeasurableSpace.CountablySeparated Z] [MeasurableEq Z]
    {M L : ℕ} {N : Set X} (hN : MeasurableSet N)
    {a : X → Z} {u : X → ℝ} (ha : Measurable a) (hu : Measurable u)
    (hinj : Function.Injective (fun x : N ↦ (a x.val, u x.val)))
    (horder : ∀ x ∈ N, ∀ y ∈ N,
      (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμN : ∀ᵐ x ∂μ, x ∈ N) (hνN : ∀ᵐ y ∂ν, y ∈ N)
    (π : Measure (X × X)) (hπ : Vlasov.IsCoupling π μ ν)
    (hlabel : ∀ᵐ p ∂π, a p.1 = a p.2)
    (δ : ℝ) (hgap : ∀ᵐ p ∂π, δ ≤ u p.2 - u p.1)
    (S : Fin M → Set ℝ) (T : Fin L → Set ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hT : ∀ j, MeasurableSet (T j))
    (hdS : Pairwise (Disjoint on S)) (hdT : Pairwise (Disjoint on T))
    (hcoverS : ∀ᵐ z ∂μ.map a, ∀ᵐ s ∂condDistrib u a μ z, s ∈ ⋃ i, S i)
    (hcoverT : ∀ᵐ z ∂μ.map a, ∀ᵐ t ∂condDistrib u a ν z, t ∈ ⋃ j, T j)
    (fallbackS : Fin M → ℝ) (fallbackT : Fin L → ℝ)
    (allowed : Fin M → Fin L → Prop)
    (hbins_from_gap : ∀ i j, ∀ s ∈ S i, ∀ t ∈ T j, δ ≤ t - s → allowed i j)
    (hbins_legal : ∀ i j, allowed i j → ∀ s ∈ S i, ∀ t ∈ T j, s ≤ t)
    (G : Set Z) (hG : MeasurableSet G)
    (P Q : Z → Fin M → Fin L → ℝ)
    (hmP : ∀ i j, Measurable (fun z ↦ P z i j))
    (hmQ : ∀ i j, Measurable (fun z ↦ Q z i j))
    (hPQ : ∀ᵐ z ∂μ.map a, z ∈ G →
      (∀ i j, 0 ≤ P z i j) ∧ (∀ i j, 0 ≤ Q z i j) ∧
      (∀ i, ∑ j, (P z i j + Q z i j) = (condDistrib u a μ z).real (S i)) ∧
      (∀ j, ∑ i, (P z i j + Q z i j) = (condDistrib u a ν z).real (T j)) ∧
      ∀ i j, ¬ allowed i j → P z i j = 0 ∧ Q z i j = 0)
    (B : ℝ) (hmassQ : ∀ᵐ z ∂μ.map a, z ∈ G → (∑ i, ∑ j, Q z i j) ≤ B) :
    let α := fun i ↦ normalizedActualBinKernel (condDistrib u a μ) (S i) (hS i) (fallbackS i)
    let β := fun j ↦ normalizedActualBinKernel (condDistrib u a ν) (T j) (hT j) (fallbackT j)
    let χ := sameLabelPopulationCoupling (μ.map a) (retainedClassFlowOn G P) α β
    ∃ (b : Z × ℝ → X) (ξ : Measure (X × X)), Measurable b ∧
      Vlasov.IsCoupling (χ.map (Prod.map b b) + ξ) μ ν ∧
      (∀ᵐ p ∂χ.map (Prod.map b b) + ξ, u p.2 - u p.1 = dist p.1 p.2) ∧
      ξ ≤ χ.map (Prod.map b b) + ξ ∧
      ξ univ ≤ ENNReal.ofReal B + (μ.map a) Gᶜ := by
  obtain ⟨γ, hγ, hbalance, hactual⟩ := exists_original_feasible_clockClassFlow
    μ ν π hπ a u ha hu hlabel δ hgap S T hS hT hdS hdT hcoverS hcoverT
    allowed hbins_from_gap
  let _instPairMarkov : IsMarkovKernel γ := hγ
  let _instLabelProbability : IsProbabilityMeasure (μ.map a) := Measure.isProbabilityMeasure_map ha.aemeasurable
  let A := fun z ↦ actualClockClassFlow (γ z) S T
  let P' := retainedClassFlowOn G P
  let Q' := residualClassFlowOn G A Q
  let W := fun z i j ↦ P' z i j + Q' z i j
  let α := fun i ↦ normalizedActualBinKernel (condDistrib u a μ) (S i) (hS i) (fallbackS i)
  let β := fun j ↦ normalizedActualBinKernel (condDistrib u a ν) (T j) (hT j) (fallbackT j)
  have hmA := measurable_actualClockClassFlow γ S T hS hT
  have hmP' := measurable_retainedClassFlowOn G hG P hmP
  have hmQ' := measurable_residualClassFlowOn G hG A Q hmA hmQ
  have hmW (i : Fin M) (j : Fin L) : Measurable (fun z ↦ W z i j) :=
    measurable_add.comp ((hmP' i j).prodMk (hmQ' i j))
  have hA : ∀ᵐ z ∂μ.map a,
      (∀ i j, 0 ≤ A z i j) ∧
      (∀ i, ∑ j, A z i j = (condDistrib u a μ z).real (S i)) ∧
      (∀ j, ∑ i, A z i j = (condDistrib u a ν z).real (T j)) ∧
      ∀ i j, ¬ allowed i j → A z i j = 0 :=
    hactual.mono fun z hz ↦ ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2.1⟩
  have hglue := originalClassFlow_glue_marginals (μ.map a) G allowed A P Q _ _ hA hPQ
  have hP' : ∀ᵐ z ∂μ.map a, ∀ i j, 0 ≤ P' z i j := hglue.mono fun z hz ↦ hz.1
  have hQ' : ∀ᵐ z ∂μ.map a, ∀ i j, 0 ≤ Q' z i j := hglue.mono fun z hz ↦ hz.2.1
  have hW : ∀ᵐ z ∂μ.map a, ∀ i j, 0 ≤ W z i j := by
    filter_upwards [hP', hQ'] with z hp hq
    exact fun i j ↦ add_nonneg (hp i j) (hq i j)
  obtain ⟨b, hb, hcoupling, hcal, _⟩ := exists_original_calibrated_coupling_of_clockBinFlow
    hN ha hu hinj horder μ ν hμN hνN hbalance S T hS hT hdS hdT hcoverS hcoverT
    fallbackS fallbackT W hmW hW
    (hglue.mono fun z hz ↦ hz.2.2.1) (hglue.mono fun z hz ↦ hz.2.2.2.1)
    allowed (hglue.mono fun z hz ↦ hz.2.2.2.2) hbins_legal
  let ξ := (sameLabelPopulationCoupling (μ.map a) Q' α β).map (Prod.map b b)
  have hwhole : (sameLabelPopulationCoupling (μ.map a) W α β).map (Prod.map b b) =
      (sameLabelPopulationCoupling (μ.map a) P' α β).map (Prod.map b b) + ξ := by
    rw [show W = (fun z i j ↦ P' z i j + Q' z i j) from rfl,
      sameLabelPopulationCoupling_add_ae (μ.map a) P' Q' hmP' hmQ' α β hP' hQ',
      Measure.map_add _ _ (hb.prodMap hb)]
  refine ⟨b, ξ, hb, ?_, ?_, Measure.le_add_left le_rfl, ?_⟩
  · rwa [← hwhole]
  · rwa [← hwhole]
  · have hmassA : ∀ᵐ z ∂μ.map a, (∑ i, ∑ j, A z i j) = (1 : ℝ) :=
      hactual.mono fun z hz ↦ hz.2.2.2.2.2
    have hQon : ∀ᵐ z ∂μ.map a, z ∈ G → ∀ i j, 0 ≤ Q z i j :=
      hPQ.mono fun z hz hGz ↦ (hz hGz).2.1
    have hmass := originalClassFlow_glue_residual_mass_le (μ.map a) G hG A Q hmA hmQ α β
      (hA.mono fun z hz ↦ hz.1) hQon (fun _ ↦ 1) hmassA B hmassQ
    change (sameLabelPopulationCoupling (μ.map a) Q' α β).map (Prod.map b b) univ ≤ _
    rw [Measure.map_apply (hb.prodMap hb) MeasurableSet.univ, preimage_univ]
    apply hmass.trans
    simp only [ENNReal.ofReal_one, setLIntegral_const, one_mul]
    exact add_le_add_left (mul_le_of_le_one_right' (prob_le_one (μ := μ.map a) (s := G))) _

end OTSelector.Reconstruction
