import OTSelector.Reconstruction.OriginalQuadraticTransportQuantizationFiniteMass

/-! Finite quadratic plans lifted in physical coordinates through a measurable equivalence. -/
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section
namespace OTSelector.Reconstruction
variable {A E : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  {I J : Type*} [Fintype I] [Fintype J]
  [MeasurableSpace I] [MeasurableSpace J]
  [DiscreteMeasurableSpace I] [DiscreteMeasurableSpace J]

/-- Exact finite plans lift to the original physical laws while their literal
quadratic cost is computed in the specified Euclidean or normed coordinates. -/
theorem exists_finiteIndex_coordinate_quadratic_coupling_lift_finite_mass
    (e : A ≃ᵐ E) (μ ν : Measure A) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set A} (hK : IsCompact (e '' K))
    (hμ : ∀ᵐ z ∂μ, z ∈ K) (hν : ∀ᵐ z ∂ν, z ∈ K)
    {T : A → I} {S : A → J} (hT : Measurable T) (hS : Measurable S)
    (α : I → ℝ) (β : J → ℝ)
    (hμmap : μ.map T = finiteWeightedMeasure α)
    (hνmap : ν.map S = finiteWeightedMeasure β)
    (P : I → J → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j = α i) (hcol : ∀ j, ∑ i, P i j = β j)
    (x : I → A) (y : J → A) {h : ℝ} (hh : 0 ≤ h)
    (hTx : ∀ z ∈ K, ‖e (x (T z)) - e z‖ ≤ h)
    (hSy : ∀ z ∈ K, ‖e (y (S z)) - e z‖ ≤ h) :
    ∃ π : Measure (A × A), Vlasov.IsCoupling π μ ν ∧
      π.map (Prod.map T S) = finitePlanMeasure P ∧
      Integrable (fun z : A × A ↦ ‖e z.2 - e z.1‖ ^ 2 / 2) π ∧
      (∫ z : A × A, ‖e z.2 - e z.1‖ ^ 2 / 2 ∂π) ≤
        (∑ i, ∑ j, P i j * (‖e (y j) - e (x i)‖ ^ 2 / 2)) +
          (μ univ).toReal * (2 * Metric.diam (e '' K) * h) := by
  have hμe : ∀ᵐ z ∂μ.map e, z ∈ e '' K := e.measurableEmbedding.ae_map_iff.mpr
    (hμ.mono fun z hz ↦ ⟨z, hz, rfl⟩)
  have hνe : ∀ᵐ z ∂ν.map e, z ∈ e '' K := e.measurableEmbedding.ae_map_iff.mpr
    (hν.mono fun z hz ↦ ⟨z, hz, rfl⟩)
  have hμemap : (μ.map e).map (T ∘ e.symm) = finiteWeightedMeasure α := by
    rw [Measure.map_map (hT.comp e.symm.measurable) e.measurable]
    simpa only [Function.comp_def, e.symm_apply_apply] using hμmap
  have hνemap : (ν.map e).map (S ∘ e.symm) = finiteWeightedMeasure β := by
    rw [Measure.map_map (hS.comp e.symm.measurable) e.measurable]
    simpa only [Function.comp_def, e.symm_apply_apply] using hνmap
  have hTxe : ∀ z ∈ e '' K, ‖(e ∘ x) ((T ∘ e.symm) z) - z‖ ≤ h := by
    rintro z ⟨w, hw, rfl⟩
    simpa only [Function.comp_apply, e.symm_apply_apply] using hTx w hw
  have hSye : ∀ z ∈ e '' K, ‖(e ∘ y) ((S ∘ e.symm) z) - z‖ ≤ h := by
    rintro z ⟨w, hw, rfl⟩
    simpa only [Function.comp_apply, e.symm_apply_apply] using hSy w hw
  obtain ⟨πe, hπe, hread, hπeI, hcost⟩ :=
    exists_finiteIndex_realPlan_quadratic_coupling_lift_finite_mass
      (μ.map e) (ν.map e) hK hμe hνe (hT.comp e.symm.measurable)
      (hS.comp e.symm.measurable) α β hμemap hνemap P hP hrow hcol
      (e ∘ x) (e ∘ y) hh hTxe hSye
  let π := πe.map (Prod.map e.symm e.symm)
  have hπ : Vlasov.IsCoupling π μ ν := by
    have hp := hπe.map e.symm e.symm e.symm.measurable e.symm.measurable
    simpa only [Measure.map_map e.symm.measurable e.measurable,
      Function.comp_def, e.symm_apply_apply, Measure.map_id'] using hp
  have hπread : π.map (Prod.map T S) = finitePlanMeasure P := by
    dsimp [π]
    rw [Measure.map_map (hT.prodMap hS) (e.symm.measurable.prodMap e.symm.measurable)]
    exact hread
  have hc : Measurable (fun z : A × A ↦ ‖e z.2 - e z.1‖ ^ 2 / 2) :=
    (((e.measurable.comp measurable_snd).sub
      (e.measurable.comp measurable_fst)).norm.pow_const 2).div_const 2
  have hI : Integrable (fun z : A × A ↦ ‖e z.2 - e z.1‖ ^ 2 / 2) π := by
    dsimp [π]
    apply (integrable_map_measure hc.aestronglyMeasurable
      (e.symm.measurable.prodMap e.symm.measurable).aemeasurable).2
    change Integrable (fun z : E × E ↦ ‖e (e.symm z.2) - e (e.symm z.1)‖ ^ 2 / 2) πe
    simpa only [e.apply_symm_apply] using hπeI
  refine ⟨π, hπ, hπread, hI, ?_⟩
  have heq : (∫ z : A × A, ‖e z.2 - e z.1‖ ^ 2 / 2 ∂π) =
      ∫ z : E × E, ‖z.2 - z.1‖ ^ 2 / 2 ∂πe := by
    dsimp [π]
    rw [integral_map (e.symm.measurable.prodMap e.symm.measurable).aemeasurable
      hc.aestronglyMeasurable]
    change (∫ z : E × E, ‖e (e.symm z.2) - e (e.symm z.1)‖ ^ 2 / 2 ∂πe) = _
    simp only [e.apply_symm_apply]
  rw [heq]
  simpa only [Function.comp_apply, Measure.map_apply e.measurable MeasurableSet.univ,
    preimage_univ] using hcost

end OTSelector.Reconstruction
