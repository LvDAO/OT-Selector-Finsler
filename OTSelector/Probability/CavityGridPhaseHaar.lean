import OTSelector.Probability.CavityCanonicalGridPhase
import Mathlib.Probability.ConditionalProbability

/-! The original Ioc phase law is invariant under physical spatial rerooting. -/
open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
noncomputable section
namespace OTSelector.Probability
variable (ι : Type*) [Fintype ι] (ell : ℝ) [h : Fact (0 < ell)]

/-- Normalized actual Lebesgue restriction to the existing Ioc grid phase cell. -/
def cavityGridPhaseLaw : Measure (ι → ℝ) :=
  (volume : Measure (ι → ℝ))[|cavityGridPhaseCell ι ell]

instance cavityGridPhaseLaw_probability : IsProbabilityMeasure (cavityGridPhaseLaw ι ell) := by
  apply cond_isProbabilityMeasure_of_finite
  · rw [volume_cavityGridPhaseCell]
    exact pow_ne_zero _ (ne_of_gt (ENNReal.ofReal_pos.mpr h.out))
  · rw [volume_cavityGridPhaseCell]
    finiteness

omit [Fintype ι] in
theorem measurable_cavityGridPhaseReroot_joint :
    Measurable (fun p : (ι → ℝ) × (ι → ℝ) ↦ cavityGridPhaseReroot ι ell p.1 p.2) :=
  (measurable_cavityGridCanonicalPhase ι ell).comp (measurable_snd.sub measurable_fst)

/-- Exact unnormalized Haar preservation, using the actual phase cell as a
fundamental domain of the same original coordinate lattice. -/
theorem measurePreserving_cavityGridPhaseReroot_restrict (v : ι → ℝ) :
    MeasurePreserving (cavityGridPhaseReroot ι ell v)
      (volume.restrict (cavityGridPhaseCell ι ell))
      (volume.restrict (cavityGridPhaseCell ι ell)) := by
  let D := cavityGridPhaseCell ι ell
  let C := cavityGridCanonicalPhase ι ell
  let T : (ι → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.subRight v
  have hC : Measurable C := measurable_cavityGridCanonicalPhase ι ell
  have hD : IsAddFundamentalDomain (CavityGridLattice ι ell) D volume :=
    isAddFundamentalDomain_cavityGridPhaseCell ι ell h.out
  have hDT : IsAddFundamentalDomain (CavityGridLattice ι ell) (T '' D) volume := by
    apply hD.image_of_equiv T.toEquiv
      (measurePreserving_add_right (volume : Measure (ι → ℝ)) v).quasiMeasurePreserving
      (Equiv.refl (CavityGridLattice ι ell))
    intro g x
    ext i
    change (g i : ℝ) + x i - v i = (g i : ℝ) + (x i - v i)
    ring
  have hmaps : (volume.restrict (T '' D)).map C = (volume.restrict D).map C := by
    ext B hB
    rw [Measure.map_apply hC hB, Measure.map_apply hC hB,
      Measure.restrict_apply (hC hB), Measure.restrict_apply (hC hB)]
    apply (hD.measure_set_eq hDT (hC hB) _).symm
    intro g
    ext x
    change C (g +ᵥ x) ∈ B ↔ C x ∈ B
    dsimp only [C]
    rw [cavityGridCanonicalPhase_vadd]
  have hidentity : (volume.restrict D).map C = volume.restrict D := by
    have hae : C =ᵐ[volume.restrict D] id :=
      ae_restrict_of_forall_mem (measurableSet_cavityGridPhaseCell ι ell)
        (fun x hx ↦ cavityGridCanonicalPhase_of_mem ι ell hx)
    rw [Measure.map_congr hae, Measure.map_id]
  have hT : MeasurePreserving T (volume : Measure (ι → ℝ)) volume :=
    measurePreserving_sub_right volume v
  refine ⟨hC.comp T.measurable, ?_⟩
  change (volume.restrict D).map (C ∘ T) = volume.restrict D
  rw [← Measure.map_map hC T.measurable,
    (hT.restrict_image_emb T.measurableEmbedding D).map_eq, hmaps, hidentity]

/-- The actual normalized grid phase remains Haar after any physical reroot. -/
theorem measurePreserving_cavityGridPhaseReroot (v : ι → ℝ) :
    MeasurePreserving (cavityGridPhaseReroot ι ell v)
      (cavityGridPhaseLaw ι ell) (cavityGridPhaseLaw ι ell) :=
  (measurePreserving_cavityGridPhaseReroot_restrict ι ell v).smul_measure
    ((volume : Measure (ι → ℝ)) (cavityGridPhaseCell ι ell))⁻¹

/-- The original normalized phase counts all translated cell gains with
exactly the inverse physical cell-volume factor. -/
theorem lintegral_cavityGridPhaseLaw_periodization
    (W : (ι → ℝ) → ℝ≥0∞) (hW : Measurable W) :
    (∫⁻ u, ∑' g : CavityGridLattice ι ell, W (g +ᵥ u) ∂cavityGridPhaseLaw ι ell) =
      (ENNReal.ofReal ell ^ Fintype.card ι)⁻¹ * ∫⁻ x, W x := by
  rw [cavityGridPhaseLaw, ProbabilityTheory.cond, lintegral_smul_measure,
    lintegral_cavityGrid_periodization ι ell h.out W hW, volume_cavityGridPhaseCell, smul_eq_mul]

omit [Fintype ι] in
/-- The same actual spatial cell, including its Ioc boundary convention,
is transported to the reindexed cell after physical rerooting. -/
theorem mem_cavityGridCube_reroot_iff
    (g : CavityGridLattice ι ell) (u v x : ι → ℝ) :
    x - v ∈ cavityGridCube ι ell
      ((g + cavityGridCanonicalOffset ι ell (u - v)) +ᵥ cavityGridPhaseReroot ι ell v u) ↔
      x ∈ cavityGridCube ι ell (g +ᵥ u) := by
  rw [cavityGrid_reindex_base]
  change (x - v) - ((g +ᵥ u) - v) ∈ cavityGridPhaseCell ι ell ↔ _
  have heq : (x - v) - ((g +ᵥ u) - v) = x - (g +ᵥ u) := by
    ext i
    change x i - v i - ((g i : ℝ) + u i - v i) = x i - ((g i : ℝ) + u i)
    ring
  rw [heq]
  rfl

end OTSelector.Probability
