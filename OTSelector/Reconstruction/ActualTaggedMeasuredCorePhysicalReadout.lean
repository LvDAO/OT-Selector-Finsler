import OTSelector.Reconstruction.ActualTaggedMeasuredCoreLsc

/-! Exact finite physical-plan readouts on arbitrary measurable tag cores.
The original joint conditional kernel, root measure, full displacement, clocks
and prefactor are retained. -/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

section RootRestriction
variable {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]

/-- A measurable tag-core restriction only intersects the original root
domain. Its original density factor is retained, including zero mass. -/
theorem cavityRootMeasure_restrict_tag_core
    (β : Measure V) (D : Set V) (N : ℝ) (tag : V → W)
    (htag : Measurable tag) (A : Set W) (hA : MeasurableSet A) :
    (cavityRootMeasure β D N).restrict (tag ⁻¹' A) =
      cavityRootMeasure β (D ∩ tag ⁻¹' A) N := by
  rw [cavityRootMeasure, Measure.restrict_smul,
    Measure.restrict_restrict (hA.preimage htag)]
  rw [inter_comm]
  rfl

/-- The original sample/root product restricted by a root tag is exactly the
same sample measure times the original root density on the intersected domain.
No finiteness hypothesis on the sample measure is required. -/
theorem prod_cavityRootMeasure_restrict_tag_core
    {Ω : Type*} [MeasurableSpace Ω]
    (Penv : Measure Ω) (β : Measure V) [SFinite β]
    (D : Set V) (N : ℝ) (tag : V → W)
    (htag : Measurable tag) (A : Set W) (hA : MeasurableSet A) :
    (Penv.prod (cavityRootMeasure β D N)).restrict (univ ×ˢ (tag ⁻¹' A)) =
      Penv.prod (cavityRootMeasure β (D ∩ tag ⁻¹' A) N) := by
  let : SFinite (cavityRootMeasure β D N) := by
    unfold cavityRootMeasure
    infer_instance
  rw [← cavityRootMeasure_restrict_tag_core β D N tag htag A hA]
  ext s hs
  rw [Measure.restrict_apply hs,
    Measure.prod_apply (hs.inter (MeasurableSet.univ.prod (hA.preimage htag))),
    Measure.prod_apply hs]
  apply lintegral_congr
  intro ξ
  rw [Measure.restrict_apply (hs.preimage measurable_prodMk_left)]
  congr 1
  ext z
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and]
end RootRestriction

section OriginalPhysical
variable {W ι M : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W] [Fintype ι] [MeasurableSpace M]
local instance taggedCorePhysicalPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance taggedCorePhysicalPlanNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩
set_option quotPrecheck false
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)

/-- Restricting the actual tagged-law readout is exactly restricting its
original sample/root law by the same root tag. The finite physical plan and
the complete clock/displacement readout are unchanged. -/
theorem lintegral_tagged_sourceWindow_restrict_tag_core_eq_original_readout
    {Ω : Type*} [MeasurableSpace Ω]
    (Penv : Measure Ω) (Γplus Γminus : Ω → Measure (M × M))
    [∀ ξ, IsFiniteMeasure (Γplus ξ)] [∀ ξ, IsFiniteMeasure (Γminus ξ)]
    (hplus : Measurable Γplus) (hminus : Measurable Γminus)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (D : Set (ι → ℝ))
    (tag : (ι → ℝ) → W) (htag : Measurable tag)
    (P : Measure (W × PairScene))
    (hlaw : P = (Penv.prod (cavityRootMeasure volume D N)).map
      (fun p ↦ (tag p.2, physicalSceneRootedLocalScene Γplus Γminus coord u N p)))
    (A : Set W) (hA : MeasurableSet A)
    {U : Set (ι → ℝ)} (hU : IsOpen U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p ∂P.restrict (A ×ˢ univ)) =
      ∫⁻ p, ENNReal.ofReal N *
        cavityRootWindowReadout (Γplus p.1) (fun e ↦ coord e.1)
          (fun e ↦ F (tag p.2, ((u e.1, u e.2), coord e.2 - coord e.1))) U p.2
        ∂(Penv.prod (cavityRootMeasure volume D N)).restrict
          (univ ×ˢ (tag ⁻¹' A)) := by
  let obs : Ω × (ι → ℝ) → W × PairScene := fun p ↦
    (tag p.2, physicalSceneRootedLocalScene Γplus Γminus coord u N p)
  have hobs : Measurable obs := ((htag.comp measurable_snd).prodMk
    (measurable_physicalSceneRootedLocalScene Γplus Γminus hplus hminus
      coord hcoord u hu N))
  have hpre : obs ⁻¹' (A ×ˢ univ) = univ ×ˢ (tag ⁻¹' A) := by
    ext p
    simp only [obs, mem_preimage, mem_prod, mem_univ, and_true, true_and]
  rw [hlaw, Measure.restrict_map hobs (hA.prod MeasurableSet.univ), hpre,
    lintegral_map
      (lowerSemicontinuous_taggedPhysicalSceneSourceWindowEnergy hU F hF).measurable hobs]
  apply lintegral_congr
  intro p
  exact setLIntegral_physicalSceneRootedPlan_energy
    (Γplus p.1) coord hcoord u hu N p.2
    (hF.measurable.comp (measurable_const.prodMk measurable_id)) U hU.measurableSet

/-- The same original conditional Palm on a measurable root-tag core is
bounded by the exact original finite physical readouts on that core. No
normalization or boundary condition is required. -/
theorem lintegral_conditional_cubePalm_restrict_tag_core_le_liminf_original_sourceWindow
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Penv : ∀ n, Measure (Ω n))
    (Γplus Γminus : ∀ n, Ω n → Measure (M × M))
    [∀ n ξ, IsFiniteMeasure (Γplus n ξ)] [∀ n ξ, IsFiniteMeasure (Γminus n ξ)]
    (hplus : ∀ n, Measurable (Γplus n)) (hminus : ∀ n, Measurable (Γminus n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (N : ℕ → ℝ) (D : ℕ → Set (ι → ℝ))
    (tag : ℕ → (ι → ℝ) → W) (htag : ∀ n, Measurable (tag n))
    (η : ProbabilityMeasure W)
    (P : ℕ → ProbabilityMeasure (W × PairScene)) (Q : ProbabilityMeasure (W × PairScene))
    (hlaw : ∀ n, (P n : Measure (W × PairScene)) =
      ((Penv n).prod (cavityRootMeasure volume (D n) (N n))).map
        (fun p ↦ (tag n p.2, physicalSceneRootedLocalScene
          (Γplus n) (Γminus n) (coord n) u (N n) p)))
    (hweak : Tendsto P atTop (𝓝 Q))
    (hmarg : ∀ n, (P n).map measurable_fst.aemeasurable = η)
    (A : Set W) (hA : MeasurableSet A)
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hsub : palmUnitCube ι ⊆ U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ w, ∫⁻ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell
        ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst.restrict A) ≤
      liminf (fun n ↦ ∫⁻ p, ENNReal.ofReal (N n) *
        cavityRootWindowReadout (Γplus n p.1) (fun e ↦ coord n e.1)
          (fun e ↦ F (tag n p.2, ((u e.1, u e.2), coord n e.2 - coord n e.1))) U p.2
        ∂((Penv n).prod (cavityRootMeasure volume (D n) (N n))).restrict
          (univ ×ˢ (tag n ⁻¹' A))) atTop := by
  have heq (n : ℕ) :=
    lintegral_tagged_sourceWindow_restrict_tag_core_eq_original_readout
      (Penv n) (Γplus n) (Γminus n) (hplus n) (hminus n)
      (coord n) (hcoord n) u hu (N n) (D n) (tag n) (htag n)
      (P n : Measure (W × PairScene)) (hlaw n) A hA hU F hF
  simpa only [heq] using
    lintegral_conditional_cubePalm_restrict_tag_core_le_liminf_tagged_sourceWindow
      η P Q hweak hmarg A hA hU hsub F hF

/-- The original measurable-core conditional Palm is bounded by the same
physical finite plans integrated first over roots in the intersected original
root domain and then over the original sample law. All clocks, full
displacements and finite prefactors remain explicit. -/
theorem lintegral_conditional_cubePalm_restrict_tag_core_le_liminf_original_tagged_sourceWindow
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (Penv : ∀ n, Measure (Ω n))
    (Γplus Γminus : ∀ n, Ω n → Measure (M × M))
    [∀ n ξ, IsFiniteMeasure (Γplus n ξ)] [∀ n ξ, IsFiniteMeasure (Γminus n ξ)]
    (hplus : ∀ n, Measurable (Γplus n)) (hminus : ∀ n, Measurable (Γminus n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (N : ℕ → ℝ) (D : ℕ → Set (ι → ℝ))
    (tag : ℕ → (ι → ℝ) → W) (htag : ∀ n, Measurable (tag n))
    (η : ProbabilityMeasure W)
    (P : ℕ → ProbabilityMeasure (W × PairScene)) (Q : ProbabilityMeasure (W × PairScene))
    (hlaw : ∀ n, (P n : Measure (W × PairScene)) =
      ((Penv n).prod (cavityRootMeasure volume (D n) (N n))).map
        (fun p ↦ (tag n p.2, physicalSceneRootedLocalScene
          (Γplus n) (Γminus n) (coord n) u (N n) p)))
    (hweak : Tendsto P atTop (𝓝 Q))
    (hmarg : ∀ n, (P n).map measurable_fst.aemeasurable = η)
    (A : Set W) (hA : MeasurableSet A)
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hsub : palmUnitCube ι ⊆ U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ w, ∫⁻ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell
        ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst.restrict A) ≤
      liminf (fun n ↦ ∫⁻ ξ, ∫⁻ root, ENNReal.ofReal (N n) *
        cavityRootWindowReadout (Γplus n ξ) (fun e ↦ coord n e.1)
          (fun e ↦ F (tag n root, ((u e.1, u e.2), coord n e.2 - coord n e.1))) U root
        ∂cavityRootMeasure volume (D n ∩ tag n ⁻¹' A) (N n) ∂Penv n) atTop := by
  apply (lintegral_conditional_cubePalm_restrict_tag_core_le_liminf_original_sourceWindow
    Penv Γplus Γminus hplus hminus coord hcoord u hu N D tag htag
    η P Q hlaw hweak hmarg A hA hU hsub F hF).trans
  exact liminf_le_liminf (Eventually.of_forall fun n ↦ by
    rw [prod_cavityRootMeasure_restrict_tag_core
      (Penv n) volume (D n) (N n) (tag n) (htag n) A hA]
    exact lintegral_prod_le _)
end OriginalPhysical

end OTSelector.Reconstruction
