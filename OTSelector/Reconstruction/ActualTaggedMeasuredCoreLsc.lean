import OTSelector.MeasureTheory.FixedMarginalRestrictedWeak
import OTSelector.Reconstruction.OriginalTaggedPalmEnergyLiminf

/-! Arbitrary measurable tag cores preserve lower-semicontinuous energy under
the same joint weak limit with fixed first marginal. All restrictions retain
their original finite mass. -/

open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option maxHeartbeats 1500000
set_option linter.unusedSectionVars false

section FiniteWeak
variable {S : Type*} [MeasurableSpace S] [TopologicalSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- The finite-measure Portmanteau open bound for measures of the same finite
mass, including zero mass. -/
theorem finiteMeasure_le_liminf_measure_open_of_tendsto_same_mass
    (Q : FiniteMeasure S) (P : ℕ → FiniteMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (hmass : ∀ n, (P n : Measure S) univ = (Q : Measure S) univ)
    {U : Set S} (hU : IsOpen U) :
    (Q : Measure S) U ≤ liminf (fun n ↦ (P n : Measure S) U) atTop := by
  have hclosed := FiniteMeasure.limsup_measure_closed_le_of_tendsto hweak
    hU.isClosed_compl
  have hQ : (Q : Measure S) U =
      (Q : Measure S) univ - (Q : Measure S) Uᶜ := by
    simpa only [compl_compl] using
      measure_compl hU.measurableSet.compl (measure_ne_top (Q : Measure S) Uᶜ)
  have hP (n : ℕ) : (P n : Measure S) U =
      (Q : Measure S) univ - (P n : Measure S) Uᶜ := by
    simpa only [compl_compl, hmass n] using
      measure_compl hU.measurableSet.compl (measure_ne_top (P n : Measure S) Uᶜ)
  rw [hQ]
  simp_rw [hP]
  have hkey := antitone_const_tsub.map_limsup_of_continuousAt (F := atTop)
    (fun n ↦ (P n : Measure S) Uᶜ)
    (ENNReal.continuous_sub_left (measure_ne_top (Q : Measure S) univ)).continuousAt
  have hsub : (Q : Measure S) univ - (Q : Measure S) Uᶜ ≤
      (Q : Measure S) univ - limsup (fun n ↦ (P n : Measure S) Uᶜ) atTop :=
    antitone_const_tsub hclosed
  exact hsub.trans_eq hkey

/-- Every nonnegative LSC observable passes to an unnormalized finite weak
limit when the original finite masses agree. Infinite energies are allowed. -/
theorem lintegral_lsc_le_liminf_of_finite_weak_tendsto_same_mass
    (Q : FiniteMeasure S) (P : ℕ → FiniteMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (hmass : ∀ n, (P n : Measure S) univ = (Q : Measure S) univ)
    (F : S → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ s, F s ∂(Q : Measure S)) ≤
      liminf (fun n ↦ ∫⁻ s, F s ∂(P n : Measure S)) atTop := by
  let trunc : ℕ → S → ℝ≥0∞ := fun n s ↦ min (n : ℝ≥0∞) (F s)
  let realTrunc : ℕ → S → ℝ := fun n s ↦
    ENNReal.truncateToReal (n : ℝ≥0∞) (F s)
  have hfinite (n : ℕ) (s : S) : min (n : ℝ≥0∞) (F s) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (min_le_left _ _)
  have hcast (n : ℕ) (s : S) : ENNReal.ofReal (realTrunc n s) = trunc n s :=
    ENNReal.ofReal_toReal (hfinite n s)
  have hreal (n : ℕ) : LowerSemicontinuous (realTrunc n) :=
    (ENNReal.continuous_truncateToReal (by finiteness)).comp_lowerSemicontinuous hF
      (ENNReal.monotone_truncateToReal (by finiteness))
  have htrunc (n : ℕ) : Measurable (trunc n) := measurable_const.min hF.measurable
  have hmono : Monotone trunc := fun m n hmn s ↦
    min_le_min (by exact_mod_cast hmn) le_rfl
  have hsup (s : S) : (⨆ n : ℕ, trunc n s) = F s := by
    change (⨆ n : ℕ, (n : ℝ≥0∞) ⊓ F s) = F s
    rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]
  have hbound (n : ℕ) : (∫⁻ s, trunc n s ∂(Q : Measure S)) ≤
      liminf (fun k ↦ ∫⁻ s, trunc n s ∂(P k : Measure S)) atTop := by
    have h := lintegral_ofReal_lsc_le_liminf_of_open_bounds (Q : Measure S)
      (fun k ↦ (P k : Measure S)) (realTrunc n) (hreal n)
      (fun _ ↦ ENNReal.truncateToReal_nonneg)
      (fun U hU ↦ finiteMeasure_le_liminf_measure_open_of_tendsto_same_mass
        Q P hweak hmass hU)
    simpa only [hcast] using h
  calc
    (∫⁻ s, F s ∂(Q : Measure S)) = ∫⁻ s, ⨆ n : ℕ, trunc n s ∂(Q : Measure S) :=
      lintegral_congr fun s ↦ (hsup s).symm
    _ = ⨆ n : ℕ, ∫⁻ s, trunc n s ∂(Q : Measure S) := lintegral_iSup htrunc hmono
    _ ≤ liminf (fun k ↦ ∫⁻ s, F s ∂(P k : Measure S)) atTop :=
      iSup_le fun n ↦ (hbound n).trans (liminf_le_liminf
        (Eventually.of_forall fun k ↦ lintegral_mono fun s ↦ min_le_right _ _))
end FiniteWeak

section MeasuredCore
variable {W S : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W]
  [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]

/-- Restriction to a measurable tag core has exactly its fixed first-marginal
mass. No boundary or positive-mass hypothesis occurs. -/
theorem measure_tag_core_eq_of_first_marginal
    (η : ProbabilityMeasure W) (R : ProbabilityMeasure (W × S))
    (hmarg : R.map measurable_fst.aemeasurable = η)
    (A : Set W) (hA : MeasurableSet A) :
    (R : Measure (W × S)) (A ×ˢ univ) = (η : Measure W) A := by
  have hmap : (R : Measure (W × S)).map Prod.fst = (η : Measure W) :=
    congrArg (fun μ : ProbabilityMeasure W ↦ (μ : Measure W)) hmarg
  rw [← hmap, Measure.map_apply measurable_fst hA]
  congr 1
  ext p
  simp only [mem_prod, mem_univ, and_true, mem_preimage]

/-- An arbitrary measurable tag core preserves full LSC energy in the original
joint weak limit with fixed first marginal. Both sides retain their original
mass; positive-measure boundaries are allowed. -/
theorem lintegral_lsc_restrict_tag_core_le_liminf_of_fixed_first_marginal
    (η : ProbabilityMeasure W)
    (Rn : ℕ → ProbabilityMeasure (W × S)) (R : ProbabilityMeasure (W × S))
    (hweak : Tendsto Rn atTop (𝓝 R))
    (hmarg : ∀ n, (Rn n).map measurable_fst.aemeasurable = η)
    (A : Set W) (hA : MeasurableSet A)
    (F : W × S → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ p, F p ∂(R : Measure (W × S)).restrict (A ×ˢ univ)) ≤
      liminf (fun n ↦ ∫⁻ p, F p
        ∂(Rn n : Measure (W × S)).restrict (A ×ˢ univ)) atTop := by
  have hmapped := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    Rn R hweak (continuous_fst : Continuous (Prod.fst : W × S → W))
  simp_rw [hmarg] at hmapped
  have hR : R.map measurable_fst.aemeasurable = η :=
    tendsto_nhds_unique hmapped tendsto_const_nhds
  apply lintegral_lsc_le_liminf_of_finite_weak_tendsto_same_mass
    (R.toFiniteMeasure.restrict (A ×ˢ univ))
    (fun n ↦ (Rn n).toFiniteMeasure.restrict (A ×ˢ univ))
    (fixed_first_marginal_restrict_tendsto_of_weak η Rn R hweak hmarg A hA) _ F hF
  intro n
  change ((Rn n : Measure (W × S)).restrict (A ×ˢ univ)) univ =
    ((R : Measure (W × S)).restrict (A ×ˢ univ)) univ
  simp only [Measure.restrict_apply_univ]
  rw [measure_tag_core_eq_of_first_marginal η (Rn n) (hmarg n) A hA,
    measure_tag_core_eq_of_first_marginal η R hR A hA]
end MeasuredCore

section TaggedPalm
variable {W ι : Type*} [TopologicalSpace W] [PolishSpace W]
  [MeasurableSpace W] [BorelSpace W] [Fintype ι]
local instance taggedMeasuredCorePlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance taggedMeasuredCorePlanNonempty : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0, inferInstance⟩⟩
set_option quotPrecheck false
local notation "PairScene" => CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)

/-- Exact disintegration on a measurable tag core keeps the original joint
law's conditional kernel and the original restricted first marginal. -/
theorem lintegral_conditional_cubePalm_restrict_tag_core
    (ρ : Measure (W × PairScene)) [IsFiniteMeasure ρ]
    (A : Set W) (hA : MeasurableSet A)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ w, ∫⁻ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell (ρ.condKernel w)) ∂ρ.fst.restrict A) =
      ∫⁻ p, taggedPhysicalSceneSourceWindowEnergy (palmUnitCube ι) F p
        ∂ρ.restrict (A ×ˢ univ) := by
  calc
    _ = ∫⁻ w in A, ∫⁻ scene, ∫⁻ e in
        {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) |
          e.1.1 ∈ palmUnitCube ι}, F (w, (physicalPairAnchor e).2)
          ∂(scene.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
          ∂ρ.condKernel w ∂ρ.fst := by
      apply lintegral_congr
      intro w
      exact lintegral_cubePalm_physicalScenePairCampbell (ρ.condKernel w)
        (hF.comp (measurable_const.prodMk measurable_id))
    _ = _ := Measure.setLIntegral_condKernel_univ_right
      (measurable_tagged_physicalScene_sourceUnit_readout hF) hA

/-- Measurable tag-core restriction preserves the LSC actual source-window
readout under the same joint weak law and its fixed first marginal. -/
theorem lintegral_tagged_sourceWindow_restrict_tag_core_le_liminf_of_weak
    (η : ProbabilityMeasure W)
    (P : ℕ → ProbabilityMeasure (W × PairScene)) (Q : ProbabilityMeasure (W × PairScene))
    (hweak : Tendsto P atTop (𝓝 Q))
    (hmarg : ∀ n, (P n).map measurable_fst.aemeasurable = η)
    (A : Set W) (hA : MeasurableSet A)
    {U : Set (ι → ℝ)} (hU : IsOpen U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p
      ∂(Q : Measure (W × PairScene)).restrict (A ×ˢ univ)) ≤
      liminf (fun n ↦ ∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p
        ∂(P n : Measure (W × PairScene)).restrict (A ×ˢ univ)) atTop :=
  lintegral_lsc_restrict_tag_core_le_liminf_of_fixed_first_marginal
    η P Q hweak hmarg A hA _
      (lowerSemicontinuous_taggedPhysicalSceneSourceWindowEnergy hU F hF)

/-- The same original conditional paired-edge Palm on any measurable tag core
is bounded by its own finite tagged source-window energies. The kernel is the
original joint limit's kernel, and the outer measure is its restricted first
marginal, without a boundary condition or a mass normalization. -/
theorem lintegral_conditional_cubePalm_restrict_tag_core_le_liminf_tagged_sourceWindow
    (η : ProbabilityMeasure W)
    (P : ℕ → ProbabilityMeasure (W × PairScene)) (Q : ProbabilityMeasure (W × PairScene))
    (hweak : Tendsto P atTop (𝓝 Q))
    (hmarg : ∀ n, (P n).map measurable_fst.aemeasurable = η)
    (A : Set W) (hA : MeasurableSet A)
    {U : Set (ι → ℝ)} (hU : IsOpen U) (hsub : palmUnitCube ι ⊆ U)
    (F : W × PhysicalPairPalmMark ι → ℝ≥0∞) (hF : LowerSemicontinuous F) :
    (∫⁻ w, ∫⁻ m, F (w, m)
      ∂cubePalm ι (physicalScenePairCampbell
        ((Q : Measure (W × PairScene)).condKernel w))
      ∂(Q : Measure (W × PairScene)).fst.restrict A) ≤
      liminf (fun n ↦ ∫⁻ p, taggedPhysicalSceneSourceWindowEnergy U F p
        ∂(P n : Measure (W × PairScene)).restrict (A ×ˢ univ)) atTop := by
  rw [lintegral_conditional_cubePalm_restrict_tag_core
    (Q : Measure (W × PairScene)) A hA F hF.measurable]
  apply le_trans _
    (lintegral_tagged_sourceWindow_restrict_tag_core_le_liminf_of_weak
      η P Q hweak hmarg A hA hU F hF)
  apply lintegral_mono
  intro p
  exact lintegral_mono_set (fun e he ↦ hsub he)
end TaggedPalm

end OTSelector.Reconstruction
