import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingBlockCounts
import OTSelector.Reconstruction.OriginalActualInputBoundaryLawTransfer
import OTSelector.Reconstruction.OriginalLegalWeightedReserveClockBudget

/-! The genuine original main-scene clock-block counts retain their joint
independent Poisson law on every compact physical window. -/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- Both actual physical-window array counts retain their independent Poisson
laws, with their literal unnormalized physical intensities. -/
theorem hasLaw_originalPoissonWindow_setCountPair_physical
    (q : ℕ) {U : Set (Fin q → ℝ)} (hUfin : volume U ≠ ∞) (hUpos : volume U ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {A B : Set (LegalMarkedPhysicalPoint q)} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    HasLaw (fun b ↦ (blockSetCount A b.1, blockSetCount B b.2))
      ((poissonMeasure (((((volume : Measure (Fin q → ℝ)).restrict U).prod α) A).toNNReal)).prod
        (poissonMeasure (((((volume : Measure (Fin q → ℝ)).restrict U).prod β) B).toNNReal)))
      (legalInputPoissonWindowLaw q U α β) := by
  have : IsFiniteMeasure ((volume : Measure (Fin q → ℝ)).restrict U) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hUfin.lt_top⟩
  have hmass : 0 < ((volume : Measure (Fin q → ℝ)).restrict U).real univ := by
    simpa only [measureReal_def, Measure.restrict_apply_univ] using ENNReal.toReal_pos hUpos hUfin
  let ρ := normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict U)
  have : IsProbabilityMeasure ρ := normalizedFiniteLaw_probability _ hmass
  let P := blockDataLaw (ρ.prod α) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  let R := blockDataLaw (ρ.prod β) (fun n ↦ poissonMeasure (volume U).toNNReal {n})
  have : IsProbabilityMeasure P := isProbabilityMeasure_originalPoissonBlockDataLaw _ _
  have : IsProbabilityMeasure R := isProbabilityMeasure_originalPoissonBlockDataLaw _ _
  have hi : IndepFun (fun b ↦ blockSetCount A b.1) (fun b ↦ blockSetCount B b.2)
      (legalInputPoissonWindowLaw q U α β) := by
    change IndepFun (fun b ↦ blockSetCount A b.1) (fun b ↦ blockSetCount B b.2) (P.prod R)
    exact indepFun_prod (measurable_blockSetCount hA) (measurable_blockSetCount hB)
  have : IsProbabilityMeasure (legalInputPoissonWindowLaw q U α β) := by
    change IsProbabilityMeasure (P.prod R)
    infer_instance
  exact hi.hasLaw_prod
    (hasLaw_originalPoissonWindow_sourceSetCount_physical q hUfin hUpos α β hA)
    (hasLaw_originalPoissonWindow_targetSetCount_physical q hUfin hUpos α β hB)

/-- The unchanged main scene has the actual two-color block-count law. Only
Q's true full-input law is used; zero-volume windows and null blocks are allowed. -/
theorem LegalWeightedStationaryPoissonMatching.hasLaw_originalMainPhysicalBlockCount_pair
    {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    HasLaw (fun scene ↦
      (originalMainPhysicalBlockCount K S 0 scene, originalMainPhysicalBlockCount K T 1 scene))
      ((poissonMeasure ((volume K).toNNReal * (α S).toNNReal)).prod
        (poissonMeasure ((volume K).toNNReal * (β T).toNNReal)))
      (Q.law : Measure (LegalMarkedOptimalInputScene q)) := by
  obtain ⟨R₀, _, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  obtain ⟨R, hR, hR₀, hlaw⟩ := Q.map_fullSpatialInputRestriction_eq_originalPoisson hK R₀
  let U := haarRootCube (Fin q) R
  have hKU : K ⊆ U := fun x hx ↦
    (mem_haarRootCube_iff_norm_le hR.le x).mpr ((hbound x hx).le.trans hR₀)
  have hUfin : volume U ≠ ∞ := (isCompact_Icc.measure_lt_top).ne
  have hUpos : volume U ≠ 0 := by
    rw [volume_haarRootCube (Fin q) hR.le, Fintype.card_fin]
    exact (ENNReal.ofReal_pos.mpr (pow_pos (by positivity) q)).ne'
  let W : Set (LegalColoredInputPoint q) := (K ×ˢ univ) ×ˢ univ
  let A : Set (LegalColoredInputPoint q) := (K ×ˢ S) ×ˢ {0}
  let B : Set (LegalColoredInputPoint q) := (K ×ˢ T) ×ˢ {1}
  have hA : MeasurableSet A := (hK.measurableSet.prod hS).prod (measurableSet_singleton _)
  have hB : MeasurableSet B := (hK.measurableSet.prod hT).prod (measurableSet_singleton _)
  have hW : MeasurableSet W := (hK.measurableSet.prod MeasurableSet.univ).prod MeasurableSet.univ
  let eval : Measure (LegalColoredInputPoint q) → ℕ × ℕ := fun ζ ↦
    (⌊(ζ A).toReal⌋₊, ⌊(ζ B).toReal⌋₊)
  have heval : Measurable eval :=
    ((Measure.measurable_coe hA).ennreal_toReal.nat_floor).prodMk
      ((Measure.measurable_coe hB).ennreal_toReal.nat_floor)
  have hrestrict : Measurable (fun ζ : LocalFiniteMeasure (LegalColoredInputPoint q) ↦
      (ζ : Measure (LegalColoredInputPoint q)).restrict W) := by
    apply Measure.measurable_of_measurable_coe
    intro C hC
    simpa only [Measure.restrict_apply hC, Function.comp_def] using
      (Measure.measurable_coe (hC.inter hW)).comp measurable_localFiniteMeasure_coe
  have heval_restrict (ζ : Measure (LegalColoredInputPoint q)) : eval (ζ.restrict W) = eval ζ := by
    have hAW : A ⊆ W := fun _ h ↦ ⟨⟨h.1.1, mem_univ _⟩, mem_univ _⟩
    have hBW : B ⊆ W := fun _ h ↦ ⟨⟨h.1.1, mem_univ _⟩, mem_univ _⟩
    simp only [eval, Measure.restrict_apply hA, Measure.restrict_apply hB,
      inter_eq_left.mpr hAW, inter_eq_left.mpr hBW]
  have heval_array (b : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q)) :
      eval (legalInputTwoBlockMeasure q b) = (blockSetCount (K ×ˢ S) b.1, blockSetCount (K ×ˢ T) b.2) := by
    simp only [eval, A, B, legalInputTwoBlockMeasure_sourceCount q (hK.measurableSet.prod hS),
      legalInputTwoBlockMeasure_targetCount q (hK.measurableSet.prod hT),
      ENNReal.toReal_natCast, Nat.floor_natCast]
  have he := congrArg (fun L : Measure (Measure (LegalColoredInputPoint q)) ↦ L.map eval) hlaw
  have hleft : Measurable (fun scene : LegalMarkedOptimalInputScene q ↦
      (scene.2 : Measure (LegalColoredInputPoint q)).restrict ((K ×ˢ univ) ×ˢ univ)) :=
    hrestrict.comp measurable_snd
  have hright : Measurable (fun b ↦ (legalInputTwoBlockMeasure q b).restrict ((K ×ˢ univ) ×ˢ univ)) :=
    hrestrict.comp (measurable_legalInputTwoBlockLocal q)
  rw [Measure.map_map heval hleft, Measure.map_map heval hright] at he
  change (Q.law : Measure (LegalMarkedOptimalInputScene q)).map
      (fun s ↦ eval ((s.2 : Measure (LegalColoredInputPoint q)).restrict W)) =
    (legalInputPoissonWindowLaw q U α β).map
      (fun b ↦ eval ((legalInputTwoBlockMeasure q b).restrict W)) at he
  simp only [heval_restrict, heval_array] at he
  have hr (γ : Measure ℝ) [SFinite γ] (C : Set ℝ) :
      (((volume : Measure (Fin q → ℝ)).restrict U).prod γ) (K ×ˢ C) = volume K * γ C := by
    rw [Measure.prod_prod, Measure.restrict_apply hK.measurableSet, inter_eq_left.mpr hKU]
  have hcount := hasLaw_originalPoissonWindow_setCountPair_physical q hUfin hUpos α β
    (hK.measurableSet.prod hS) (hK.measurableSet.prod hT)
  simp only [hr, ENNReal.toNNReal_mul] at hcount
  refine ⟨((measurable_originalMainPhysicalBlockCount hK.measurableSet hS 0).prodMk
    (measurable_originalMainPhysicalBlockCount hK.measurableSet hT 1)).aemeasurable, ?_⟩
  exact he.trans hcount.map_eq

end OTSelector.Reconstruction
