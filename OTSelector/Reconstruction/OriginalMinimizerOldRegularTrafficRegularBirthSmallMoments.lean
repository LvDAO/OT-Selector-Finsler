import OTSelector.Reconstruction.OriginalMinimizerOldRegularTrafficRegularBirthMinBound

/-! The actual endpoint-confined regular birth count event has its K s² band
moment and original-input exponential count tail. No selected-cloud law is used. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ENNReal NNReal ContDiff Matrix.Norms.Operator Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
local notation "qdim" => finrank ℝ S.covector.ker
local notation "MarkClock" => PhysicalPairPalmMark (Fin qdim) × ℝ

/-- Actual regular birth source confinement and its physical min-one bound give
the original same-band quadratic moment and its actual endpoint-count tail. -/
theorem exists_original_regularBirth_confined_goodBad_smallMoments
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) (hq : 0 < qdim)
    {gap diameter : ℝ} (hgap : 0 < gap)
    (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching qdim μ ν (D.originalFocalKinetic gap) g)
    (side : Fin 2)
    {Bedge Cedge radius : ℝ} (hBedge : 0 ≤ Bedge) (hCedge : 0 ≤ Cedge) :
    ∃ Cgood Btail : ℝ,0 ≤ Cgood ∧ 0 ≤ Btail ∧
    ∀ {s : ℝ},0 < s → ∀ {η : (Fin qdim → ℝ) → ℝ≥0∞},Measurable η →
    ∀ {Band : Set ℝ},MeasurableSet Band →
    ∀ mask : MarkClock → ℝ≥0∞,Measurable mask →
    ∀ {Small : Set (LegalMarkedOptimalInputScene qdim)},MeasurableSet Small →
    let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
    let d := fun z : MarkClock ↦ originalSeedPathOffset S w z.2 z.1
    let f := fun z : MarkClock ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
    let W := birthTrafficSpatialWindow (0:Matrix (Fin qdim) (Fin qdim) ℝ) 1 s radius
    let V := occupiedPairTrafficContributors qdim d η f
    let N := fun scene : LegalMarkedOptimalInputScene qdim ↦
      ((scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ Band) ×ˢ {side})).toReal
    let traffic := fun scene : LegalMarkedOptimalInputScene qdim ↦
      (legalMarkedCompletePathTraffic qdim d η f scene).toReal
    (∀ x m,(∫⁻ c : ℝ,η (x+d (m,c))*f (m,c)) ≤
      ENNReal.ofReal (Bedge*min 1 ((Cedge*Real.sqrt s)*
        ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖))) →
    (∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),scene ∈ Small →
      (∀ p ∈ V scene,p.1+(if side = 0 then 0 else p.2.2) ∈ W ∧
        (if side = 0 then p.2.1.1 else p.2.1.2) ∈ Band) ∧
      physicalScenePairKernel scene.1 (V scene) ≤
        (scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ Band) ×ˢ {side})) →
    ∀ {K : ℝ},0 ≤ K →
      let Good := {scene : LegalMarkedOptimalInputScene qdim | scene ∈ Small ∧ N scene ≤ K}
      MemLp (Good.indicator traffic) 2 (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
      (∫ scene,(Good.indicator traffic scene)^2
        ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim))) ≤
        Cgood*K*s^2*(∫⁻ m in {m : PhysicalPairPalmMark (Fin qdim) | (if side = 0 then m.1.1 else m.1.2) ∈ Band},
          ENNReal.ofReal (‖originalSeedPairMomentum S w m‖^2) ∂legalMarkedJointPalm qdim Q.law).toReal ∧
      MemLp ({scene | K < N scene}.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
      eLpNorm ({scene | K < N scene}.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
        ENNReal.ofReal (Btail*Real.exp (-K/4)) := by
  obtain ⟨Cv,hCv,hvol⟩ := exists_birthTrafficSpatialWindow_volume_bound
    (Matrix.PosSemidef.zero (n := Fin qdim)) (by simpa only [Fintype.card_fin] using hq) radius
  let Cgood := (Bedge*Cedge)^2*Cv*(qdim:ℝ)
  let Btail := Real.sqrt 8*Bedge*Real.exp (Cv*(Real.exp 1-1)/2)
  refine ⟨Cgood,Btail,by dsimp [Cgood];positivity,by dsimp [Btail];positivity,?_⟩
  intro s hs η hη Band hBand mask hmask Small hSmall
  dsimp only
  let T := positiveMatrixNormalizer (s • (1:Matrix (Fin qdim) (Fin qdim) ℝ))
  let d := fun z : MarkClock ↦ originalSeedPathOffset S w z.2 z.1
  let f := fun z : MarkClock ↦ ENNReal.ofReal ‖originalSeedClockOccupation S w z.2 z.1‖ * mask z
  let W := birthTrafficSpatialWindow (0:Matrix (Fin qdim) (Fin qdim) ℝ) 1 s radius
  let B := {m : PhysicalPairPalmMark (Fin qdim) | (if side = 0 then m.1.1 else m.1.2) ∈ Band}
  let V := occupiedPairTrafficContributors qdim d η f
  let N := fun scene : LegalMarkedOptimalInputScene qdim ↦
    ((scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ Band) ×ˢ {side})).toReal
  let traffic := fun scene : LegalMarkedOptimalInputScene qdim ↦
    (legalMarkedCompletePathTraffic qdim d η f scene).toReal
  intro hsingle hconf K hK
  let Good := {scene : LegalMarkedOptimalInputScene qdim | scene ∈ Small ∧ N scene ≤ K}
  have hd := measurable_originalSeedPathOffset_joint S hF hw
  have hf : Measurable f := (measurable_originalSeedClockOccupation S hF hw).norm.ennreal_ofReal.mul hmask
  have hW : MeasurableSet W := (isCompact_birthTrafficSpatialWindow _ _ _ _).measurableSet
  have hB : MeasurableSet B := by
    by_cases hside : side = 0
    · change MeasurableSet ((fun m : PhysicalPairPalmMark (Fin qdim) ↦ if side = 0 then m.1.1 else m.1.2) ⁻¹' Band)
      simpa only [hside,ite_true] using hBand.preimage (measurable_fst.fst : Measurable (fun m : PhysicalPairPalmMark (Fin qdim) ↦ m.1.1))
    · change MeasurableSet ((fun m : PhysicalPairPalmMark (Fin qdim) ↦ if side = 0 then m.1.1 else m.1.2) ⁻¹' Band)
      simpa only [hside,ite_false] using hBand.preimage (measurable_fst.snd : Measurable (fun m : PhysicalPairPalmMark (Fin qdim) ↦ m.1.2))
  have hV : ∀ scene,MeasurableSet (V scene) := fun scene ↦
    measurableSet_occupiedPairTrafficContributors d hd hη hf scene
  have hcount : Measurable N :=
    ((Measure.measurable_coe ((hW.prod hBand).prod (measurableSet_singleton side))).comp
      (measurable_localFiniteMeasure_coe.comp measurable_snd)).ennreal_toReal
  have hGood : MeasurableSet Good := hSmall.inter (measurableSet_le hcount measurable_const)
  have hvolume : volume W ≤ ENNReal.ofReal Cv := by
    simpa only [one_pow,inv_one,mul_one] using hvol zero_lt_one le_rfl hs
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  have hintensity : ((volume : Measure (Fin qdim → ℝ)).prod (if side = 0 then μ else ν))
      (W ×ˢ Band) ≤ ENNReal.ofReal Cv := by
    rw [Measure.prod_prod]
    have hprob : (if side = 0 then μ else ν) Band ≤ 1 := by
      by_cases hs : side = 0
      · simpa only [hs,ite_true] using (prob_le_one (μ := μ) (s := Band))
      · simpa only [hs,ite_false] using (prob_le_one (μ := ν) (s := Band))
    exact (mul_le_mul' hvolume hprob).trans_eq (mul_one _)
  have hNfinite : ∀ᵐ (scene : LegalMarkedOptimalInputScene qdim) ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      (scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ Band) ×ˢ {side}) < (∞ : ℝ≥0∞) := by
    fin_cases side
    · exact (Q.original_source_exp_moment_of_finite_intensity (hW.prod hBand)
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hintensity) (t := 0) (by norm_num)).1
    · exact (Q.original_target_exp_moment_of_finite_intensity (hW.prod hBand)
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hintensity) (t := 0) (by norm_num)).1
  have hsingleLinear (x) (m) : (∫⁻ c : ℝ,η (x+d (m,c))*f (m,c)) ≤
      ENNReal.ofReal ((Bedge*Cedge)*Real.sqrt s)*
        ENNReal.ofReal ‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖ := by
    apply (hsingle x m).trans
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Bedge*Cedge)*Real.sqrt s)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ Bedge*((Cedge*Real.sqrt s)*‖(Tᵀ)⁻¹ *ᵥ originalSeedPairMomentum S w m‖) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hBedge
      _ = _ := by ring
  have hsingleOne (x) (m) : (∫⁻ c : ℝ,η (x+d (m,c))*f (m,c)) ≤ ENNReal.ofReal Bedge :=
    (hsingle x m).trans (ENNReal.ofReal_le_ofReal
      (mul_le_of_le_one_right hBedge (min_le_left _ _)))
  have hg := D.goodEvent_original_anchorConfined_traffic_memLp_two_ae hF hw hgap hbounds Q
    (fun m ↦ if side = 0 then 0 else m.2) (by
      by_cases hs : side = 0
      · simp only [hs,ite_true]; exact measurable_const
      · simp only [hs,ite_false]; exact measurable_snd) (Tᵀ)⁻¹ hη mask hmask hGood.compl hW
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolume) hB V hV hK
    (show 0 ≤ (Bedge*Cedge)*Real.sqrt s by positivity) (by
      filter_upwards [hconf,hNfinite] with scene hscene hfinite
      intro hn
      have hGoodScene : scene ∈ Good := not_not.mp hn
      obtain ⟨hsource,hN⟩ := hscene hGoodScene.1
      refine ⟨?_,?_,ae_occupiedPairTrafficContributors_outside_zero d η f scene,
        ae_of_all _ (fun p ↦ hsingleLinear p.1 p.2)⟩
      · intro p hp
        exact hsource p hp
      · apply hN.trans
        rw [← ENNReal.ofReal_toReal hfinite.ne]
        exact ENNReal.ofReal_le_ofReal hGoodScene.2)
  simp only [compl_compl] at hg
  have hwreal : (volume W).toReal ≤ Cv := by
    simpa only [ENNReal.toReal_ofReal hCv.le] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hvolume
  have hmreal := D.original_regular_birthNormalizer_quadraticMoment_toReal_le hF hw hgap hbounds Q hs B
  have hpower := regularBirth_confined_quadratic_power_bound (q := qdim) (C := Bedge*Cedge)
    hs hCv.le hK ENNReal.toReal_nonneg hwreal hmreal
  have hmean := hg.2.trans hpower
  have htailData : ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene qdim)),
      scene ∈ Small → K < N scene →
      (∀ᵐ p ∂physicalScenePairKernel scene.1,p ∉ V scene →
        (∫⁻ c : ℝ,η (p.1+d (p.2,c))*f (p.2,c)) = 0) ∧
      (∀ᵐ p ∂(physicalScenePairKernel scene.1).restrict (V scene),
        (∫⁻ c : ℝ,η (p.1+d (p.2,c))*f (p.2,c)) ≤ ENNReal.ofReal Bedge) ∧
      physicalScenePairKernel scene.1 (V scene) ≤
        (scene.2 : Measure (LegalColoredInputPoint qdim)) ((W ×ˢ Band) ×ˢ {side}) := by
    filter_upwards [hconf] with scene hscene
    intro hsSmall _
    exact ⟨ae_occupiedPairTrafficContributors_outside_zero d η f scene,
      ae_of_all _ (fun p ↦ hsingleOne p.1 p.2),(hscene hsSmall).2⟩
  have ht : MemLp ({scene | K < N scene}.indicator (Small.indicator traffic)) 2
      (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ∧
      eLpNorm ({scene | K < N scene}.indicator (Small.indicator traffic)) 2
        (Q.law : Measure (LegalMarkedOptimalInputScene qdim)) ≤
        ENNReal.ofReal (Btail*Real.exp (-K/4)) := by
    fin_cases side
    · have ht := Q.original_source_countTail_completePath_ltwo_ae_on d hd hη hf (hW.prod hBand)
        hCv.le hintensity hSmall V hV (K := K) hBedge htailData
      exact ⟨ht.1,ht.2.2⟩
    · have ht := Q.original_target_countTail_completePath_ltwo_ae_on d hd hη hf (hW.prod hBand)
        hCv.le hintensity hSmall V hV (K := K) hBedge htailData
      exact ⟨ht.1,ht.2.2⟩
  refine ⟨hg.1,?_,ht.1,ht.2⟩
  simpa only [Cgood,mul_assoc,mul_left_comm,mul_comm] using hmean

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
