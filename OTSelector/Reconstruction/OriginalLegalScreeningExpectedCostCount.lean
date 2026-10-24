import OTSelector.Reconstruction.OriginalScreeningBoundaryBudgetActualCountLimit
import OTSelector.Reconstruction.OriginalStageReserveJoinedExperiment

/-! Actual main and raw-reserve counts pay arbitrary exceptional events on their joint experiment. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {q : ℕ} {α β : Measure ℝ} [IsProbabilityMeasure α] [IsProbabilityMeasure β]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}

private theorem integral_add_three {Ω : Type*} [MeasurableSpace Ω]
    (M : Measure Ω) {f g h : Ω → ℝ} (hf : Integrable f M)
    (hg : Integrable g M) (hh : Integrable h M) :
    (∫ p, f p+g p+h p ∂M) = (∫ p, f p ∂M)+(∫ p, g p ∂M)+(∫ p, h p ∂M) :=
  (integral_add (hf.add hg) hh).trans
    (congrArg (fun x : ℝ ↦ x + ∫ p, h p ∂M) (integral_add hf hg))

/-- Count all actual original main inputs and both raw reserve prefixes.
This observable is read before any deletion, screening or matching selection. -/
def originalScreeningFullExperimentCount (K : Set (Fin q → ℝ))
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) : ℝ :=
  originalScreeningActualCount K p.1 + (mSourceCount p.2 : ℝ) + (mTargetCount p.2 : ℝ)

/-- The complete actual count is nonnegative for every original observation. -/
theorem originalScreeningFullExperimentCount_nonneg (K : Set (Fin q → ℝ))
    (p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ) :
    0 ≤ originalScreeningFullExperimentCount K p :=
  add_nonneg (add_nonneg (originalScreeningActualCount_nonneg K p.1) (Nat.cast_nonneg _))
    (Nat.cast_nonneg _)

/-- The original product law provides exact total mean and a selected-event
bound even when that event observes the entire main scene and both raw clouds. -/
theorem LegalWeightedStationaryPoissonMatching.original_screening_fullExperimentCount
    (Q : LegalWeightedStationaryPoissonMatching q α β kin g) (rate : ℝ≥0)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) (hfin : volume K ≠ ∞) :
    let M := originalMainReserveExperimentLaw Q rate
    Integrable (originalScreeningFullExperimentCount K) M ∧
      (∫ p, originalScreeningFullExperimentCount K p ∂M) = 2*volume.real K+2*(rate : ℝ) ∧
      ∀ bad : Set (LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ), MeasurableSet bad →
        (∫ p, bad.indicator (originalScreeningFullExperimentCount K) p ∂M) ≤
          (2*volume.real K+2*(rate : ℝ))*M.real bad +
            2*Real.sqrt (volume.real K)+2*Real.sqrt (rate : ℝ) := by
  let P := (Q.law : Measure (LegalMarkedOptimalInputScene q))
  let Z := twoMarkedCloudLaw q ℝ ℝ α β rate
  let M := P.prod Z
  have hm := Q.originalScreeningActualCount_moments K hK hfin
  have hmi : Integrable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      originalScreeningActualCount K p.1) M := hm.2.1.comp_fst Z
  have hsi : Integrable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (mSourceCount p.2 : ℝ)) M := (integrable_mSourceCount q α β rate).comp_snd P
  have hti : Integrable (fun p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ ↦
      (mTargetCount p.2 : ℝ)) M := (integrable_mTargetCount q α β rate).comp_snd P
  have hI : Integrable (originalScreeningFullExperimentCount K) M := (hmi.add hsi).add hti
  refine ⟨hI,?_,?_⟩
  · have hmain : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
        originalScreeningActualCount K p.1 ∂M) = 2*volume.real K := by
      exact (integral_fun_fst (μ := P) (ν := Z) (originalScreeningActualCount K)).trans
        (by simpa only [measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using hm.2.2.1)
    have hsource : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
        (mSourceCount p.2 : ℝ) ∂M) = (rate : ℝ) := by
      exact (integral_fun_snd (μ := P) (ν := Z) (fun z ↦ (mSourceCount z : ℝ))).trans
        (by simpa only [P,Z,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
          using integral_mSourceCount_eq q α β rate)
    have htarget : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
        (mTargetCount p.2 : ℝ) ∂M) = (rate : ℝ) := by
      exact (integral_fun_snd (μ := P) (ν := Z) (fun z ↦ (mTargetCount z : ℝ))).trans
        (by simpa only [P,Z,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
          using integral_mTargetCount_eq q α β rate)
    change (∫ p, originalScreeningActualCount K p.1+(mSourceCount p.2 : ℝ)+
        (mTargetCount p.2 : ℝ) ∂M) = _
    rw [integral_add_three M hmi hsi hti,hmain,hsource,htarget]
    ring
  · intro bad hbad
    have hmd := integral_indicator_le_center_mass_add_abs M hmi (2*volume.real K) bad hbad
    have hsd := integral_indicator_le_center_mass_add_abs M hsi (rate : ℝ) bad hbad
    have htd := integral_indicator_le_center_mass_add_abs M hti (rate : ℝ) bad hbad
    have hmabs : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
        |originalScreeningActualCount K p.1-2*volume.real K| ∂M) ≤ 2*Real.sqrt (volume.real K) := by
      exact (integral_fun_fst (μ := P) (ν := Z)
        (fun scene ↦ |originalScreeningActualCount K scene-2*volume.real K|)).trans_le
          (by simpa only [P,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul] using hm.2.2.2)
    have hsabs : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
        |(mSourceCount p.2 : ℝ)-(rate : ℝ)| ∂M) ≤ Real.sqrt (rate : ℝ) := by
      exact (integral_fun_snd (μ := P) (ν := Z)
        (fun z ↦ |(mSourceCount z : ℝ)-(rate : ℝ)|)).trans_le
          (by simpa only [P,Z,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
            using integral_abs_mSourceCount_sub_le q α β rate)
    have htabs : (∫ p : LegalMarkedOptimalInputScene q × TwoMarkedCloudSpace q ℝ ℝ,
        |(mTargetCount p.2 : ℝ)-(rate : ℝ)| ∂M) ≤ Real.sqrt (rate : ℝ) := by
      exact (integral_fun_snd (μ := P) (ν := Z)
        (fun z ↦ |(mTargetCount z : ℝ)-(rate : ℝ)|)).trans_le
          (by simpa only [P,Z,measureReal_def,measure_univ,ENNReal.toReal_one,one_smul]
            using integral_abs_mTargetCount_sub_le q α β rate)
    have heq : bad.indicator (originalScreeningFullExperimentCount K) =
        (bad.indicator (fun p ↦ originalScreeningActualCount K p.1) +
          bad.indicator (fun p ↦ (mSourceCount p.2 : ℝ))) +
          bad.indicator (fun p ↦ (mTargetCount p.2 : ℝ)) := by
      funext p
      by_cases hp : p ∈ bad <;> simp [hp,originalScreeningFullExperimentCount]
    rw [heq]
    simp only [Pi.add_apply]
    change (∫ p, bad.indicator (fun p ↦ originalScreeningActualCount K p.1) p +
      bad.indicator (fun p ↦ (mSourceCount p.2 : ℝ)) p +
      bad.indicator (fun p ↦ (mTargetCount p.2 : ℝ)) p ∂M) ≤ _
    rw [integral_add_three M (hmi.indicator hbad) (hsi.indicator hbad) (hti.indicator hbad)]
    dsimp only [originalMainReserveExperimentLaw] at *
    linarith

end OTSelector.Reconstruction
