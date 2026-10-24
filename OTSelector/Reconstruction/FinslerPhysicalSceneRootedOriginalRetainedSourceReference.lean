import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalSourceWindowReference
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalRetainedSourceDomination

/-!
# Actual retained source references in the fixed original seed frame

Finite original population references control the retained near union of the
same global plan. Its source marginal is dominated by the original source rows;
all targets and actual restricted columns stay in place. The finite reference
is independent of the sample scale and root, and any positive scalar error
budget is attained internally without a uniform bound across auxiliary cores.
-/
open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal NNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)


variable (j : ℕ)
set_option quotPrecheck false
local notation "V" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
/-- The actual retained near union in one fixed original frame has one finite
AC source reference at every accuracy. This bound is uniform over all original
global plans with the correct source marginal, actual roots and sample scales. -/
theorem exists_original_retained_source_window_reference
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, (κ j).IsAddHaarMeasure]
    (U : Set V) (hU : MeasurableSet U) (hUfinite : volume U ≠ ⊤) :
    ∃ errorConstant : ℝ≥0∞, errorConstant ≠ ⊤ ∧
    ∀ tolerance : ℝ, 0 < tolerance →
    ∃ reference : Measure Point,
      IsFiniteMeasure reference ∧ reference.OuterRegular ∧
      reference ≪ (volume : Measure V).prod (volume : Measure ℝ) ∧
      ∀ scale : ℝ, 0 < scale → ∀ root : V,
      ∀ Γ : Measure (M × M), Γ.fst = η₀ →
      ∀ (A B : Set M) (nearRadius : ℝ) (s : Set Point), MeasurableSet s →
        (physicalSceneRootedPlan
          (Γ.restrict (D.retainedNearCarrierEvent A B nearRadius ∩
            (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
              (lambda := lambda) j ×ˢ univ)))
          (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale) u
          (scale ^ finrank ℝ (P j).seed.covector.ker) root).fst (s ∩ (U ×ˢ univ)) ≤
        reference s + ENNReal.ofReal tolerance * errorConstant := by
  classical
  let _inst : MetricSpace M := F.metricSpace
  have hdata (i : Fin D.haar.continuous.count) :
      ∃ errorConstant : ℝ≥0∞, errorConstant ≠ ⊤ ∧
      ∀ tolerance : ℝ, 0 < tolerance →
      ∃ reference : Measure Point,
        IsFiniteMeasure reference ∧ reference.OuterRegular ∧
        reference ≪ (volume : Measure V).prod (volume : Measure ℝ) ∧
        ∀ scale : ℝ, 0 < scale → ∀ root : V,
        ∀ s : Set Point, MeasurableSet s →
          (if (D.haar.continuous.coefficient i).seedIndex = j then
            ENNReal.ofReal (scale ^ finrank ℝ (P j).seed.covector.ker) *
              ((η₀.restrict (a ⁻¹' (D.haar.continuous.coefficient i).roots)).map (fun x ↦
                (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale x - root,
                  u x))) (s ∩ (U ×ˢ univ)) else 0) ≤
          reference s + ENNReal.ofReal tolerance * errorConstant := by
    by_cases hi : (D.haar.continuous.coefficient i).seedIndex = j
    · subst j
      have hbasis :
          ⇑(Module.finBasis ℝ
            (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFunL =
          ⇑(Module.finBasis ℝ
            (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker).equivFun := by
        funext w k
        rfl
      simpa only [ite_true, physicalSceneOriginalSeedScaledPosition,
        physicalSceneOriginalSeedBasisPosition, PopulationHaarPressureCore.sceneCoordinate,
        hbasis] using
        D.exists_original_core_source_window_reference hF hcomplete hu ha hinj i U hU hUfinite
    · refine ⟨0, ENNReal.zero_ne_top, fun tolerance htolerance ↦
        ⟨0, inferInstance, inferInstance, Measure.AbsolutelyContinuous.zero _, ?_⟩⟩
      intro scale hscale root s hs
      rw [ite_eq_right hi]
      exact bot_le
  choose constant hconstant data using hdata
  let errorConstant := ∑ i : Fin D.haar.continuous.count, constant i
  refine ⟨errorConstant, ENNReal.sum_ne_top.mpr (fun i _ ↦ hconstant i), ?_⟩
  intro tolerance htolerance
  choose reference hfinite hregular hac hbound using fun i ↦ data i tolerance htolerance
  let _instRefFinite : ∀ i, IsFiniteMeasure (reference i) := hfinite
  let totalReference : Measure Point := ∑ i : Fin D.haar.continuous.count, reference i
  have htotalFinite : IsFiniteMeasure totalReference := by
    dsimp only [totalReference]
    rw [← Measure.sum_fintype]
    infer_instance
  let _instTotalFinite := htotalFinite
  have htotalAC : totalReference ≪ (volume : Measure V).prod (volume : Measure ℝ) := by
    dsimp only [totalReference]
    rw [← Measure.sum_fintype]
    exact Measure.absolutelyContinuous_sum_left hac
  refine ⟨totalReference, htotalFinite, inferInstance, htotalAC, ?_⟩
  intro scale hscale root Γ hfst A B nearRadius s hs
  have hr := D.rooted_retainedNearCarrier_fixed_seed_source_test_le_sum_original_rows
    hcomplete ha Γ hfst j A B nearRadius
    (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale)
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j scale)
    hu.continuous.measurable (scale ^ finrank ℝ (P j).seed.covector.ker) root s U
  have hb := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦
    hbound i scale hscale root s hs
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hb
  have hh := hr.trans hb
  simpa only [Measure.finsetSum_apply, totalReference, errorConstant] using hh

/-- Every positive accuracy budget is attained internally by the original
finite conditional population. No quantitative relation between core accuracy,
reference partition size and the prescribed source error is assumed. -/
theorem exists_original_retained_source_window_reference_of_accuracy
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    [∀ j, (κ j).IsAddHaarMeasure]
    (U : Set V) (hU : MeasurableSet U) (hUfinite : volume U ≠ ⊤)
    (error : ℝ≥0∞) (herror : error ≠ 0) :
    ∃ reference : Measure Point,
      IsFiniteMeasure reference ∧ reference.OuterRegular ∧
      reference ≪ (volume : Measure V).prod (volume : Measure ℝ) ∧
      ∀ scale : ℝ, 0 < scale → ∀ root : V,
      ∀ Γ : Measure (M × M), Γ.fst = η₀ →
      ∀ (A B : Set M) (nearRadius : ℝ) (s : Set Point), MeasurableSet s →
        (physicalSceneRootedPlan
          (Γ.restrict (D.retainedNearCarrierEvent A B nearRadius ∩
            (physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
              (lambda := lambda) j ×ˢ univ)))
          (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j scale) u
          (scale ^ finrank ℝ (P j).seed.covector.ker) root).fst (s ∩ (U ×ˢ univ)) ≤
        reference s + error := by
  obtain ⟨constant, hconstant, hdata⟩ :=
    D.exists_original_retained_source_window_reference j hF hcomplete hu ha hinj U hU hUfinite
  obtain ⟨tolerance, htolerance, hsmall⟩ := ENNReal.exists_nnreal_pos_mul_lt hconstant herror
  obtain ⟨reference, hfinite, hregular, hac, hbound⟩ := hdata tolerance htolerance
  refine ⟨reference, hfinite, hregular, hac, ?_⟩
  intro scale hscale root Γ hfst A B nearRadius s hs
  apply (hbound scale hscale root Γ hfst A B nearRadius s hs).trans
  apply add_le_add le_rfl
  simpa only [ENNReal.ofReal_coe_nnreal] using hsmall.le

end PopulationLocalPressureCore
end OTSelector.Reconstruction
