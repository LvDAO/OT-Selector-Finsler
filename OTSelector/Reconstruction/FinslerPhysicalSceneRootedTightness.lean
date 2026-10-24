import OTSelector.Reconstruction.FinslerPhysicalSceneLimitClock
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedDisplacement
import OTSelector.MeasureTheory.LocalFiniteMeasureTightness
import OTSelector.Probability.JointLawTightness

/-!
# Tightness of actual rooted physical plan laws

Haar root averaging bounds each source spatial window by its volume times the
original plan mass. Compact edge tests lie in such windows, so finite expected
original mass gives tightness and one common weak subsequence for both actual
source-restricted plans. Their original environment and realized columns remain
unchanged.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Haar rooting controls source-window mass by the original finite mass. -/
theorem lintegral_physicalSceneRootedPlan_sourceWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, physicalSceneRootedPlan Γ coord u N z {e | e.1.1 ∈ U}
      ∂cavityRootMeasure volume D N) ≤ volume U * Γ univ := by
  have heq : physicalSceneLongEdgeWindow U 0 = {e | e.1.1 ∈ U} := by
    ext e
    simp [physicalSceneLongEdgeWindow]
  simp_rw [← heq, physicalSceneRootedPlan_longEdgeWindow Γ coord hcoord u hu N _ U hU 0]
  simpa using lintegral_cavityRoot_scaled_window_le volume Γ
    (fun p ↦ coord p.1) (hcoord.comp measurable_fst)
    (fun _ ↦ (1 : ℝ≥0∞)) measurable_const U hU D N hN

/-- Retaining a realized source cell can only lower Haar-averaged local mass. -/
theorem lintegral_restricted_physicalSceneRootedPlan_sourceWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ] (H : Set M)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U) :
    (∫⁻ z, physicalSceneRootedPlan (Γ.restrict (H ×ˢ univ)) coord u N z
      {e | e.1.1 ∈ U} ∂cavityRootMeasure volume D N) ≤ volume U * Γ univ := by
  exact (lintegral_physicalSceneRootedPlan_sourceWindow_le
    (Γ.restrict (H ×ˢ univ)) coord hcoord u hu N hN D U hU).trans
      (mul_le_mul_right (Measure.restrict_le_self univ) _)


/-- Original total mass controls the vague laws of actual rooted physical plans. -/
theorem isTightMeasureSet_physicalSceneRootedLocalPlan
    {I : Type*} {Ω : I → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (Γ : ∀ k, Ω k → Measure (M × M)) [∀ k w, IsFiniteMeasure (Γ k w)]
    (hΓ : ∀ k, Measurable (Γ k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (N : I → ℝ) (hN : ∀ k, 0 < N k) (D : I → Set (ι → ℝ))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hmass : ∀ k, (∫⁻ w, Γ k w univ ∂P k) ≤ C) :
    IsTightMeasureSet (range (fun k ↦
      ((P k).prod (cavityRootMeasure volume (D k) (N k))).map
        (physicalSceneRootedLocalPlan (Γ k) (coord k) u (N k)))) := by
  let K := CompactExhaustion.choice (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))
  have hbounded (n : ℕ) : ∃ R > 0, ∀ e ∈ K n, ‖e.1.1‖ < R := by
    obtain ⟨R, hR, hb⟩ := ((K.isCompact n).image
      (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
    exact ⟨R, hR, fun e he ↦ hb e.1.1 ⟨e, he, rfl⟩⟩
  choose R hR hKR using hbounded
  refine LocalFiniteMeasure.isTightMeasureSet_map_of_lintegral_localMass_le
    (fun k ↦ (P k).prod (cavityRootMeasure volume (D k) (N k)))
    (fun k ↦ physicalSceneRootedLocalPlan (Γ k) (coord k) u (N k))
    (fun k ↦ measurable_physicalSceneRootedLocalPlan (Γ k) (hΓ k)
      (coord k) (hcoord k) u hu (N k))
    (fun n ↦ interior (K n)) (fun _ ↦ isOpen_interior) ?_
    (fun n ↦ volume (Metric.ball (0 : ι → ℝ) (R n)) * C)
    (fun _ ↦ ENNReal.mul_ne_top measure_ball_lt_top.ne hC) ?_
  · intro A hA
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
    exact ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩
  · intro k n
    let ρ := cavityRootMeasure volume (D k) (N k)
    have : SFinite ρ := by
      dsimp only [ρ, cavityRootMeasure]
      infer_instance
    have hplan := measurable_physicalSceneRootedLocalPlan (Γ k) (hΓ k)
      (coord k) (hcoord k) u hu (N k)
    have hprod := lintegral_prod (μ := P k) (ν := ρ)
      ((fun q : LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ↦
        (q : Measure _) (interior (K n))) ∘
        physicalSceneRootedLocalPlan (Γ k) (coord k) u (N k))
      (((LocalFiniteMeasure.measurable_measure_open isOpen_interior).comp hplan).aemeasurable)
    dsimp only [Function.comp_def] at hprod
    rw [hprod]
    calc
      _ ≤ ∫⁻ w, ∫⁻ z, physicalSceneRootedPlan (Γ k w) (coord k) u (N k) z
          {e | e.1.1 ∈ Metric.ball 0 (R n)} ∂ρ ∂P k := by
        apply lintegral_mono
        intro w
        apply lintegral_mono
        intro z
        exact measure_mono (fun e he ↦ by
          simpa only [mem_ofPred_eq, Metric.mem_ball, dist_zero_right]
            using hKR n e (interior_subset he))
      _ ≤ ∫⁻ w, volume (Metric.ball (0 : ι → ℝ) (R n)) * Γ k w univ ∂P k := by
        apply lintegral_mono
        intro w
        exact lintegral_physicalSceneRootedPlan_sourceWindow_le (Γ k w)
          (coord k) (hcoord k) u hu (N k) (hN k) (D k)
          (Metric.ball 0 (R n)) Metric.isOpen_ball.measurableSet
      _ = volume (Metric.ball (0 : ι → ℝ) (R n)) * ∫⁻ w, Γ k w univ ∂P k :=
        lintegral_const_mul' _ _ measure_ball_lt_top.ne
      _ ≤ _ := mul_le_mul_right (hmass k) _


/-- Both original plans retain their common environment and root in one tight law. -/
theorem isTightMeasureSet_physicalSceneRestrictedRootedLocalSceneLaw
    {I : Type*} {Ω : I → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (Γplus Γminus : ∀ k, Ω k → Measure (M × M))
    [∀ k w, IsFiniteMeasure (Γplus k w)] [∀ k w, IsFiniteMeasure (Γminus k w)]
    (hplus : ∀ k, Measurable (Γplus k)) (hminus : ∀ k, Measurable (Γminus k))
    (H : I → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : I → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (N : I → ℝ) (hN : ∀ k, 0 < N k) (D : I → Set (ι → ℝ))
    (hD : ∀ k, volume (D k) = ENNReal.ofReal (N k))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hmassplus : ∀ k, (∫⁻ w, Γplus k w univ ∂P k) ≤ C)
    (hmassminus : ∀ k, (∫⁻ w, Γminus k w univ ∂P k) ≤ C) :
    IsTightMeasureSet (range (fun k ↦
      (physicalSceneRestrictedRootedLocalSceneLaw (P k) (Γplus k) (Γminus k)
        (hplus k) (hminus k) (H k) (hH k) (coord k) (hcoord k) u hu
        (N k) (hN k) (D k) (hD k) :
        Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))))) := by
  let Γp := fun k w ↦ (Γplus k w).restrict (H k ×ˢ univ)
  let Γm := fun k w ↦ (Γminus k w).restrict (H k ×ˢ univ)
  have hp (k : I) : Measurable (Γp k) :=
    measurable_physicalPlan_sourceRestriction (Γplus k) (hplus k) (H k) (hH k)
  have hm (k : I) : Measurable (Γm k) :=
    measurable_physicalPlan_sourceRestriction (Γminus k) (hminus k) (H k) (hH k)
  have hmp (k : I) : (∫⁻ w, Γp k w univ ∂P k) ≤ C :=
    (lintegral_mono (fun w ↦ Measure.restrict_le_self univ)).trans (hmassplus k)
  have hmm (k : I) : (∫⁻ w, Γm k w univ ∂P k) ≤ C :=
    (lintegral_mono (fun w ↦ Measure.restrict_le_self univ)).trans (hmassminus k)
  exact isTightMeasureSet_original_joint_of_marginals
    (fun k ↦ (P k).prod (cavityRootMeasure volume (D k) (N k)))
    (fun k ↦ physicalSceneRootedLocalPlan (Γp k) (coord k) u (N k))
    (fun k ↦ physicalSceneRootedLocalPlan (Γm k) (coord k) u (N k))
    (fun k ↦ measurable_physicalSceneRootedLocalPlan (Γp k) (hp k)
      (coord k) (hcoord k) u hu (N k))
    (fun k ↦ measurable_physicalSceneRootedLocalPlan (Γm k) (hm k)
      (coord k) (hcoord k) u hu (N k))
    (isTightMeasureSet_physicalSceneRootedLocalPlan P Γp hp coord hcoord u hu N hN D C hC hmp)
    (isTightMeasureSet_physicalSceneRootedLocalPlan P Γm hm coord hcoord u hu N hN D C hC hmm)

/-- Finite expected original mass produces a common actual weak scene subsequence. -/
theorem exists_tendsto_subseq_physicalSceneRestrictedRootedLocalSceneLaw
    {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (Γplus Γminus : ∀ k, Ω k → Measure (M × M))
    [∀ k w, IsFiniteMeasure (Γplus k w)] [∀ k w, IsFiniteMeasure (Γminus k w)]
    (hplus : ∀ k, Measurable (Γplus k)) (hminus : ∀ k, Measurable (Γminus k))
    (H : ℕ → Set M) (hH : ∀ k, MeasurableSet (H k))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ k, Measurable (coord k))
    (u : M → ℝ) (hu : Measurable u)
    (N : ℕ → ℝ) (hN : ∀ k, 0 < N k) (D : ℕ → Set (ι → ℝ))
    (hD : ∀ k, volume (D k) = ENNReal.ofReal (N k))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hmassplus : ∀ k, (∫⁻ w, Γplus k w univ ∂P k) ≤ C)
    (hmassminus : ∀ k, (∫⁻ w, Γminus k w univ ∂P k) ≤ C) :
    ∃ Q, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun k ↦ physicalSceneRestrictedRootedLocalSceneLaw (P (φ k))
        (Γplus (φ k)) (Γminus (φ k)) (hplus (φ k)) (hminus (φ k))
        (H (φ k)) (hH (φ k)) (coord (φ k)) (hcoord (φ k)) u hu
        (N (φ k)) (hN (φ k)) (D (φ k)) (hD (φ k))) atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_probabilityMeasure_of_isTight
    (fun k ↦ physicalSceneRestrictedRootedLocalSceneLaw (P k) (Γplus k) (Γminus k)
      (hplus k) (hminus k) (H k) (hH k) (coord k) (hcoord k) u hu
      (N k) (hN k) (D k) (hD k))
  exact isTightMeasureSet_physicalSceneRestrictedRootedLocalSceneLaw P Γplus Γminus
    hplus hminus H hH coord hcoord u hu N hN D hD C hC hmassplus hmassminus


end OTSelector.Reconstruction
