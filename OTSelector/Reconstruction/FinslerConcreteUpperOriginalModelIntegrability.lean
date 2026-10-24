import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelCoreBounds
import OTSelector.Reconstruction.MarkedStationaryValueLegalRegularity
/-! The physical forward-core upper estimate applies to the exact Q/U choices
already used by the original population and its canonical optimizer. -/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 300000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
namespace OTSelector.Reconstruction.PartialMatching

/-- Finite legal values need an absolute bound only at their used edges. -/
theorem integrable_legalValue_of_ae_allowed_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {m n : ℕ} (graph : Ω → Finset (Fin m × Fin n))
    (hgraph : ∀ S, MeasurableSet {sample | graph sample = S})
    (score : Ω → Fin m → Fin n → ℝ)
    (hscore : ∀ j k, Measurable (fun sample ↦ score sample j k))
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ᵐ sample ∂P, ∀ j k, (j,k) ∈ graph sample → |score sample j k| ≤ B) :
    Integrable (fun sample ↦ legalMaximumValue (graph sample) (score sample)) P := by
  have hm := measurable_legalMaximumValue graph hgraph score hscore
  apply (integrable_const (μ := P) ((m : ℝ) * B)).mono' hm.aestronglyMeasurable
  filter_upwards [hbound] with sample hs
  rw [Real.norm_eq_abs]
  have hv := abs_legalMaximumValue_le_of_allowed (graph sample) (score sample) hs
  have hcard : legalMaximumCard (graph sample) ≤ m :=
    (legalMaximumCard_le_min (graph sample)).trans (min_le_left m n)
  exact hv.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hB)

end OTSelector.Reconstruction.PartialMatching
namespace OTSelector.Reconstruction.PopulationLocalPressureCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Literal original physical model values on a gated cloud are integrable.
Only retained vertices need lie in the actual compact original root core. -/
theorem integrable_originalClockClass_legalValue
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (classify : ℝ → Fin Q.count) (hclassify : Measurable classify) (f : M × M →ᵇ ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {m n : ℕ} (xs : Fin m → Ω → M) (ys : Fin n → Ω → M)
    (hxs : ∀ j, Measurable (xs j)) (hys : ∀ k, Measurable (ys k))
    (activeS : Ω → Fin m → Prop) (activeT : Ω → Fin n → Prop)
    (hAm : ∀ j, MeasurableSet {sample | activeS sample j})
    (hBm : ∀ k, MeasurableSet {sample | activeT sample k})
    (hsource : ∀ᵐ sample ∂P, ∀ j, activeS sample j → a (xs j sample) ∈ (D.haar.continuous.coefficient i).roots)
    (htarget : ∀ᵐ sample ∂P, ∀ k, activeT sample k → a (ys k sample) ∈ (D.haar.continuous.coefficient i).roots)
    {scale : ℝ} (hscale : 0 ≤ scale) (tilt : ℝ) :
    let graph : Ω → Finset (Fin m × Fin n) := fun sample ↦ Finset.univ.filter (fun e : Fin m × Fin n ↦
      activeS sample e.1 ∧ activeT sample e.2 ∧
        D.originalClockClassAllowed i Q classify (xs e.1 sample) (ys e.2 sample))
    Integrable (fun sample ↦ PartialMatching.legalMaximumValue (graph sample) (fun j k ↦
      scale * D.originalClockClassKinetic i Q ref classify (xs j sample) (ys k sample) +
      tilt * D.originalClockClassProbe i Q ref classify f (xs j sample) (ys k sample))) P := by
  classical
  obtain ⟨B,hB,hedge⟩ := D.exists_originalClockClass_physical_edge_bound i Q ref classify f
  obtain ⟨hlegal,hkin,hprobe,hscore⟩ :=
    D.measurable_originalClockClass_model hF hcomplete hu ha hinj i Q ref classify hclassify f
  let graph : Ω → Finset (Fin m × Fin n) := fun sample ↦ Finset.univ.filter (fun e : Fin m × Fin n ↦
    activeS sample e.1 ∧ activeT sample e.2 ∧
      D.originalClockClassAllowed i Q classify (xs e.1 sample) (ys e.2 sample))
  let score : Ω → Fin m → Fin n → ℝ := fun sample j k ↦
    scale * D.originalClockClassKinetic i Q ref classify (xs j sample) (ys k sample) +
    tilt * D.originalClockClassProbe i Q ref classify f (xs j sample) (ys k sample)
  have hmgraph : Measurable graph := by
    apply measurable_finset_iff.mpr
    intro e
    apply measurableSet_setOfPred.mp
    have heq : {sample | e ∈ graph sample} =
        {sample | activeS sample e.1} ∩ {sample | activeT sample e.2} ∩
          {sample | D.originalClockClassAllowed i Q classify (xs e.1 sample) (ys e.2 sample)} := by
      ext sample
      simp only [graph, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [heq]
    exact ((hAm e.1).inter (hBm e.2)).inter (hlegal.preimage ((hxs e.1).prodMk (hys e.2)))
  have hmScore : ∀ j k, Measurable (fun sample ↦ score sample j k) := by
    intro j k
    have h := (hscore scale tilt).comp ((hxs j).prodMk (hys k))
    simpa only [Function.comp_def, score] using h
  change Integrable (fun sample ↦ PartialMatching.legalMaximumValue (graph sample) (score sample)) P
  apply PartialMatching.integrable_legalValue_of_ae_allowed_bound P graph
    (fun S ↦ (measurableSet_singleton S).preimage hmgraph) score hmScore
    (B := scale * B + |tilt| * ‖f‖)
    (add_nonneg (mul_nonneg hscale hB) (mul_nonneg (abs_nonneg tilt) (norm_nonneg f)))
  filter_upwards [hsource,htarget] with sample hs ht
  intro j k hjk
  obtain ⟨hSj,hTk,_⟩ := (Finset.mem_filter.mp hjk).2
  exact hedge (xs j sample) (ys k sample) (hs j hSj) (ht k hTk) scale hscale tilt

end OTSelector.Reconstruction.PopulationLocalPressureCore
