import OTSelector.MeasureTheory.IteratedWeakClosedCarrier

/-! Open edge masks retain their actual original core carrier in weak limits.
Only the masked part vanishes outside the original closed macro-label set;
other edges and all original joint scene coordinates are preserved. -/
open Set Function MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
variable {ι : Type*} [Fintype ι]
local notation "V" => ι → ℝ
local notation "Edge" => ((V × ℝ) × (V × ℝ))

/-- Original source carrying on a measurable edge mask excludes its bounded
rooted source windows outside the corresponding closed macro thickening. -/
theorem physicalSceneCoreSourceWindow_inter_eq_zero_of_carried
    (μ : Measure Edge) {B : Set Edge} (hB : MeasurableSet B)
    {K : Set V} {tag : V} {scale R ε : ℝ}
    (hscale : 0 < scale) (hsmall : R / scale ≤ ε)
    (hcarried : ∀ᵐ e ∂μ, e ∈ B → tag + scale⁻¹ • e.1.1 ∈ K)
    (htag : tag ∉ Metric.cthickening ε K) :
    μ (physicalSceneCoreSourceWindow R ∩ B) = 0 := by
  have hcar : ∀ᵐ e ∂μ.restrict B, tag + scale⁻¹ • e.1.1 ∈ K := by
    filter_upwards [ae_restrict_of_ae hcarried, ae_restrict_mem hB] with e he hmem
    exact he hmem
  have hzero := physicalSceneCoreSourceWindow_eq_zero_of_carried
    (μ.restrict B) hscale hsmall hcar htag
  rwa [Measure.restrict_apply (isOpen_physicalSceneCoreSourceWindow R).measurableSet] at hzero

section Limits
variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

omit [MeasurableSpace S] [OpensMeasurableSpace S] [HasOuterApproxClosed S] in
/-- Vanishing mass of an open edge mask outside a fixed closed tag carrier is
a closed constraint on the same tagged vague scene. -/
theorem isClosed_physicalSceneOpenCoreCarrier
    (tag : S → V) (htag : Continuous tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Continuous plan)
    {K : Set V} (hK : IsClosed K) {B : Set Edge} (hB : IsOpen B) :
    IsClosed {s | tag s ∈ K ∨ (plan s : Measure Edge) B = 0} := by
  have hz : IsClosed {s | (plan s : Measure Edge) B ≤ 0} :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hB).comp hplan).isClosed_preimage 0
  convert (hK.preimage htag).union hz using 1
  ext s
  simp only [mem_ofPred_eq, mem_union, mem_preimage, nonpos_iff_eq_zero]

/-- Actual shrinking source offsets on an open edge mask force the weak
limiting masked mass to vanish outside its original closed carrier. No
assumption is made about any unmasked edge or original target column. -/
theorem ae_physicalSceneOpenCoreCarrier_of_weak_tendsto
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (tag : S → V) (htag : Continuous tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Continuous plan)
    {K : Set V} (hK : IsClosed K) {B : Set Edge} (hB : IsOpen B)
    (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (hscaleTop : Tendsto scale atTop atTop)
    (hcarried : ∀ n, ∀ᵐ s ∂(P n : Measure S),
      ∀ᵐ e ∂(plan s : Measure Edge), e ∈ B → tag s + (scale n)⁻¹ • e.1.1 ∈ K) :
    ∀ᵐ s ∂(Q : Measure S), tag s ∈ K ∨ (plan s : Measure Edge) B = 0 := by
  have hwindow (ε : ℝ) (hε : 0 < ε) (R : ℝ) :
      ∀ᵐ s ∂(Q : Measure S), tag s ∈ Metric.cthickening ε K ∨
        (plan s : Measure Edge) (physicalSceneCoreSourceWindow R ∩ B) = 0 := by
    let Good : Set S := {s | tag s ∈ Metric.cthickening ε K ∨
      (plan s : Measure Edge) (physicalSceneCoreSourceWindow R ∩ B) ≤ 0}
    have hGood : IsClosed Good := (Metric.isClosed_cthickening.preimage htag).union
      (((LocalFiniteMeasure.lowerSemicontinuous_measure_open
        ((isOpen_physicalSceneCoreSourceWindow R).inter hB)).comp hplan).isClosed_preimage 0)
    have hsmall : Tendsto (fun n ↦ R / scale n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hscaleTop
    have hmem : ∀ᶠ n in atTop, ∀ᵐ s ∂(P n : Measure S), s ∈ Good := by
      filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with n hn
      filter_upwards [hcarried n] with s hs
      by_cases ht : tag s ∈ Metric.cthickening ε K
      · exact Or.inl ht
      · exact Or.inr (physicalSceneCoreSourceWindow_inter_eq_zero_of_carried
          (plan s : Measure Edge) hB.measurableSet (hscale n) hn.le hs ht).le
    simpa only [Good, mem_ofPred_eq, nonpos_iff_eq_zero] using
      ae_closed_set_of_physicalScene_weak_tendsto_eventually Q P hweak hGood hmem
  have hall : ∀ᵐ s ∂(Q : Measure S), ∀ k m : ℕ,
      tag s ∈ Metric.cthickening (1 / ((k : ℝ) + 1)) K ∨
        (plan s : Measure Edge) (physicalSceneCoreSourceWindow (m : ℝ) ∩ B) = 0 :=
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun m ↦ hwindow _ (by positivity) _
  filter_upwards [hall] with s hs
  by_cases ht : tag s ∈ K
  · exact Or.inl ht
  · right
    have hnot : tag s ∉ closure K := by simpa only [hK.closure_eq] using ht
    have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Metric.eventually_notMem_cthickening_of_infEDist_pos hnot)
    obtain ⟨k, hk⟩ := hsmall.exists
    have hnull (m : ℕ) :
        (plan s : Measure Edge) (physicalSceneCoreSourceWindow (m : ℝ) ∩ B) = 0 :=
      (hs k m).resolve_left hk
    have hcover : (⋃ m : ℕ, physicalSceneCoreSourceWindow (ι := ι) (m : ℝ) ∩ B) = B := by
      ext e
      constructor
      · intro he
        obtain ⟨m, hm⟩ := mem_iUnion.mp he
        exact hm.2
      · intro he
        obtain ⟨m, hm⟩ := exists_nat_gt ‖e.1.1‖
        exact mem_iUnion.mpr ⟨m, hm, he⟩
    rw [← hcover]
    exact measure_iUnion_null hnull

/-- The same masked closed carrier persists through the separate sample and
tilt limits, on the original joint scene with unchanged projections. -/
theorem ae_physicalSceneOpenCoreCarrier_of_iterated_weak
    (P : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S) (φ : ℕ → ℕ → ℕ) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ P ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (tag : S → V) (htag : Continuous tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Continuous plan)
    {K : Set V} (hK : IsClosed K) {B : Set Edge} (hB : IsOpen B)
    (scale : ℕ → ℕ → ℝ) (hscale : ∀ ℓ n, 0 < scale ℓ n)
    (hscaleTop : ∀ ℓ, Tendsto (scale ℓ) atTop atTop)
    (hcarried : ∀ ℓ n, ∀ᵐ s ∂(P ℓ (φ ℓ n) : Measure S),
      ∀ᵐ e ∂(plan s : Measure Edge), e ∈ B → tag s + (scale ℓ n)⁻¹ • e.1.1 ∈ K) :
    (∀ ℓ, ∀ᵐ s ∂(Q ℓ : Measure S), tag s ∈ K ∨ (plan s : Measure Edge) B = 0) ∧
      ∀ᵐ s ∂(R : Measure S), tag s ∈ K ∨ (plan s : Measure Edge) B = 0 := by
  have hQ (ℓ : ℕ) := ae_physicalSceneOpenCoreCarrier_of_weak_tendsto
    (Q ℓ) (fun n ↦ P ℓ (φ ℓ n)) (hinner ℓ) tag htag plan hplan hK hB
      (scale ℓ) (hscale ℓ) (hscaleTop ℓ) (hcarried ℓ)
  exact ⟨hQ, ae_closed_set_of_physicalScene_weak_tendsto R _ houter _
    (isClosed_physicalSceneOpenCoreCarrier tag htag plan hplan hK hB) (fun ℓ ↦ hQ (ψ ℓ))⟩
end Limits
end OTSelector.Reconstruction
