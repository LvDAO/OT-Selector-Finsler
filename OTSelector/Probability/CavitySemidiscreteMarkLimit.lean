import OTSelector.Probability.CavitySemidiscreteMarkWindows

/-!
# Vanishing forbidden mark mass in actual common limits

An increasing original cost gap and a uniform expected energy bound remove a
forbidden open mark event from both limiting plans. The original independent
root is retained, and no ordering of all sampled source-target pairs is assumed.
-/

open MeasureTheory Set Filter Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Probability

variable {ι A B : Type*} [Fintype ι]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
  [T2Space A] [LocallyCompactSpace A] [PseudoMetrizableSpace A]
  [SigmaCompactSpace A] [SecondCountableTopology A]
  [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B]
  [T2Space B] [LocallyCompactSpace B] [PseudoMetrizableSpace B]
  [SigmaCompactSpace B] [SecondCountableTopology B]

local instance cavitySemidiscreteMarkLimitLocalInst1 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace

omit [Fintype ι] [MeasurableSpace A] [BorelSpace A] [T2Space A]
  [LocallyCompactSpace A] [PseudoMetrizableSpace A] [SigmaCompactSpace A]
  [SecondCountableTopology A] [MeasurableSpace B] [BorelSpace B] [T2Space B]
  [LocallyCompactSpace B] [PseudoMetrizableSpace B] [SigmaCompactSpace B]
  [SecondCountableTopology B] in
/-- Rooted mark windows are open whenever both original factors are open. -/
theorem isOpen_cavityMarkWindow {U : Set (ι → ℝ)} (hU : IsOpen U)
    {E : Set (A × B)} (hE : IsOpen E) : IsOpen (cavityMarkWindow U E) :=
  (hU.preimage continuous_fst.fst).inter
    (hE.preimage (continuous_fst.snd.prodMk continuous_snd.snd))

/-- Passing to the almost-sure finite version can only decrease open-event mass. -/
theorem cavityRootedLocalSceneLaw_open_bounds
    {Ω : Type*} [MeasurableSpace Ω] {m : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Measure ((ι → ℝ) × A)) [SFinite μ]
    (aplus aminus : Ω × ((ι → ℝ) × A) → Fin (m + 1) → ℝ)
    (hplusm : ∀ j, Measurable (fun v ↦ aplus v j))
    (hminusm : ∀ j, Measurable (fun v ↦ aminus v j))
    (Y : Ω → Fin (m + 1) → ((ι → ℝ) × B))
    (hY : ∀ j, Measurable (fun ω ↦ Y ω j))
    (N : ℝ) (hN : 0 < N) (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal N)
    (U : Set (((ι → ℝ) × A) × ((ι → ℝ) × B))) (hU : IsOpen U) (b : ℝ≥0∞)
    (hp : (∫⁻ v : Ω × (ι → ℝ), cavitySpatialRootedPlan μ
      (fun s ↦ aplus (v.1, s)) (Y v.1) N v.2 U ∂P.prod (cavityRootMeasure volume D N)) ≤ b)
    (hm : (∫⁻ v : Ω × (ι → ℝ), cavitySpatialRootedPlan μ
      (fun s ↦ aminus (v.1, s)) (Y v.1) N v.2 U ∂P.prod (cavityRootMeasure volume D N)) ≤ b) :
    (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U
      ∂(cavityRootedLocalSceneLaw P μ aplus aminus hplusm hminusm Y hY N hN D hD : Measure _)) ≤ b ∧
    (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U
      ∂(cavityRootedLocalSceneLaw P μ aplus aminus hplusm hminusm Y hY N hN D hD : Measure _)) ≤ b := by
  have hm₀ : Measurable (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U) :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hU).comp continuous_fst).measurable
  have hm₁ : Measurable (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U) :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open hU).comp continuous_snd).measurable
  have hscene := measurable_cavityRootedLocalScene μ aplus aminus hplusm hminusm Y hY N
  constructor
  · change (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U
      ∂(P.prod (cavityRootMeasure volume D N)).map (cavityRootedLocalScene μ aplus aminus Y N)) ≤ b
    rw [lintegral_map hm₀ hscene]
    apply le_trans _ hp
    apply lintegral_mono
    intro v
    change (finitePlanLocalVersion (fun v : Ω × (ι → ℝ) ↦ cavitySpatialRootedPlan μ
      (fun s ↦ aplus (v.1, s)) (Y v.1) N v.2) v :
      Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U ≤ _
    rw [coe_finitePlanLocalVersion]
    split_ifs <;> simp
  · change (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B),
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U
      ∂(P.prod (cavityRootMeasure volume D N)).map (cavityRootedLocalScene μ aplus aminus Y N)) ≤ b
    rw [lintegral_map hm₁ hscene]
    apply le_trans _ hm
    apply lintegral_mono
    intro v
    change (finitePlanLocalVersion (fun v : Ω × (ι → ℝ) ↦ cavitySpatialRootedPlan μ
      (fun s ↦ aminus (v.1, s)) (Y v.1) N v.2) v :
      Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) U ≤ _
    rw [coe_finitePlanLocalVersion]
    split_ifs <;> simp

/-- Vanishing actual window expectations remove the forbidden event from both
whole limiting plans, including their noncompact source direction. -/
theorem ae_no_mark_event_of_weak_window_bounds
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))
    (Pn : ℕ → ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))
    (hweak : Tendsto Pn atTop (𝓝 Q))
    (E : Set (A × B)) (hE : IsOpen E)
    (r : ℕ → ℝ≥0∞) (hr : Tendsto r atTop (𝓝 ⊤)) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ n k : ℕ,
      (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B), (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)))
        (cavityMarkWindow (Metric.ball 0 (k + 1)) E) ∂(Pn n : Measure _)) ≤
          volume (Metric.ball (0 : ι → ℝ) (k + 1)) * C / r n ∧
      (∫⁻ π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B), (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B)))
        (cavityMarkWindow (Metric.ball 0 (k + 1)) E) ∂(Pn n : Measure _)) ≤
          volume (Metric.ball (0 : ι → ℝ) (k + 1)) * C / r n) :
    ∀ᵐ π ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      (∀ᵐ e ∂(π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))), (e.1.2, e.2.2) ∉ E) ∧
      (∀ᵐ e ∂(π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))), (e.1.2, e.2.2) ∉ E) := by
  let U (k : ℕ) := Metric.ball (0 : ι → ℝ) (k + 1)
  have hzero (k : ℕ) : ∀ᵐ π ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) (cavityMarkWindow (U k) E) = 0 ∧
      (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))) (cavityMarkWindow (U k) E) = 0 := by
    have hlim : Tendsto (fun n ↦ volume (U k) * C / r n) atTop (𝓝 0) := by
      simpa only [ENNReal.div_top] using ENNReal.Tendsto.const_div hr
        (Or.inr (ENNReal.mul_ne_top (measure_ball_lt_top.ne) hC))
    apply Filter.Eventually.and <;> apply ae_eq_zero_of_lowerSemicontinuous_lintegral_tendsto_zero Q Pn hweak
    · exact (LocalFiniteMeasure.lowerSemicontinuous_measure_open
        (isOpen_cavityMarkWindow Metric.isOpen_ball hE)).comp continuous_fst
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ ↦ zero_le) (fun n ↦ (hbound n k).1)
    · exact (LocalFiniteMeasure.lowerSemicontinuous_measure_open
        (isOpen_cavityMarkWindow Metric.isOpen_ball hE)).comp continuous_snd
    · exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
        (fun _ ↦ zero_le) (fun n ↦ (hbound n k).2)
  have hsub : {e : ((ι → ℝ) × A) × ((ι → ℝ) × B) | (e.1.2, e.2.2) ∈ E} ⊆
      ⋃ k : ℕ, cavityMarkWindow (U k) E := by
    intro e he
    obtain ⟨k, hk⟩ := exists_nat_gt ‖e.1.1‖
    apply mem_iUnion.mpr ⟨k, ?_⟩
    exact ⟨by simpa only [U, Metric.mem_ball, dist_zero_right] using
      hk.trans (lt_add_one (k : ℝ)), he⟩
  filter_upwards [ae_all_iff.mpr hzero] with π hπ
  constructor
  · simpa only [ae_iff, Set.compl_ofPred, not_not] using
      measure_mono_null hsub (measure_iUnion_null (fun k ↦ (hπ k).1))
  · simpa only [ae_iff, Set.compl_ofPred, not_not] using
      measure_mono_null hsub (measure_iUnion_null (fun k ↦ (hπ k).2))

/-- Original allocation energy and the actual increasing forbidden-event cost gap
supply legal concentration for both plans in the common weak limit. -/
theorem ae_actualRootedScene_no_mark_event_of_energy
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ω n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (aplus aminus : ∀ n, Ω n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (D : ℕ → Set (ι → ℝ)) (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    (E : Set (A × B)) (hE : IsOpen E)
    (w : ∀ n, Ω n → (((ι → ℝ) × A) × Fin (m n + 1)) → ℝ≥0∞)
    (hw : ∀ n ω, Measurable (w n ω))
    (r : ℕ → ℝ≥0∞) (hr0 : ∀ n, r n ≠ 0) (hrt : ∀ n, r n ≠ ⊤)
    (hr : Tendsto r atTop (𝓝 ⊤))
    (hgapplus : ∀ n, ∀ᵐ ω ∂P n,
      ∀ᵐ e ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aplus n (ω, s)),
        (e.1.2, (Y n ω e.2).2) ∈ E → r n ≤ w n ω e)
    (hgapminus : ∀ n, ∀ᵐ ω ∂P n,
      ∀ᵐ e ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aminus n (ω, s)),
        (e.1.2, (Y n ω e.2).2) ∈ E → r n ≤ w n ω e)
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (henergyplus : ∀ n, (∫⁻ ω, ∫⁻ e, w n ω e
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aplus n (ω, s)) ∂P n) ≤ C)
    (henergyminus : ∀ n, (∫⁻ ω, ∫⁻ e, w n ω e
      ∂semidiscreteAllocationMeasure (μ n) (fun s ↦ aminus n (ω, s)) ∂P n) ≤ C)
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))
    (hweak : Tendsto (fun n ↦ cavityRootedLocalSceneLaw (P n) (μ n)
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
      (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q)) :
    ∀ᵐ π ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      (∀ᵐ e ∂(π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))), (e.1.2, e.2.2) ∉ E) ∧
      (∀ᵐ e ∂(π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))), (e.1.2, e.2.2) ∉ E) := by
  apply ae_no_mark_event_of_weak_window_bounds Q _ hweak E hE r hr C hC
  intro n k
  apply cavityRootedLocalSceneLaw_open_bounds (P n) (μ n) (aplus n) (aminus n)
    (hplusm n) (hminusm n) (Y n) (hY n) (N n) (hN n) (D n) (hD n)
    (cavityMarkWindow (Metric.ball 0 (k + 1)) E)
    (isOpen_cavityMarkWindow Metric.isOpen_ball hE)
  · exact lintegral_original_rootedPlan_markWindow_le (P n) (μ n) (p n)
      (aplus n) (hplusm n) (Y n) (hY n) (N n) (hN n) (D n)
      (Metric.ball 0 (k + 1)) Metric.isOpen_ball.measurableSet measure_ball_lt_top.ne
      E hE.measurableSet (w n) (hw n) (r n) (hr0 n) (hrt n)
      (((hfeas n).mono fun _ h ↦ h.1).and (hgapplus n)) C (henergyplus n)
  · exact lintegral_original_rootedPlan_markWindow_le (P n) (μ n) (p n)
      (aminus n) (hminusm n) (Y n) (hY n) (N n) (hN n) (D n)
      (Metric.ball 0 (k + 1)) Metric.isOpen_ball.measurableSet measure_ball_lt_top.ne
      E hE.measurableSet (w n) (hw n) (r n) (hr0 n) (hrt n)
      (((hfeas n).mono fun _ h ↦ h.2).and (hgapminus n)) C (henergyminus n)

end OTSelector.Probability
