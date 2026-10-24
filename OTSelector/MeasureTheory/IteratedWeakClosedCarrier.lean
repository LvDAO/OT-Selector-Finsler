import OTSelector.MeasureTheory.LocalFiniteMeasure
import OTSelector.MeasureTheory.WeakClosedCarrier
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreCarrier.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerPhysicalSceneRootedCoreCarrier`; the selected original proof blocks follow. -/
section

/-!
# MeasureTheory.IteratedWeakClosedCarrier

Conditions: The explicit weakly convergent joint laws, a continuous macro tag and vague plan, a closed carrier, positive scales tending to infinity and the actual carried-offset condition.
Objects: Shrinking tagged source offsets, bounded open source windows and the limiting alternative: tag lies in the closed carrier or the limiting plan is zero.
Proof detail: Exclude windows outside fixed closed thickenings once offsets shrink, transfer each closed law constraint by Portmanteau, then exhaust radii and let the thickening width decrease to zero; repeat for the outer limit.

## Mathematical sources

- D. H. Fremlin, *Measure Theory, Volume 4*: Section 437J(d), (f), (g) and Sections 437K–437L, narrow topology and semicontinuous evaluation. https://www1.essex.ac.uk/maths/people/fremlin/chap43.pdf#page=61
- D. H. Fremlin, *Measure Theory, Volume 4, Appendix 4A*: Section 4A2A–4A2B, pp. 6–10 (closures, Hausdorff spaces, continuity and products). https://www1.essex.ac.uk/maths/people/fremlin/chap4a.pdf#page=6
- Terence Tao, *Analysis I*: Section 6.4, Corollaries 6.4.14 (squeeze test) and 6.4.17 (zero test). https://github.com/teorth/analysis/blob/main/Analysis/Section_6_4.lean

Source relation: A closed-constraint/exhaustion corollary with an explicit finite-dimensional source projection. No target-marginal hypothesis, moment estimate or exchange of the two limit stages is required.
-/

/-! Shrinking original source-coordinate offsets force weak rooted plans to
vanish outside their original closed macroscopic carrier. Open source windows
suffice; no moment bound or target marginal assumption is needed. -/
open Set Function MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal Topology
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

section WeakClosed
variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

/-- An eventually satisfied closed original carrier survives the same weak law. -/
theorem ae_closed_set_of_physicalScene_weak_tendsto_eventually
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q)) {K : Set S} (hK : IsClosed K)
    (hmem : ∀ᶠ n in atTop, ∀ᵐ s ∂(P n : Measure S), s ∈ K) :
    ∀ᵐ s ∂(Q : Measure S), s ∈ K := by
  have hzero : (fun n ↦ (P n : Measure S) Kᶜ) =ᶠ[atTop] (fun _ ↦ 0) := hmem
  have hlim : Tendsto (fun n ↦ (P n : Measure S) Kᶜ) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' hzero.symm
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl
  change (Q : Measure S) Kᶜ ≤ atTop.liminf (fun n ↦ (P n : Measure S) Kᶜ) at hle
  exact le_antisymm (hle.trans_eq hlim.liminf_eq) bot_le
end WeakClosed

variable {ι : Type*} [Fintype ι]
local notation "V" => ι → ℝ
local notation "Edge" => ((V × ℝ) × (V × ℝ))

/-- A bounded open source window in the unchanged physical edge space. -/
def physicalSceneCoreSourceWindow (R : ℝ) : Set Edge := {e | ‖e.1.1‖ < R}

theorem isOpen_physicalSceneCoreSourceWindow (R : ℝ) :
    IsOpen (physicalSceneCoreSourceWindow (ι := ι) R) :=
  isOpen_lt (continuous_fst.fst.norm) continuous_const

/-- The unchanged original source carrier excludes every bounded rooted source
window when its macro tag lies outside the corresponding closed thickening. -/
theorem physicalSceneCoreSourceWindow_eq_zero_of_carried
    (μ : Measure Edge) {K : Set V} {tag : V} {scale R ε : ℝ}
    (hscale : 0 < scale) (hsmall : R / scale ≤ ε)
    (hcarried : ∀ᵐ e ∂μ, tag + scale⁻¹ • e.1.1 ∈ K)
    (htag : tag ∉ Metric.cthickening ε K) :
    μ (physicalSceneCoreSourceWindow R) = 0 := by
  have hnull : ∀ᵐ e ∂μ, e ∉ physicalSceneCoreSourceWindow R := by
    filter_upwards [hcarried] with e he hwindow
    have hnorm : ‖e.1.1‖ ≤ R := hwindow.le
    apply htag
    apply Metric.mem_cthickening_of_dist_le tag (tag + scale⁻¹ • e.1.1) ε K he
    have heq : tag - (tag + scale⁻¹ • e.1.1) = -(scale⁻¹ • e.1.1) := by abel
    rw [dist_eq_norm, heq, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hscale)]
    exact ((mul_le_mul_of_nonneg_left hnorm (inv_pos.mpr hscale).le).trans_eq
      (by ring)).trans hsmall
  apply measure_mono_null _ (ae_iff.mp hnull)
  intro e he
  exact fun hnot ↦ hnot he

section Limits
variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
  [OpensMeasurableSpace S] [HasOuterApproxClosed S]

omit [MeasurableSpace S] [OpensMeasurableSpace S] [HasOuterApproxClosed S] in
/-- Being outside the original closed tag carrier forces the actual plan to
vanish. This is a closed constraint on the same tagged vague scene. -/
theorem isClosed_physicalSceneCoreCarrier
    (tag : S → V) (htag : Continuous tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Continuous plan)
    {K : Set V} (hK : IsClosed K) :
    IsClosed {s | tag s ∈ K ∨ (plan s : Measure Edge) = 0} := by
  have hzero : IsClosed {s | (plan s : Measure Edge) univ ≤ 0} :=
    ((LocalFiniteMeasure.lowerSemicontinuous_measure_open isOpen_univ).comp hplan).isClosed_preimage 0
  have heq : {s | (plan s : Measure Edge) univ ≤ 0} = {s | (plan s : Measure Edge) = 0} := by
    ext s
    simp only [mem_ofPred_eq, nonpos_iff_eq_zero, Measure.measure_univ_eq_zero]
  rw [heq] at hzero
  exact (hK.preimage htag).union hzero

/-- Actual shrinking source offsets force every weak limiting plan to be zero
outside the original closed source-label carrier. The full original joint law
and all its remaining coordinates are preserved. -/
theorem ae_physicalSceneCoreCarrier_of_weak_tendsto
    (Q : ProbabilityMeasure S) (P : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (tag : S → V) (htag : Continuous tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Continuous plan)
    {K : Set V} (hK : IsClosed K) (scale : ℕ → ℝ)
    (hscale : ∀ n, 0 < scale n) (hscaleTop : Tendsto scale atTop atTop)
    (hcarried : ∀ n, ∀ᵐ s ∂(P n : Measure S),
      ∀ᵐ e ∂(plan s : Measure Edge), tag s + (scale n)⁻¹ • e.1.1 ∈ K) :
    ∀ᵐ s ∂(Q : Measure S), tag s ∈ K ∨ (plan s : Measure Edge) = 0 := by
  have hwindow (ε : ℝ) (hε : 0 < ε) (R : ℝ) :
      ∀ᵐ s ∂(Q : Measure S), tag s ∈ Metric.cthickening ε K ∨
        (plan s : Measure Edge) (physicalSceneCoreSourceWindow R) = 0 := by
    let Good : Set S := {s | tag s ∈ Metric.cthickening ε K ∨
      (plan s : Measure Edge) (physicalSceneCoreSourceWindow R) ≤ 0}
    have hGood : IsClosed Good := (Metric.isClosed_cthickening.preimage htag).union
      (((LocalFiniteMeasure.lowerSemicontinuous_measure_open
        (isOpen_physicalSceneCoreSourceWindow R)).comp hplan).isClosed_preimage 0)
    have hsmall : Tendsto (fun n ↦ R / scale n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hscaleTop
    have hmem : ∀ᶠ n in atTop, ∀ᵐ s ∂(P n : Measure S), s ∈ Good := by
      filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with n hn
      filter_upwards [hcarried n] with s hs
      by_cases ht : tag s ∈ Metric.cthickening ε K
      · exact Or.inl ht
      · exact Or.inr (physicalSceneCoreSourceWindow_eq_zero_of_carried
          (plan s : Measure Edge) (hscale n) hn.le hs ht).le
    simpa only [Good, mem_ofPred_eq, nonpos_iff_eq_zero] using
      ae_closed_set_of_physicalScene_weak_tendsto_eventually Q P hweak hGood hmem
  have hall : ∀ᵐ s ∂(Q : Measure S), ∀ k m : ℕ,
      tag s ∈ Metric.cthickening (1 / ((k : ℝ) + 1)) K ∨
        (plan s : Measure Edge) (physicalSceneCoreSourceWindow (m : ℝ)) = 0 :=
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun m ↦ hwindow _ (by positivity) _
  filter_upwards [hall] with s hs
  by_cases ht : tag s ∈ K
  · exact Or.inl ht
  · right
    have hnot : tag s ∉ closure K := by simpa only [hK.closure_eq] using ht
    have hsmall := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually
      (Metric.eventually_notMem_cthickening_of_infEDist_pos hnot)
    obtain ⟨k, hk⟩ := hsmall.exists
    have hnull (m : ℕ) : (plan s : Measure Edge) (physicalSceneCoreSourceWindow (m : ℝ)) = 0 :=
      (hs k m).resolve_left hk
    have hcover : (⋃ m : ℕ, physicalSceneCoreSourceWindow (ι := ι) (m : ℝ)) = univ := by
      apply eq_univ_of_forall
      intro e
      obtain ⟨m, hm⟩ := exists_nat_gt ‖e.1.1‖
      exact mem_iUnion.mpr ⟨m, hm⟩
    apply Measure.measure_univ_eq_zero.mp
    rw [← hcover]
    exact measure_iUnion_null hnull

/-- The same original closed core carrier survives the outer tilt limit. -/
theorem ae_physicalSceneCoreCarrier_of_iterated_weak
    (P : ℕ → ℕ → ProbabilityMeasure S) (Q : ℕ → ProbabilityMeasure S)
    (R : ProbabilityMeasure S) (φ : ℕ → ℕ → ℕ) (ψ : ℕ → ℕ)
    (hinner : ∀ ℓ, Tendsto (fun n ↦ P ℓ (φ ℓ n)) atTop (𝓝 (Q ℓ)))
    (houter : Tendsto (fun ℓ ↦ Q (ψ ℓ)) atTop (𝓝 R))
    (tag : S → V) (htag : Continuous tag)
    (plan : S → LocalFiniteMeasure Edge) (hplan : Continuous plan)
    {K : Set V} (hK : IsClosed K) (scale : ℕ → ℕ → ℝ)
    (hscale : ∀ ℓ n, 0 < scale ℓ n)
    (hscaleTop : ∀ ℓ, Tendsto (scale ℓ) atTop atTop)
    (hcarried : ∀ ℓ n, ∀ᵐ s ∂(P ℓ (φ ℓ n) : Measure S),
      ∀ᵐ e ∂(plan s : Measure Edge), tag s + (scale ℓ n)⁻¹ • e.1.1 ∈ K) :
    (∀ ℓ, ∀ᵐ s ∂(Q ℓ : Measure S), tag s ∈ K ∨ (plan s : Measure Edge) = 0) ∧
      ∀ᵐ s ∂(R : Measure S), tag s ∈ K ∨ (plan s : Measure Edge) = 0 := by
  have hQ (ℓ : ℕ) := ae_physicalSceneCoreCarrier_of_weak_tendsto
    (Q ℓ) (fun n ↦ P ℓ (φ ℓ n)) (hinner ℓ) tag htag plan hplan hK
      (scale ℓ) (hscale ℓ) (hscaleTop ℓ) (hcarried ℓ)
  exact ⟨hQ, ae_closed_set_of_physicalScene_weak_tendsto R _ houter _
    (isClosed_physicalSceneCoreCarrier tag htag plan hplan hK) (fun ℓ ↦ hQ (ψ ℓ))⟩
end Limits
end OTSelector.Reconstruction

end
end
