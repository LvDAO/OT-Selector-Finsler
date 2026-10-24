import OTSelector.Reconstruction.OriginalReservePhysicalWindowSampler
import OTSelector.Reconstruction.OriginalReserveInputClockCarrier

/-! Every literal original finite reserve atom lies in its actual spatial and clock carriers. -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

/-- The normalized actual window law is carried by that same Borel window. -/
theorem ae_originalPhysicalReservePoint_mem (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : MeasurableSet K) :
    ∀ᵐ x ∂normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K), x ∈ K := by
  apply ae_iff.mpr
  change normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K) Kᶜ = 0
  rw [normalizedFiniteLaw, Measure.smul_apply,
    Measure.restrict_apply hK.compl, compl_inter_self, measure_empty, smul_zero]

/-- The original physical iid law retains every original spatial point and clock mark
inside their actual carriers, on one event for all original natural indices. -/
theorem ae_all_originalPhysicalReserveCloud_points (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    (α : Measure ℝ) [IsProbabilityMeasure α] {A : Set ℝ}
    (hα : ∀ᵐ x ∂α, x ∈ A) :
    ∀ᵐ ω ∂originalPhysicalReserveCloudLaw q K α,
      ∀ i : ℕ, (ω.2 i).1 ∈ K ∧ (ω.2 i).2 ∈ A := by
  let := isProbabilityMeasure_originalPhysicalReservePointLaw q hK hKpos
  let σ := (normalizedFiniteLaw ((volume : Measure (Fin q → ℝ)).restrict K)).prod α
  have hpoint : ∀ᵐ p ∂σ, p.1 ∈ K ∧ p.2 ∈ A :=
    (ae_fst_of_ae (ae_originalPhysicalReservePoint_mem q hK.measurableSet)).and
      (ae_snd_of_ae hα)
  have hseq : ∀ᵐ z ∂Measure.infinitePi (fun _ : ℕ ↦ σ),
      ∀ i : ℕ, (z i).1 ∈ K ∧ (z i).2 ∈ A := by
    apply ae_all_iff.mpr
    intro i
    have heval : ∀ᵐ p ∂(Measure.infinitePi (fun _ : ℕ ↦ σ)).map (fun z ↦ z i),
        p.1 ∈ K ∧ p.2 ∈ A := by
      rw [Measure.infinitePi_map_eval]
      exact hpoint
    exact ae_of_ae_map (measurable_pi_apply i).aemeasurable heval
  exact ae_snd_of_ae hseq

/-- A pointwise property of both original finite arrays holds for their colored point measure. -/
theorem originalFiniteInputArrays_ae_of_forall {q : ℕ}
    (arrays : BlockData (LegalMarkedPhysicalPoint q) × BlockData (LegalMarkedPhysicalPoint q))
    {P : LegalColoredInputPoint q → Prop}
    (hs : ∀ i, P (arrays.1.2 i, 0)) (ht : ∀ i, P (arrays.2.2 i, 1)) :
    ∀ᵐ p ∂legalInputTwoBlockMeasure q arrays, P p := by
  change (∀ᵐ p ∂(∑ i : Fin arrays.1.1, Measure.dirac (arrays.1.2 i, (0 : Fin 2))) +
    (∑ i : Fin arrays.2.1, Measure.dirac (arrays.2.2 i, (1 : Fin 2))), P p)
  rw [ae_add_measure_iff]
  constructor
  · rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro i
    simpa only [ae_dirac_eq, eventually_pure] using hs i
  · rw [← Measure.sum_fintype, Measure.ae_sum_iff]
    intro i
    simpa only [ae_dirac_eq, eventually_pure] using ht i

/-- Both actual reserve arrays, with their unchanged marks and colors, are carried
by the same compact marked window whenever their original clock laws are. -/
theorem ae_originalPhysicalReserveCloudArrays_mem (q : ℕ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) (hKpos : volume K ≠ 0)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    {A : Set ℝ} (hα : ∀ᵐ x ∂α, x ∈ A) (hβ : ∀ᵐ x ∂β, x ∈ A) :
    ∀ᵐ ω ∂originalPhysicalReserveTwoCloudLaw q K α β,
      ∀ᵐ p ∂legalInputTwoBlockMeasure q (originalPhysicalReserveCloudArrays q ω),
        p ∈ (K ×ˢ A) ×ˢ (univ : Set (Fin 2)) := by
  let := isProbabilityMeasure_originalPhysicalReservePointLaw q hK hKpos
  let : IsProbabilityMeasure (originalPhysicalReserveCloudLaw q K α) := by
    unfold originalPhysicalReserveCloudLaw
    infer_instance
  let : IsProbabilityMeasure (originalPhysicalReserveCloudLaw q K β) := by
    unfold originalPhysicalReserveCloudLaw
    infer_instance
  filter_upwards [ae_fst_of_ae (ae_all_originalPhysicalReserveCloud_points q hK hKpos α hα),
    ae_snd_of_ae (ae_all_originalPhysicalReserveCloud_points q hK hKpos β hβ)] with ω hs ht
  apply originalFiniteInputArrays_ae_of_forall
  · intro i
    exact ⟨hs i, mem_univ _⟩
  · intro i
    exact ⟨ht i, mem_univ _⟩

end OTSelector.Reconstruction
