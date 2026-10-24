import OTSelector.Probability.CavitySemidiscreteSourceMassLaw
import OTSelector.MeasureTheory.CompactProductMarginalTests

/-!
# Actual source projections remain locally finite in common weak limits

The original source probability and Haar root averaging supply every required
window moment internally. No moment or proper-projection assumption is added.
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

local instance cavitySemidiscreteSourceMarginalLimitLocalInst1 : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × A) × ((ι → ℝ) × B))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Every actual common weak limit has two locally finite source marginals.
This follows from the original source probabilities, with no energy premise. -/
theorem ae_actualRootedScene_locallyFinite_source_marginals
    {Ωn : ℕ → Type*} [∀ n, MeasurableSpace (Ωn n)]
    (m : ℕ → ℕ) (P : ∀ n, Measure (Ωn n)) [∀ n, IsProbabilityMeasure (P n)]
    (μ : ℕ → Measure ((ι → ℝ) × A)) [∀ n, IsProbabilityMeasure (μ n)]
    (p : ∀ n, Ωn n → Fin (m n + 1) → ℝ)
    (Y : ∀ n, Ωn n → Fin (m n + 1) → ((ι → ℝ) × B))
    (hY : ∀ n j, Measurable (fun ω ↦ Y n ω j))
    (aplus aminus : ∀ n, Ωn n × ((ι → ℝ) × A) → Fin (m n + 1) → ℝ)
    (hplusm : ∀ n j, Measurable (fun v ↦ aplus n v j))
    (hminusm : ∀ n j, Measurable (fun v ↦ aminus n v j))
    (hfeas : ∀ n, ∀ᵐ ω ∂P n,
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aplus n (ω, s)) ∧
      IsSemidiscreteAllocation (μ n) (p n ω) (fun s ↦ aminus n (ω, s)))
    (D : ℕ → Set (ι → ℝ)) (N : ℕ → ℝ) (hN : ∀ n, 0 < N n)
    (hD : ∀ n, volume (D n) = ENNReal.ofReal (N n))
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B)))
    (hweak : Tendsto (fun n ↦ cavityRootedLocalSceneLaw (P n) (μ n)
      (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n)
      (N n) (hN n) (D n) (hD n)) atTop (𝓝 Q)) :
    ∀ᵐ π ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B))),
      IsFiniteMeasureOnCompacts (π.1 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst ∧
      IsFiniteMeasureOnCompacts (π.2 : Measure (((ι → ℝ) × A) × ((ι → ℝ) × B))).fst := by
  let K := CompactExhaustion.choice (ι → ℝ)
  let U := fun k ↦ interior (K k) ×ˢ (univ : Set A)
  have hU : ∀ k, IsOpen (U k) := fun _ ↦ isOpen_interior.prod isOpen_univ
  have hcover : ∀ L : Set ((ι → ℝ) × A), IsCompact L → ∃ k, L ⊆ U k := by
    intro L hL
    obtain ⟨k, hk⟩ := K.exists_superset_of_isCompact (hL.image continuous_fst)
    refine ⟨k + 1, ?_⟩
    intro x hx
    exact ⟨K.subset_interior_succ k (hk (mem_image_of_mem _ hx)), mem_univ _⟩
  have hC : ∀ k, volume (interior (K k)) ≠ ⊤ := fun k ↦
    ne_top_of_le_ne_top (K.isCompact k).measure_lt_top.ne (measure_mono interior_subset)
  have hb (k n : ℕ) := cavityRootedLocalSceneLaw_sourceWindow_bounds (P n) (μ n) (p n)
    (aplus n) (aminus n) (hplusm n) (hminusm n) (Y n) (hY n) (hfeas n)
    (N n) (hN n) (D n) (hD n) (interior (K k)) isOpen_interior
  have hset (k : ℕ) : U k ×ˢ (univ : Set ((ι → ℝ) × B)) =
      {e : (((ι → ℝ) × A) × ((ι → ℝ) × B)) | e.1.1 ∈ interior (K k)} := by
    ext e
    simp [U]
  have h₀ := ae_locallyFinite_fst_of_weak_source_window_bounds Q _ hweak
    (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦ π.1) continuous_fst
    U hU hcover (fun k ↦ volume (interior (K k))) hC (fun k n ↦ by
      rw [hset]; exact (hb k n).1)
  have h₁ := ae_locallyFinite_fst_of_weak_source_window_bounds Q _ hweak
    (fun π : CavityLocalScene ((ι → ℝ) × A) ((ι → ℝ) × B) ↦ π.2) continuous_snd
    U hU hcover (fun k ↦ volume (interior (K k))) hC (fun k n ↦ by
      rw [hset]; exact (hb k n).2)
  exact h₀.and h₁

end OTSelector.Probability
