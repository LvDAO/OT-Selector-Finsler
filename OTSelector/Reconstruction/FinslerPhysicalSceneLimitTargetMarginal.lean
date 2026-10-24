import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetMass
import OTSelector.MeasureTheory.IteratedWeakTargetMassTail

/-!
# Actual iterated scene target marginals are locally finite

The exact original feasible global allocations and Haar window bounds produce
local finiteness of both full target projections after both weak-limit stages.
The original random restricted column masses remain unchanged throughout.
-/

open Set Function Filter MeasureTheory ProbabilityTheory OTSelector.Probability
open scoped Topology ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]
variable (base : (ι → ℝ) × ℝ)
local instance physicalSceneOuterTargetMarginalStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance physicalSceneOuterTargetMarginalConfigTopology : TopologicalSpace (LocalConfiguration base) := vagueTopology _
local instance physicalSceneOuterTargetMarginalConfigBorel : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance physicalSceneOuterTargetMarginalConfigPolish : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance physicalSceneOuterTargetMarginalPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := LocalFiniteMeasure.instPolishSpace

/-- Actual original feasible global allocations produce locally finite full
target projections under the successive sample-size and tilt-index limits. -/
theorem ae_iterated_actualAllocationRootedScene_target_locallyFinite
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (m : ℕ → ℕ) (Penv : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (Penv n)]
    (μ : Measure M) [IsFiniteMeasure μ]
    (aplus aminus : ∀ _k n, Ω n → M → Fin (m n + 1) → ℝ)
    (hplus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aplus k n z.1 z.2 j))
    (hminus : ∀ k n j, Measurable (fun z : Ω n × M ↦ aminus k n z.1 z.2 j))
    (Y : ∀ n, Ω n → Fin (m n + 1) → M)
    (hY : ∀ n j, Measurable (fun w ↦ Y n w j))
    (p : ∀ n, Ω n → Fin (m n + 1) → ℝ)
    (hfp : ∀ k n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aplus k n w))
    (hfm : ∀ k n, ∀ᵐ w ∂Penv n, IsSemidiscreteAllocation μ (p n w) (aminus k n w))
    (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (D : ℕ → Set (ι → ℝ)) (hD : ∀ n, volume (D n) = ENNReal.ofReal ((m n : ℝ) + 1))
    (Q : ℕ → ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))
    (φ : ℕ → ℕ → ℕ)
    (hinner : ∀ k, Tendsto (fun n ↦ actualAllocationRootedCountableSceneLaw base
      (Penv (φ k n)) μ (aplus k (φ k n)) (aminus k (φ k n))
      (hplus k (φ k n)) (hminus k (φ k n)) (Y (φ k n)) (hY (φ k n))
      (H (φ k n)) (hH (φ k n)) (coord (φ k n)) (hcoord (φ k n))
      u hu (D (φ k n)) (hD (φ k n))) atTop (𝓝 (Q k)))
    (R : ProbabilityMeasure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base))
    (ψ : ℕ → ℕ) (houter : Tendsto (Q ∘ ψ) atTop (𝓝 R)) :
    ∀ᵐ s ∂(R : Measure
      (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)),
      IsFiniteMeasureOnCompacts (s.1.1 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd ∧
      IsFiniteMeasureOnCompacts (s.1.2 : Measure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))).snd := by
  let P := fun k n ↦ actualAllocationRootedCountableSceneLaw base
    (Penv (φ k n)) μ (aplus k (φ k n)) (aminus k (φ k n))
    (hplus k (φ k n)) (hminus k (φ k n)) (Y (φ k n)) (hY (φ k n))
    (H (φ k n)) (hH (φ k n)) (coord (φ k n)) (hcoord (φ k n))
    u hu (D (φ k n)) (hD (φ k n))
  let U := fun n : ℕ ↦ Metric.ball (0 : ι → ℝ) ((n : ℝ) + 1) ×ˢ (univ : Set ℝ)
  have hU (n : ℕ) : IsOpen (U n) := Metric.isOpen_ball.prod isOpen_univ
  have hcover : ∀ K : Set ((ι → ℝ) × ℝ), IsCompact K → ∃ n, K ⊆ U n := by
    intro K hK
    obtain ⟨r, hr, hKr⟩ := (hK.image continuous_fst).isBounded.exists_pos_norm_lt
    obtain ⟨n, hn⟩ := exists_nat_gt r
    refine ⟨n, fun x hx ↦ ⟨?_, mem_univ _⟩⟩
    change dist x.1 0 < (n : ℝ) + 1
    rw [dist_zero_right]
    exact (hKr x.1 ⟨x, hx, rfl⟩).trans (hn.trans (by linarith))
  let C := fun n : ℕ ↦ volume (Metric.ball (0 : ι → ℝ) ((n : ℝ) + 1)) * μ univ
  have hC (n : ℕ) : C n ≠ ⊤ := ENNReal.mul_ne_top measure_ball_lt_top.ne (measure_ne_top μ univ)
  have hb (k n j : ℕ) := lintegral_actualAllocationRootedCountableScene_targetWindow_le base
    (Penv (φ k n)) μ (aplus k (φ k n)) (aminus k (φ k n))
    (hplus k (φ k n)) (hminus k (φ k n)) (Y (φ k n)) (hY (φ k n))
    (p (φ k n)) (hfp k (φ k n)) (hfm k (φ k n))
    (H (φ k n)) (hH (φ k n)) (coord (φ k n)) (hcoord (φ k n))
    u hu (D (φ k n)) (hD (φ k n)) (U := Metric.ball 0 ((j : ℝ) + 1)) Metric.isOpen_ball
  have heq (j : ℕ) : (univ : Set ((ι → ℝ) × ℝ)) ×ˢ U j =
      {e : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) | e.2.1 ∈ Metric.ball 0 ((j : ℝ) + 1)} := by
    ext e
    simp [U]
  have hpa := ae_locallyFinite_snd_of_iterated_weak_target_window_bounds P Q hinner R ψ houter
    (fun s ↦ s.1.1) (continuous_fst.comp continuous_fst) U hU hcover C hC
    (fun k n j ↦ by rw [heq]; exact (hb k n j).1)
  have hma := ae_locallyFinite_snd_of_iterated_weak_target_window_bounds P Q hinner R ψ houter
    (fun s ↦ s.1.2) (continuous_snd.comp continuous_fst) U hU hcover C hC
    (fun k n j ↦ by rw [heq]; exact (hb k n j).2)
  exact hpa.and hma

end OTSelector.Reconstruction
