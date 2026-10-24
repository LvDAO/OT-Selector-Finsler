import OTSelector.MeasureTheory.FixedSourceWeakReadout
import OTSelector.Reconstruction.FinslerPhysicalSceneReadoutMacroscopicMarginals

/-!
# Actual probe gap expectations pass weak laws on a fixed original source

A source-only bounded continuous approximation is enough. Closedness preserves
the original source marginal through the weak law, and a bounded continuous
extension supplies integrability and expectation convergence internally.
-/
open Set Function MeasureTheory Filter TopologicalSpace
open scoped Topology BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000
variable {X Y : Type*} [TopologicalSpace X] [PolishSpace X]
  [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- Weak laws retain the fixed source and the entire actual probe gap expectation,
with no continuity or measurability premise on the original readout itself. -/
theorem fixed_source_probe_gap_expectation_tendsto_of_weak
    {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
    [OpensMeasurableSpace S] [HasOuterApproxClosed S]
    (R : ProbabilityMeasure S) (Pn : ℕ → ProbabilityMeasure S)
    (hweak : Tendsto Pn atTop (𝓝 R))
    (π₀ π₁ : S → ProbabilityMeasure (X × Y))
    (hπ₀ : Continuous π₀) (hπ₁ : Continuous π₁)
    (μ : Measure X) [IsProbabilityMeasure μ] (f : X × Y → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hfBound : ∀ p, |f p| ≤ B)
    (happrox : ∀ ε > 0, ∃ G : (X × Y) →ᵇ ℝ,
      ∀ π : ProbabilityMeasure (X × Y), (π : Measure (X × Y)).fst = μ →
        |(∫ p, f p ∂(π : Measure (X × Y))) - ∫ p, G p ∂(π : Measure (X × Y))| ≤ ε)
    (hsource₀ : ∀ n, ∀ᵐ s ∂(Pn n : Measure S), (π₀ s : Measure (X × Y)).fst = μ)
    (hsource₁ : ∀ n, ∀ᵐ s ∂(Pn n : Measure S), (π₁ s : Measure (X × Y)).fst = μ) :
    (∀ᵐ s ∂(R : Measure S), (π₀ s : Measure (X × Y)).fst = μ ∧
      (π₁ s : Measure (X × Y)).fst = μ) ∧
    (∀ n, Integrable (fun s ↦ |(∫ p, f p ∂(π₀ s : Measure (X × Y))) -
      ∫ p, f p ∂(π₁ s : Measure (X × Y))|) (Pn n : Measure S)) ∧
    Integrable (fun s ↦ |(∫ p, f p ∂(π₀ s : Measure (X × Y))) -
      ∫ p, f p ∂(π₁ s : Measure (X × Y))|) (R : Measure S) ∧
    Tendsto (fun n ↦ ∫ s, |(∫ p, f p ∂(π₀ s : Measure (X × Y))) -
      ∫ p, f p ∂(π₁ s : Measure (X × Y))| ∂(Pn n : Measure S)) atTop
      (𝓝 (∫ s, |(∫ p, f p ∂(π₀ s : Measure (X × Y))) -
        ∫ p, f p ∂(π₁ s : Measure (X × Y))| ∂(R : Measure S))) := by
  let C : Set S := {s | (π₀ s : Measure (X × Y)).fst = μ ∧
    (π₁ s : Measure (X × Y)).fst = μ}
  have hC : IsClosed C :=
    ((isClosed_probability_fixed_source μ).preimage hπ₀).inter
      ((isClosed_probability_fixed_source μ).preimage hπ₁)
  have hPnC (n : ℕ) : ∀ᵐ s ∂(Pn n : Measure S), s ∈ C := by
    filter_upwards [hsource₀ n, hsource₁ n] with s h₀ h₁ using ⟨h₀, h₁⟩
  have hRC := ae_closed_set_of_physicalScene_weak_tendsto R Pn hweak C hC hPnC
  obtain ⟨L, hLbound, hLeq⟩ :=
    exists_boundedContinuous_probability_integral_extension_of_source_approx
      μ f hB hfBound happrox
  have hL (π : ProbabilityMeasure (X × Y)) : |L π| ≤ B := by
    exact ((Real.norm_eq_abs (L π)) ▸ L.norm_coe_le_norm π).trans hLbound
  let obs : S → ℝ := fun s ↦ |(∫ p, f p ∂(π₀ s : Measure (X × Y))) -
    ∫ p, f p ∂(π₁ s : Measure (X × Y))|
  let Hfun : S → ℝ := fun s ↦ |L (π₀ s) - L (π₁ s)|
  have hHbound (s : S) : |Hfun s| ≤ 2 * B := by
    change |(|L (π₀ s) - L (π₁ s)|)| ≤ 2 * B
    rw [abs_abs]
    exact (abs_sub _ _).trans (by linarith [hL (π₀ s), hL (π₁ s)])
  let H : S →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨Hfun, ((L.continuous.comp hπ₀).sub (L.continuous.comp hπ₁)).abs⟩
    (4 * B) (fun s t ↦ by
      change dist (Hfun s) (Hfun t) ≤ 4 * B
      rw [Real.dist_eq]
      exact (abs_sub _ _).trans (by linarith [hHbound s, hHbound t]))
  have hident (s : S) (hs : s ∈ C) : H s = obs s := by
    change |L (π₀ s) - L (π₁ s)| = _
    rw [hLeq (π₀ s) hs.1, hLeq (π₁ s) hs.2]
  have hidentN (n : ℕ) : (fun s ↦ H s) =ᵐ[(Pn n : Measure S)] obs :=
    (hPnC n).mono hident
  have hidentR : (fun s ↦ H s) =ᵐ[(R : Measure S)] obs := hRC.mono hident
  have hInt (Q : ProbabilityMeasure S) : Integrable (fun s ↦ H s) (Q : Measure S) :=
    Integrable.of_bound H.continuous.aestronglyMeasurable (2 * B)
      (ae_of_all _ fun s ↦ (Real.norm_eq_abs (H s)).symm ▸ hHbound s)
  refine ⟨hRC, fun n ↦ (hInt (Pn n)).congr (hidentN n),
    (hInt R).congr hidentR, ?_⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hweak) H
  rw [integral_congr_ae hidentR] at h
  exact h.congr' (Eventually.of_forall fun n ↦ integral_congr_ae (hidentN n))

end OTSelector.Reconstruction
