import OTSelector.Reconstruction.MarkedStationaryValueLegalInputPalmNormalization

/-!
# The same actual joint input scene has strictly forward matching support

The original product-almost-everywhere absolute clock gap is inherited by
all original legal finite edges. The existing closed-clock weak-limit result
then controls the whole actual edge support after the exact pair projection.
This is a support assertion in the same joint scene, not only a Palm assertion.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

local instance markedStationaryValueLegalInputForwardSceneInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputForwardScenePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace

/-- All actual support edges keep the original positive clock gap, even when
the two original populations interleave. No global clock ordering is added. -/
theorem ae_support_clockGap_of_legalMarkedInputSceneLaw_tendsto
    (q : ℕ) (hq : 0 < q)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    {Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)}
    (hweak : Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k)) atTop (𝓝 Q))
    {δ : ℝ} (hsep : ∀ᵐ p ∂α.prod β, δ ≤ |p.2 - p.1|) :
    ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      ∀ e ∈ (s.1.1 : Measure (LegalMarkedPhysicalEdge q)).support,
        δ ≤ e.2.2 - e.1.2 := by
  have hpair := legalMarkedInputPairLaw_tendsto q hq α β kin hk g hg t L hL hweak
  have hgap := (ae_cubePalm_clockGap_of_legalMarkedOptimalRootedSceneLaw_tendsto
    q hq α β kin hk g hg t L hL hpair hsep).1
  have hjoint : ∀ᵐ s ∂(Q : Measure (LegalMarkedOptimalInputScene q)),
      ∀ᵐ e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q)), δ ≤ e.2.2 - e.1.2 := by
    exact ae_of_ae_map (μ := (Q : Measure (LegalMarkedOptimalInputScene q)))
      measurable_fst.aemeasurable hgap
  filter_upwards [hjoint] with s hs
  exact Measure.support_subset_of_isClosed
    (isClosed_le continuous_const (continuous_snd.snd.sub continuous_fst.snd)) hs

end OTSelector.Reconstruction
