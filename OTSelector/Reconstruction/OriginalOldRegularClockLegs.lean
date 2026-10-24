import OTSelector.Reconstruction.OriginalRegularClockGeometry

/-! Uniform actual geometry on compact regular physical-clock strips, and
whole-span length lower bounds, with focal endpoints still allowed. -/
open Set Function Filter MeasureTheory Matrix Module Manifold
open scoped Topology ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
/-- An old source-side regular clock is separated from both actual edge ends.
The estimate follows from its literal nearer-side and old-clock inequalities. -/
theorem source_oldRegular_clock_leg_bounds {l a b c ε gap : ℝ}
    (hnear : c - a ≤ b - c) (hold : a - l < c - a)
    (hregular : ε < c - l) (hgap : gap ≤ b - a) :
    ε / 2 < c - a ∧ gap / 2 ≤ b - c := by
  constructor <;> linarith

/-- The reflected old target-side clock gives the same two genuine leg bounds. -/
theorem target_oldRegular_clock_leg_bounds {h a b c ε gap : ℝ}
    (hnear : b - c ≤ c - a) (hold : h - b < b - c)
    (hregular : ε < h - c) (hgap : gap ≤ b - a) :
    gap / 2 ≤ c - a ∧ ε / 2 < b - c := by
  constructor <;> linarith

/-- The literal source-side birth/regular region lies in a compact physical
clock strip, independently of how short its elapsed source leg becomes. -/
theorem source_birthRegular_clock_strip {l h a b c ε gap : ℝ}
    (hupper : b < h) (hactive : a < c) (hnear : c - a ≤ b - c)
    (hregular : ε < a - l) (hgap : gap ≤ b - a) :
    l + ε < c ∧ c < h - gap / 2 := by
  constructor <;> linarith

/-- The corresponding target-side birth/regular clock has the reflected strip. -/
theorem target_birthRegular_clock_strip {l h a b c ε gap : ℝ}
    (hlower : l < a) (hactive : c < b) (hnear : b - c ≤ c - a)
    (hregular : ε < h - b) (hgap : gap ≤ b - a) :
    l + gap / 2 < c ∧ c < h - ε := by
  constructor <;> linarith

namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

/-- The actual whole-span mobility lower bound controls both original legs
at a nearby reference clock, uniformly over all old regular edges. No rank or
endpoint nonfocality condition is imposed. -/
theorem exists_original_uniform_reference_legs
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) {ε : ℝ} (hε : 0 < ε) :
    ∃ κ > 0, ∀ {a b c r : ℝ},
      a - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      b - (S.level : ℝ) ∈ Ioo D.lo D.hi →
      ε ≤ c - a → ε ≤ b - c → |r - c| ≤ ε / 2 →
      r - (S.level : ℝ) ∈ Ioo D.lo D.hi ∧
        (originalSeedClockCompliance S w a r - (κ * (ε / 2)) • 1).PosSemidef ∧
        (originalSeedClockCompliance S w r b - (κ * (ε / 2)) • 1).PosSemidef := by
  obtain ⟨κ, hκ, hlegs⟩ := D.exists_original_compliance_wholeSpan_length_lower hF hw
  refine ⟨κ, hκ, ?_⟩
  intro a b c r ha hb hleft hright hr
  have hrs := abs_le.mp hr
  have hrl : ε / 2 ≤ r - a := by linarith [hrs.1]
  have hrr : ε / 2 ≤ b - r := by linarith [hrs.2]
  have har : a < r := by linarith
  have hrb : r < b := by linarith
  have hrI : r - (S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ⟨by linarith [ha.1], by linarith [hb.2]⟩
  refine ⟨hrI, ?_, ?_⟩
  · apply scalar_identity_lower_bound_mono
      (show κ * (ε / 2) ≤ (r - a) * κ by nlinarith)
    exact hlegs har.le ha hrI
  · apply scalar_identity_lower_bound_mono
      (show κ * (ε / 2) ≤ (b - r) * κ by nlinarith)
    exact hlegs hrb.le hrI hb

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
