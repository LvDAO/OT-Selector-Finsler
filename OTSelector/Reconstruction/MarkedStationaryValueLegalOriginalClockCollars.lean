import OTSelector.Transport.CompactClockCoercivity
import OTSelector.Reconstruction.OriginalSeedPairCoefficientContinuity
import OTSelector.Reconstruction.FinslerPopulationConditionalSeparation

/-!
# Interior collars of the actual original conditional Finsler coefficient

The unchanged conditional populations have full mass inside their original
common seed span. The literal original inverse-compliance coefficient is
continuous and positive on its strict interior, so compact collar coercivity
is produced without extending positivity to the potentially focal endpoints.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace Matrix Module Manifold
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}

namespace OriginalSeedConditionalMoments
variable (D : OriginalSeedConditionalMoments S w μ ν)

/-- The original pair coefficient is continuous on the entire strict interior
clock domain, by neighborhoods contained in the original compact intervals. -/
theorem continuousOn_pair_coefficient_interior
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels) :
    ContinuousOn (originalSeedPairCoefficient S w)
      {p | p.1 - S.level ∈ Ioo D.lo D.hi ∧
        p.2 - S.level ∈ Ioo D.lo D.hi ∧ p.1 < p.2} := by
  intro p hp
  let a : ℝ := (D.lo + S.level + p.1) / 2
  let b : ℝ := (p.2 + D.hi + S.level) / 2
  have ha : a - S.level ∈ Ioo D.lo D.hi := by
    dsimp [a]
    constructor <;> linarith [hp.1.1, hp.1.2]
  have hb : b - S.level ∈ Ioo D.lo D.hi := by
    dsimp [b]
    constructor <;> linarith [hp.2.1.1, hp.2.1.2]
  have hap : a < p.1 := by dsimp [a]; linarith [hp.1.1]
  have hpb : p.2 < b := by dsimp [b]; linarith [hp.2.1.2]
  have hab : a ≤ b := (hap.trans (hp.2.2.trans hpb)).le
  have hc := D.continuousOn_pair_coefficient hF hw hab ha hb
  have hmem : p ∈ {r : ℝ × ℝ | r.1 ∈ Icc a b ∧ r.2 ∈ Icc a b ∧ r.1 < r.2} :=
    ⟨⟨hap.le, (hp.2.2.trans hpb).le⟩, ⟨(hap.trans hp.2.2).le, hpb.le⟩, hp.2.2⟩
  have hn : {r : ℝ × ℝ | r.1 ∈ Icc a b ∧ r.2 ∈ Icc a b ∧ r.1 < r.2} ∈ 𝓝 p := by
    have ho : IsOpen {r : ℝ × ℝ | (a < r.1 ∧ r.2 < b) ∧ r.1 < r.2} :=
      ((isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt continuous_snd continuous_const)).inter
        (isOpen_lt continuous_fst continuous_snd)
    apply mem_of_superset (ho.mem_nhds ⟨⟨hap, hpb⟩, hp.2.2⟩)
    intro r hr
    exact ⟨⟨hr.1.1.le, (hr.2.trans hr.1.2).le⟩,
      ⟨(hr.1.1.trans hr.2).le, hr.1.2.le⟩, hr.2⟩
  exact ((hc p hmem).continuousAt hn).continuousWithinAt

/-- The actual original Finsler coefficient has arbitrarily full compact
clock collars. Every lower bound is produced on its own interior collar and
is independent of any pairing or selected matching endpoint. -/
theorem exists_compact_pair_coefficient_collars
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {δ diameter : ℝ} (hδ : 0 < δ) (hbounds : ConditionalClockSupportBounds μ ν δ diameter)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ A B : Set ℝ, IsCompact A ∧ IsCompact B ∧
      A ⊆ {x | x - S.level ∈ Ioo D.lo D.hi} ∩ μ.support ∧
      B ⊆ {x | x - S.level ∈ Ioo D.lo D.hi} ∩ ν.support ∧
      μ Aᶜ < ε ∧ ν Bᶜ < ε ∧
      ∃ c > 0, ∀ a ∈ A, ∀ b ∈ B, a < b →
        ∀ v : Fin (finrank ℝ S.covector.ker) → ℝ,
          c * ‖v‖ ^ 2 ≤ matrixQuadratic (originalSeedPairCoefficient S w (a, b)) v := by
  let _ : IsProbabilityMeasure μ := D.support.source.probability
  let _ : IsProbabilityMeasure ν := D.support.target.probability
  exact exists_compact_legal_clock_collars (finrank ℝ S.covector.ker) μ ν
    (measurableSet_Ioo.preimage ((measurable_id : Measurable (id : ℝ → ℝ)).sub_const (S.level : ℝ)))
    μ.isClosed_support.measurableSet ν.isClosed_support.measurableSet
    (ae_iff.mp D.support.source.ae_open) (ae_iff.mp D.support.target.ae_open)
    μ.measure_compl_support ν.measure_compl_support hδ
    (fun a ha b hb ↦ by simpa only [Real.dist_eq, abs_sub_comm] using hbounds.separated a ha b hb)
    (originalSeedPairCoefficient S w) (D.continuousOn_pair_coefficient_interior hF hw)
    (fun p hp hq hpq ↦ (D.pair_compliance_posDef hF hw hp hq hpq).2)
    (fun a b v ↦ matrixQuadratic (originalSeedPairCoefficient S w (a, b)) v)
    (fun _ _ _ _ _ _ ↦ rfl) hε

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
