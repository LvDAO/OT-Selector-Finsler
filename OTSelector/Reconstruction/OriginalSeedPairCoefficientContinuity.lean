import OTSelector.Reconstruction.OriginalSeedPairCoefficient
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of the original pair coefficient

A continuous positive kernel has continuous compliance in both endpoints on
compact interior intervals. Inversion is continuous at every strictly ordered
pair, giving the actual original quadratic coefficient without a selected chart.
-/

open Set Matrix Module Manifold MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Operator

noncomputable section
namespace OTSelector.Reconstruction

open OTSelector.Geometry ContinuousFinslerNorm
set_option backward.isDefEq.respectTransparency false

/-- The actual oriented compliance is continuous in both endpoints of a compact interval. -/
theorem continuousOn_intervalCompliance {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {K : ℝ → V} {a b : ℝ} (hab : a ≤ b) (hK : ContinuousOn K (Icc a b)) :
    ContinuousOn (fun p : ℝ × ℝ ↦ ∫ t in p.1..p.2, K t)
      (Icc a b ×ˢ Icc a b) := by
  have hKu : ContinuousOn K (uIcc a b) := by simpa only [uIcc_of_le hab] using hK
  have hi := hKu.intervalIntegrable (μ := volume)
  have hp : ContinuousOn (fun x ↦ ∫ t in a..x, K t) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      intervalIntegral.continuousOn_primitive_interval' hi left_mem_uIcc
  have hc : ContinuousOn (fun p : ℝ × ℝ ↦
      (∫ t in a..p.2, K t) - ∫ t in a..p.1, K t) (Icc a b ×ˢ Icc a b) :=
    (hp.comp continuousOn_snd (fun _ h ↦ h.2)).sub
      (hp.comp continuousOn_fst (fun _ h ↦ h.1))
  apply hc.congr
  intro p hp
  have hint {x : ℝ} (hx : x ∈ Icc a b) : IntervalIntegrable K volume a x := by
    apply hi.mono_set
    rw [uIcc_of_le hx.1, uIcc_of_le hab]
    exact Icc_subset_Icc le_rfl hx.2
  exact (intervalIntegral.integral_interval_sub_left (hint hp.2) (hint hp.1)).symm

/-- Inverse compliance is continuous on all strictly ordered pairs of a compact
interval where the original kernel is continuous and positive definite. -/
theorem continuousOn_inverseIntervalCompliance {n : Type*} [Fintype n] [DecidableEq n]
    {K : ℝ → Matrix n n ℝ} {a b : ℝ} (hab : a ≤ b)
    (hK : ContinuousOn K (Icc a b)) (hpos : ∀ t ∈ Icc a b, (K t).PosDef) :
    ContinuousOn (fun p : ℝ × ℝ ↦ (∫ t in p.1..p.2, K t)⁻¹)
      {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 < p.2} := by
  have hc := (continuousOn_intervalCompliance hab hK).mono
    (show {p : ℝ × ℝ | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 < p.2} ⊆
      Icc a b ×ˢ Icc a b from fun _ h ↦ ⟨h.1, h.2.1⟩)
  intro p hp
  have hsub : Icc p.1 p.2 ⊆ Icc a b := Icc_subset_Icc hp.1.1 hp.2.1.2
  have hpd := posDef_intervalIntegral hp.2.2 (hK.mono hsub)
    (fun t ht ↦ hpos t (hsub ht))
  have hinv : ContinuousAt (fun A : Matrix n n ℝ ↦ A⁻¹)
      (∫ t in p.1..p.2, K t) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using continuousAt_inv₀ hpd.det_pos.ne'
  exact hinv.comp_continuousWithinAt
    (f := fun q : ℝ × ℝ ↦ ∫ t in q.1..q.2, K t) (hc p hp)

private theorem continuousOn_orderedPair_shift {V : Type*} [TopologicalSpace V]
    {f : ℝ × ℝ → V} {a b c : ℝ}
    (hc : ContinuousOn f {p | p.1 ∈ Icc (a - c) (b - c) ∧
      p.2 ∈ Icc (a - c) (b - c) ∧ p.1 < p.2}) :
    ContinuousOn (fun p : ℝ × ℝ ↦ f (p.1 - c, p.2 - c))
      {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 < p.2} := by
  let shift : ℝ × ℝ → ℝ × ℝ := fun p ↦ (p.1 - c, p.2 - c)
  have hs : Continuous shift := (continuous_fst.sub continuous_const).prodMk
    (continuous_snd.sub continuous_const)
  have hm : MapsTo shift {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 < p.2}
      {p | p.1 ∈ Icc (a - c) (b - c) ∧ p.2 ∈ Icc (a - c) (b - c) ∧ p.1 < p.2} := by
    intro p hp
    exact ⟨⟨sub_le_sub_right hp.1.1 _, sub_le_sub_right hp.1.2 _⟩,
      ⟨sub_le_sub_right hp.2.1.1 _, sub_le_sub_right hp.2.1.2 _⟩,
      sub_lt_sub_right hp.2.2 _⟩
  exact hc.comp hs.continuousOn hm

/-- The same continuous inverse compliance in an arbitrary fixed scalar clock. -/
theorem continuousOn_inverseScalarIntervalCompliance {n : Type*}
    [Fintype n] [DecidableEq n] {K : ℝ → Matrix n n ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hK : ContinuousOn K (Icc (a - c) (b - c)))
    (hpos : ∀ t ∈ Icc (a - c) (b - c), (K t).PosDef) :
    ContinuousOn (fun p : ℝ × ℝ ↦ (∫ t in (p.1 - c)..(p.2 - c), K t)⁻¹)
      {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 < p.2} := by
  have hc := continuousOn_inverseIntervalCompliance (sub_le_sub_right hab _) hK hpos
  exact continuousOn_orderedPair_shift hc

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

namespace OriginalSeedConditionalMoments

variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)

omit [BorelSpace E] in
/-- The same original scalar coefficient is continuous on every compact interior
ordered-pair region, in the original label basis and scalar time convention. -/
theorem continuousOn_pair_coefficient (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {a b : ℝ} (hab : a ≤ b)
    (ha : a - S.level ∈ Ioo D.lo D.hi) (hb : b - S.level ∈ Ioo D.lo D.hi) :
    ContinuousOn (originalSeedPairCoefficient S w)
      {p | p.1 ∈ Icc a b ∧ p.2 ∈ Icc a b ∧ p.1 < p.2} := by
  have hK := D.original_kernel_regular hF hw
  have hsub : Icc (a - S.level) (b - S.level) ⊆ Ioo D.lo D.hi :=
    Icc_subset_Ioo ha.1 hb.2
  exact continuousOn_inverseScalarIntervalCompliance hab (hK.1.mono hsub)
    (fun t ht ↦ hK.2 t (hsub ht))

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
