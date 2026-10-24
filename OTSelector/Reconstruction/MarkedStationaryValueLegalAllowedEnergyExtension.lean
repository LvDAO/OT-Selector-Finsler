import OTSelector.Reconstruction.MarkedStationaryValueLegalInputPalmNormalization
import Mathlib.Topology.TietzeExtension

/-!
# Continuous nonnegative energy tests agreeing on the actual legal carrier

The original quadratic coefficient and probe are continuous only on their real
closed clock carrier. Tietze extension is used solely to build a continuous
weak-convergence test; it changes neither the legal graph nor any actual cost.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- A genuine actual closed coefficient carrier produces a nonnegative global
continuous test agreeing with the original shifted signed cost at every actual
carrier mark and every full displacement. No global kernel continuity is needed. -/
theorem exists_continuous_nonnegative_legal_shifted_energy
    (q : ℕ) {K : Set (ℝ × ℝ)} (hK : IsClosed K)
    (matrix : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ)
    (hmatrix : ContinuousOn matrix K)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} (hkn : ∀ a b v, 0 ≤ kin a b v)
    (hactual : ∀ w ∈ K, ∀ v, kin w.1 w.2 v = matrixQuadratic (matrix w) v)
    {g : ℝ → ℝ → ℝ} (hg : ContinuousOn (Function.uncurry g) K)
    {G : ℝ} (hgb : ∀ w ∈ K, |g w.1 w.2| ≤ G) (t : ℝ) :
    ∃ F : C(PhysicalPairPalmMark (Fin q), ℝ), (∀ m, 0 ≤ F m) ∧
      ∀ m : PhysicalPairPalmMark (Fin q), m.1 ∈ K →
        F m = kin m.1.1 m.1.2 m.2 + t * g m.1.1 m.1.2 + |t| * G := by
  let S : Set (PhysicalPairPalmMark (Fin q)) := K ×ˢ univ
  let H (m : PhysicalPairPalmMark (Fin q)) :=
    matrixQuadratic (matrix m.1) m.2 + t * g m.1.1 m.1.2 + |t| * G
  have hH : ContinuousOn H S := by
    have hg' : ContinuousOn (fun m : PhysicalPairPalmMark (Fin q) ↦ g m.1.1 m.1.2) S :=
      hg.comp continuous_fst.continuousOn (fun m hm ↦ hm.1)
    exact ((continuousOn_matrixQuadratic_field hmatrix univ).add
      (continuousOn_const.mul hg')).add continuousOn_const
  let H' : C(S, ℝ) := ⟨fun m ↦ H m, continuousOn_iff_continuous_domRestrict.mp hH⟩
  obtain ⟨E, hE⟩ := H'.exists_restrict_eq (hK.prod isClosed_univ)
  let F : C(PhysicalPairPalmMark (Fin q), ℝ) :=
    ⟨fun m ↦ max (E m) 0, E.continuous.max continuous_const⟩
  refine ⟨F, fun m ↦ le_max_right _ _, fun m hm ↦ ?_⟩
  have hEm : E m = H m := congrArg (fun f : C(S, ℝ) ↦ f ⟨m, hm, mem_univ _⟩) hE
  have habs : |t * g m.1.1 m.1.2| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb m.1 hm) (abs_nonneg t)
  have hn : 0 ≤ H m := by
    dsimp [H]
    rw [← hactual m.1 hm m.2]
    linarith [(abs_le.mp habs).1, hkn m.1.1 m.1.2 m.2]
  change max (E m) 0 = _
  rw [hEm, max_eq_left hn]
  dsimp [H]
  rw [← hactual m.1 hm m.2]

end OTSelector.Reconstruction
