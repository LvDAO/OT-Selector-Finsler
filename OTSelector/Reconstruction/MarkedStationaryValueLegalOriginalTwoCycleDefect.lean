import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalTwoEdgeSwap

/-!
# The exact bounded-probe defect of an original weighted two-cycle

The unchanged original weighted cost is its kinetic term plus the original
paired-clock probe. A legal weighted two-cycle inequality yields precisely the
pure kinetic defect 4 |t| G. Conversely, violating this defect gives a strict
improvement for the same original weighted cost.
-/
open Set Function MeasureTheory Filter Topology TopologicalSpace
noncomputable section
namespace OTSelector.Reconstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.unusedSectionVars false

/-- The original kinetic cost and original paired-clock probe on a physical edge. -/
def originalWeightedEdgeCost {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (e : LegalMarkedPhysicalEdge q) : ℝ :=
  kin e.1.2 e.2.2 (e.2.1 - e.1.1) + t * g e.1.2 e.2.2

/-- The original weighted edge cost remains Borel without any new coefficient assumption. -/
theorem measurable_originalWeightedEdgeCost {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (originalWeightedEdgeCost kin g t) := by
  exact (hk.comp ((measurable_fst.snd.prodMk measurable_snd.snd).prodMk
    (measurable_snd.fst.sub measurable_fst.fst))).add
      ((hg.comp (measurable_fst.snd.prodMk measurable_snd.snd)).const_mul t)

/-- The four unchanged bounded probe terms give the exact kinetic defect. -/
theorem originalWeightedTwoCycle_le_imp_kinetic_defect {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (e f : LegalMarkedPhysicalEdge q)
    (hcycle : originalWeightedEdgeCost kin g t e + originalWeightedEdgeCost kin g t f ≤
      originalWeightedEdgeCost kin g t (e.1, f.2) +
        originalWeightedEdgeCost kin g t (f.1, e.2)) :
    kin e.1.2 e.2.2 (e.2.1 - e.1.1) + kin f.1.2 f.2.2 (f.2.1 - f.1.1) ≤
      kin e.1.2 f.2.2 (f.2.1 - e.1.1) + kin f.1.2 e.2.2 (e.2.1 - f.1.1) +
        4 * |t| * G := by
  have hb (a b : ℝ) : |t * g a b| ≤ |t| * G := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hgb a b) (abs_nonneg t)
  have h₁ := neg_le_of_abs_le (hb e.1.2 e.2.2)
  have h₂ := neg_le_of_abs_le (hb f.1.2 f.2.2)
  have h₃ := le_of_abs_le (hb e.1.2 f.2.2)
  have h₄ := le_of_abs_le (hb f.1.2 e.2.2)
  dsimp only [originalWeightedEdgeCost] at hcycle
  nlinarith

/-- Failure of the claimed kinetic defect is an actual strict original weighted improvement. -/
theorem originalKinetic_defect_violation_imp_weighted_improvement {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {G : ℝ} (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ)
    (e f : LegalMarkedPhysicalEdge q)
    (hbad : kin e.1.2 f.2.2 (f.2.1 - e.1.1) +
      kin f.1.2 e.2.2 (e.2.1 - f.1.1) + 4 * |t| * G <
        kin e.1.2 e.2.2 (e.2.1 - e.1.1) + kin f.1.2 f.2.2 (f.2.1 - f.1.1)) :
    originalWeightedEdgeCost kin g t (e.1, f.2) +
      originalWeightedEdgeCost kin g t (f.1, e.2) <
        originalWeightedEdgeCost kin g t e + originalWeightedEdgeCost kin g t f := by
  apply lt_of_not_ge
  intro hle
  exact hbad.not_ge
    (originalWeightedTwoCycle_le_imp_kinetic_defect kin g hgb t e f hle)

/-- The original bounded probe makes its stated cycle defect nonnegative. -/
theorem originalTwoCycleDefect_nonneg (g : ℝ → ℝ → ℝ) {G : ℝ}
    (hgb : ∀ a b, |g a b| ≤ G) (t : ℝ) : 0 ≤ 4 * |t| * G := by
  have hG : 0 ≤ G := (abs_nonneg (g 0 0)).trans (hgb 0 0)
  positivity

end OTSelector.Reconstruction
