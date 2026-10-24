import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalScene
import OTSelector.Reconstruction.MarkedStationaryValueLegalStationaryDilation
import OTSelector.Reconstruction.FinslerRelativeLawLegalRepair
import OTSelector.Finite.MaxCardValueScaling

/-! Physical dilation preserves the actual legal graph and original finite labels.
The signed cost and its minimum scale quadratically with the corresponding tilt. -/

open Set Function MeasureTheory
open scoped BigOperators
noncomputable section
namespace OTSelector.Reconstruction

/-- Multiplication by a nonnegative scalar preserves minimization at the true
legal maximum, including Hall-deficient graphs and empty original arrays. -/
theorem PartialMatching.legalMaximumValue_const_mul {m n : ℕ}
    (G : Finset (Fin m × Fin n)) (cost : Fin m → Fin n → ℝ)
    {a : ℝ} (ha : 0 ≤ a) :
    PartialMatching.legalMaximumValue G (fun i j ↦ a * cost i j) =
      a * PartialMatching.legalMaximumValue G cost := by
  obtain ⟨σ,hσ,hσcard,hσcost⟩ := PartialMatching.exists_cost_eq_legalMaximumValue G cost
  obtain ⟨τ,hτ,hτcard,hτcost⟩ := PartialMatching.exists_cost_eq_legalMaximumValue G
    (fun i j ↦ a * cost i j)
  apply le_antisymm
  · calc
      _ ≤ σ.cost (fun i j ↦ a * cost i j) :=
        PartialMatching.legalMaximumValue_le _ hσ hσcard
      _ = a * PartialMatching.legalMaximumValue G cost := by
        rw [OTSelector.PartialMatching.cost_const_mul,hσcost]
  · calc
      _ ≤ a * τ.cost cost := mul_le_mul_of_nonneg_left
        (PartialMatching.legalMaximumValue_le _ hτ hτcard) ha
      _ = PartialMatching.legalMaximumValue G (fun i j ↦ a * cost i j) := by
        rw [← OTSelector.PartialMatching.cost_const_mul,hτcost]

/-- The full physical displacement dilates while both original clocks stay fixed.
The new tilt is divided by the same quadratic factor before scaling the signed cost. -/
theorem legalMarkedPhysicalTiltedEdge_dilation {q : ℕ}
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {c : ℝ} (hc : c ≠ 0)
    (hhom : ∀ a b v, kin a b (c • v) = c^2 * kin a b v)
    (t : ℝ) (e : LegalMarkedPhysicalEdge q) :
    legalMarkedPhysicalTiltedEdge q kin g t (legalMarkedEdgeDilation q c hc e) =
      c^2 * legalMarkedPhysicalTiltedEdge q kin g (t / c^2) e := by
  change kin e.1.2 e.2.2 (c • e.2.1-c • e.1.1) + t*g e.1.2 e.2.2 = _
  rw [← smul_sub,hhom]
  unfold legalMarkedPhysicalTiltedEdge
  field_simp

/-- The original scalar-clock legal graph is literally unchanged by dilation.
No original index, particle count or legal cardinality is replaced. -/
theorem scalarClockLegalGraph_original_dilation {q m n : ℕ}
    (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
    {c : ℝ} (hc : c ≠ 0) :
    scalarClockLegalGraph (fun i ↦ (legalMarkedPointDilation q c hc (x i)).2)
      (fun j ↦ (legalMarkedPointDilation q c hc (y j)).2) =
      scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2) := rfl

/-- Every matching on the unchanged original labels has exactly the dilated signed
cost, so the identity applies in particular to the actual retained core and repair. -/
theorem originalFiniteMatching_cost_dilation {q m n : ℕ}
    (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
    (σ : OTSelector.PartialMatching m n)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {c : ℝ} (hc : c ≠ 0)
    (hhom : ∀ a b v, kin a b (c • v) = c^2 * kin a b v) (t : ℝ) :
    σ.cost (fun i j ↦ legalMarkedPhysicalTiltedEdge q kin g t
      (legalMarkedPointDilation q c hc (x i),legalMarkedPointDilation q c hc (y j))) =
      c^2 * σ.cost (fun i j ↦ legalMarkedPhysicalTiltedEdge q kin g (t/c^2) (x i,y j)) := by
  simp_rw [show ∀ i j, legalMarkedPhysicalTiltedEdge q kin g t
    (legalMarkedPointDilation q c hc (x i),legalMarkedPointDilation q c hc (y j)) =
      c^2 * legalMarkedPhysicalTiltedEdge q kin g (t/c^2) (x i,y j) from
        fun i j ↦ legalMarkedPhysicalTiltedEdge_dilation kin g hc hhom t (x i,y j)]
  exact OTSelector.PartialMatching.cost_const_mul _ σ _

/-- The finite minimum at the actual legal maximum scales on precisely the same
original arrays. It makes no assumption that the maximum equals the smaller count. -/
theorem originalFiniteLegalValue_dilation {q m n : ℕ}
    (x : Fin m → LegalMarkedPhysicalPoint q) (y : Fin n → LegalMarkedPhysicalPoint q)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ)
    {c : ℝ} (hc : c ≠ 0)
    (hhom : ∀ a b v, kin a b (c • v) = c^2 * kin a b v) (t : ℝ) :
    PartialMatching.legalMaximumValue
      (scalarClockLegalGraph (fun i ↦ (legalMarkedPointDilation q c hc (x i)).2)
        (fun j ↦ (legalMarkedPointDilation q c hc (y j)).2))
      (fun i j ↦ legalMarkedPhysicalTiltedEdge q kin g t
        (legalMarkedPointDilation q c hc (x i),legalMarkedPointDilation q c hc (y j))) =
      c^2 * PartialMatching.legalMaximumValue
        (scalarClockLegalGraph (fun i ↦ (x i).2) (fun j ↦ (y j).2))
        (fun i j ↦ legalMarkedPhysicalTiltedEdge q kin g (t/c^2) (x i,y j)) := by
  rw [scalarClockLegalGraph_original_dilation]
  simp_rw [show ∀ i j, legalMarkedPhysicalTiltedEdge q kin g t
    (legalMarkedPointDilation q c hc (x i),legalMarkedPointDilation q c hc (y j)) =
      c^2 * legalMarkedPhysicalTiltedEdge q kin g (t/c^2) (x i,y j) from
        fun i j ↦ legalMarkedPhysicalTiltedEdge_dilation kin g hc hhom t (x i,y j)]
  exact PartialMatching.legalMaximumValue_const_mul _ _ (sq_nonneg c)

end OTSelector.Reconstruction
