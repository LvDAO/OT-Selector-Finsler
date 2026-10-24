import OTSelector.Reconstruction.OriginalStageResidualDensityEndpointReadouts
import OTSelector.Reconstruction.OriginalStageResidualDensityActualWindowArrays

/-! Actual extreme-class removal supplies the two endpoint gamma equalities. -/
open Set Function Filter MeasureTheory Module Manifold
open scoped ENNReal Topology ContDiff BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability

/-- Total mass of the actual surviving reserve measure is its exact original-index count. -/
theorem originalStageRemainingReserveMeasure_mass {q : ℕ} (z : MarkedCloudSpace q ℝ)
    (kept : Finset (Fin z.1)) :
    (originalStageRemainingReserveMeasure z kept).real univ = (kept.card : ℝ) := by
  simpa [originalStageRemainingReserveClassCount] using
    originalStageRemainingReserveMeasure_class_mass z kept (C := univ) MeasurableSet.univ

/-- An exact original-window array representation has exactly the actual colored count;
this count equality is derived from the represented measure, not provided separately. -/
theorem IsOriginalStageMainWindowArrays.actual_counts {q : ℕ} {R : ℝ}
    {scene : LegalMarkedOptimalInputScene q} {sourceMain targetMain : MarkedCloudSpace q ℝ}
    (h : IsOriginalStageMainWindowArrays R scene sourceMain targetMain) :
    (legalInputColorMeasure q scene.2 0).real {p | p.1 ∈ haarRootCube (Fin q) R} = (sourceMain.1 : ℝ) ∧
    (legalInputColorMeasure q scene.2 1).real {p | p.1 ∈ haarRootCube (Fin q) R} = (targetMain.1 : ℝ) := by
  have hs := congrArg (fun π : Measure (LegalMarkedPhysicalPoint q) ↦ π.real univ) h.1
  have ht := congrArg (fun π : Measure (LegalMarkedPhysicalPoint q) ↦ π.real univ) h.2
  rw [originalStageRemainingReserveMeasure_mass, Finset.card_univ, Fintype.card_fin] at hs ht
  simpa only [measureReal_def, Measure.restrict_apply_univ] using And.intro hs ht

/-- Interior original reserve clock marks give zero empty prefix and the exact kept-index
color difference at the full prefix, even after adaptive mark/index removal. -/
theorem originalStageRemainingReservePrefix_extremes {q : ℕ}
    (sourceReserve targetReserve : MarkedCloudSpace q ℝ)
    (sourceKept : Finset (Fin sourceReserve.1)) (targetKept : Finset (Fin targetReserve.1))
    {lo hi : ℝ}
    (hs : ∀ i : Fin sourceReserve.1, lo < (sourceReserve.2 i).2 ∧ (sourceReserve.2 i).2 < hi)
    (ht : ∀ i : Fin targetReserve.1, lo < (targetReserve.2 i).2 ∧ (targetReserve.2 i).2 < hi) :
    originalStageRemainingReservePrefix sourceReserve targetReserve sourceKept targetKept lo = 0 ∧
    originalStageRemainingReservePrefix sourceReserve targetReserve sourceKept targetKept hi =
      (sourceKept.card : ℝ) - targetKept.card := by
  have hsl : originalStageRemainingReserveClassCount sourceReserve sourceKept (Iio lo) = 0 := by
    unfold originalStageRemainingReserveClassCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    exact not_lt_of_ge (hs i).1.le
  have htl : originalStageRemainingReserveClassCount targetReserve targetKept (Iic lo) = 0 := by
    unfold originalStageRemainingReserveClassCount
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro i _
    exact not_le_of_gt (ht i).1
  have hsu : originalStageRemainingReserveClassCount sourceReserve sourceKept (Iio hi) = sourceKept.card := by
    exact congrArg Finset.card (Finset.filter_eq_self.mpr (fun i _ ↦ (hs i).2))
  have htu : originalStageRemainingReserveClassCount targetReserve targetKept (Iic hi) = targetKept.card := by
    exact congrArg Finset.card (Finset.filter_eq_self.mpr (fun i _ ↦ (ht i).2.le))
  simp only [originalStageRemainingReservePrefix, hsl, htl, hsu, htu, Nat.cast_zero, sub_self,
    and_self]

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
namespace OriginalSeedConditionalMoments
variable {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker} {μ ν : Measure ℝ}
  (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- On one original full-scene event, every actual main-window representation and every
original reserve observation with interior clock marks and actual extreme-class capacity
produce gamma_0 = gamma_m = 0 after deleting precisely the actual full color excess.
No endpoint gamma, desired balance or finished cut-cancellation assumption is used. -/
theorem ae_all_originalStageExcessRemoval_endpoint_gamma_eq_zero
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    {kin : ℝ → ℝ → (Fin (finrank ℝ S.covector.ker) → ℝ) → ℝ} {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν kin g)
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2 * ell ≤ R) :
    ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ A : OriginalStageExcessRemovalData (finrank ℝ S.covector.ker),
      IsOriginalStageMainWindowArrays R scene A.sourceMain A.targetMain →
      (∀ i : Fin A.sourceReserve.1, D.lo + (S.level : ℝ) < (A.sourceReserve.2 i).2 ∧
        (A.sourceReserve.2 i).2 < D.hi + (S.level : ℝ)) →
      (∀ i : Fin A.targetReserve.1, D.lo + (S.level : ℝ) < (A.targetReserve.2 i).2 ∧
        (A.targetReserve.2 i).2 < D.hi + (S.level : ℝ)) → A.hasCapacity →
      let B : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier _) :=
        ⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩
      B.gamma (D.lo + (S.level : ℝ)) = 0 ∧ B.gamma (D.hi + (S.level : ℝ)) = 0 := by
  let q := finrank ℝ S.covector.ker
  have hη := (contDiff_originalEuclideanMollifier q).continuous
  have hcη := hasCompactSupport_originalEuclideanMollifier q
  have hηI := integrable_originalEuclideanMollifier q
  have hηone := integral_originalEuclideanMollifier_eq_one q
  have hsupport := raw_unit_range_of_euclidean_unit_range (originalEuclideanMollifier_unit_range q)
  have heven := coordinate_even_of_euclideanRadial (originalEuclideanMollifier_radial q)
  have hηM := abs_originalEuclideanMollifier_le q
  filter_upwards [D.ae_originalStageEndpointReadouts Q R,
    D.ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError hF hw Q hell hR
      (D.lo + (S.level : ℝ)) hη hcη hηI hηone hsupport heven hηM,
    D.ae_all_originalStageGamma_eq_reservePrefix_add_fullCutError hF hw Q hell hR
      (D.hi + (S.level : ℝ)) hη hcη hηI hηone hsupport heven hηM]
    with scene hread hlo hhi
  intro A harray hs ht hcap
  dsimp only
  let B : OriginalStageResidualDensityData S w R ell (originalEuclideanMollifier q) :=
    ⟨scene, A.sourceReserve, A.targetReserve, A.sourceKept, A.targetKept⟩
  have hreserve := originalStageRemainingReservePrefix_extremes A.sourceReserve A.targetReserve
    A.sourceKept A.targetKept hs ht
  have hdelta0 : originalStageFullCutError S w R (D.lo + (S.level : ℝ))
      (originalEuclideanMollifier q) scene = 0 := by
    rw [originalStageFullCutError, hread.1, hread.2.2.1]
    simp only [integral_zero_measure, integral_zero, sub_self]
  have hdeltam : originalStageFullCutError S w R (D.hi + (S.level : ℝ))
      (originalEuclideanMollifier q) scene = (A.sourceMain.1 : ℝ) - A.targetMain.1 := by
    rw [originalStageFullCutError, hread.2.1, hread.2.2.2,
      harray.actual_counts.1, harray.actual_counts.2]
    simp only [integral_zero_measure, integral_zero, sub_zero]
  have hbalance : (A.sourceMain.1 : ℝ) + A.sourceKept.card =
      (A.targetMain.1 : ℝ) + A.targetKept.card := by
    exact_mod_cast (A.removal_counts_and_balance hcap).2.2
  constructor
  · rw [hlo A.sourceReserve A.targetReserve A.sourceKept A.targetKept, hdelta0]
    change (originalStageRemainingReservePrefix _ _ _ _ _ + 0) / B.cubeVolume = 0
    rw [hreserve.1]
    simp
  · rw [hhi A.sourceReserve A.targetReserve A.sourceKept A.targetKept, hdeltam]
    change (originalStageRemainingReservePrefix _ _ _ _ _ +
      ((A.sourceMain.1 : ℝ) - A.targetMain.1)) / B.cubeVolume = 0
    rw [hreserve.2, show (A.sourceKept.card : ℝ) - A.targetKept.card +
      ((A.sourceMain.1 : ℝ) - A.targetMain.1) = 0 by linarith]
    exact zero_div _

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
