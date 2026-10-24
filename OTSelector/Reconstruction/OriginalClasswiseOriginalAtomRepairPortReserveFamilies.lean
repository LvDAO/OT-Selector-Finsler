import OTSelector.Reconstruction.OriginalLegalScreeningComparatorOrientedPortFamilies
import OTSelector.Finite.AtomicFamilyReindexing

/-! Genuine port and reserve probability laws on unchanged unused original labels. -/
open Set Function MeasureTheory
open scoped ENNReal BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction

/-- The actual port counting law and original reserve counting law construct
probability smoothing laws on the unchanged unused labels. Every clock class
is retained, and only actual port mass is charged for the reflected smoothing. -/
theorem exists_originalUnusedAtomFamily_of_port_reserve
    {q : ℕ} {I J : Type*} [Fintype I] [Fintype J]
    (b : OrthonormalBasis (Fin q) ℝ (EuclideanSpace ℝ (Fin q))) {R : ℝ} (hR : 1 ≤ R)
    (π : Measure (LegalMarkedPhysicalPoint q)) (A : OriginalOrientedPortAtomFamily b R π)
    (x : I → LegalMarkedPhysicalPoint q) (y : J → LegalMarkedPhysicalPoint q)
    (hcount : (∑ i, Measure.dirac (x i)) = π + ∑ j, Measure.dirac (y j))
    (laws : J → Measure (EuclideanSpace ℝ (Fin q)))
    (hlaws : ∀ j, IsProbabilityMeasure (laws j))
    (hI : ∀ j, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (y j).1) v^2) (laws j)) :
    ∃ κ : I → Measure (EuclideanSpace ℝ (Fin q)),
      (∀ i, IsProbabilityMeasure (κ i)) ∧
      (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2) (κ i)) ∧
      (∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i) ≤
        π.real univ + ∑ j, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (y j).1) v^2 ∂laws j ∧
      ∀ C : Set ℝ, MeasurableSet C →
        (∑ i, if (x i).2 ∈ C then κ i else 0) =
          (((volume.restrict (originalCenteredPhysicalCubeRegion b (2*R))).withDensity
            (fun z ↦ ENNReal.ofReal (originalOrientedStageReflectedClassDensity b R C π z))).map
            (EuclideanSpace.equiv _ ℝ).symm) + ∑ j, if (y j).2 ∈ C then laws j else 0 := by
  let points : Fin A.count ⊕ J → LegalMarkedPhysicalPoint q := Sum.elim A.points y
  let η : Fin A.count ⊕ J → Measure (EuclideanSpace ℝ (Fin q)) := Sum.elim A.law laws
  have hs := A.spec hR
  have hxy : (∑ i, Measure.dirac (x i)) = ∑ j, Measure.dirac (points j) := by
    rw [hcount, Fintype.sum_sum_type]
    conv_lhs => rw [A.measure_eq]
    rfl
  have hprob (j : Fin A.count ⊕ J) : IsProbabilityMeasure (η j) := by
    cases j with
    | inl i => exact hs.1 i
    | inr j => exact hlaws j
  have hint (j : Fin A.count ⊕ J) :
      Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (points j).1) v^2) (η j) := by
    cases j with
    | inl i => exact hs.2.1 i
    | inr j => exact hI j
  obtain ⟨κ,hκ,hκI,henergy,hclass⟩ := exists_originalAtomFamily_of_countingMeasure_eq
    x points hxy (fun p ↦ (EuclideanSpace.equiv _ ℝ).symm p.1) Prod.snd η hprob hint
  refine ⟨κ,hκ,hκI,?_,?_⟩
  · rw [henergy, Fintype.sum_sum_type]
    exact add_le_add hs.2.2.1 le_rfl
  · intro C hC
    rw [hclass C, Fintype.sum_sum_type]
    dsimp only [points, η, Sum.elim_inl, Sum.elim_inr]
    rw [← hs.2.2.2 C hC]

end OTSelector.Reconstruction
