import OTSelector.Reconstruction.OriginalClasswiseOriginalAtomRepairPortReserveFamilies
import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsLaws
import OTSelector.Reconstruction.OriginalStageClockSlabsLabels

/-! Literal surviving reserve laws and real port kernels construct actual stage arrivals. -/
open Set Function MeasureTheory Module Manifold
open scoped ENNReal BigOperators ContDiff Topology Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
    (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell : ℝ}
namespace OriginalOrientedStageResidualDensityData

/-- Real source port kernels and surviving original reserve laws give each
unchanged unused source label a probability law with the literal Ico arrival. -/
theorem exists_originalUnused_sourceArrivalFamily
    (A : OriginalOrientedStageResidualDensityData S w b R ell) (hR : 1 ≤ R)
    (P : OriginalOrientedPortAtomFamily b R A.sourcePortMeasure)
    (G : OriginalStageClockGrid) {I : Type*} [Fintype I]
    (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
    (hcount : (∑ i, Measure.dirac (x i)) = A.sourcePortMeasure +
      ∑ j : A.sourceKept, Measure.dirac (A.sourceReserve.2 j.val))
    (laws : A.sourceKept → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hprob : ∀ j, IsProbabilityMeasure (laws j))
    (hI : ∀ j, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm
      (A.sourceReserve.2 j.val).1) v^2) (laws j))
    (hclass : ∀ i : Fin G.count,
      (∑ j : A.sourceKept, if (A.sourceReserve.2 j.val).2 ∈ G.sourceCell i then laws j else 0) =
        ENNReal.ofReal ((originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept
          (G.sourceCell i) : ℝ)/A.cubeVolume) • A.cubeMeasure.map (EuclideanSpace.equiv _ ℝ).symm) :
    ∃ κ : I → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
      (∀ i, IsProbabilityMeasure (κ i)) ∧
      (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2) (κ i)) ∧
      (∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i) ≤
        A.sourcePortMeasure.real univ +
          ∑ j : A.sourceKept, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (A.sourceReserve.2 j.val).1) v^2 ∂laws j ∧
      ∀ i : Fin G.count, (∑ j, if (x j).2 ∈ G.sourceCell i then κ j else 0) =
        A.orientedSourceArrivalLaw (G.cut i.val) (G.cut (i.val+1)) := by
  obtain ⟨κ,hκ,hκI,henergy,hclasses⟩ := exists_originalUnusedAtomFamily_of_port_reserve b hR
    A.sourcePortMeasure P x (fun j : A.sourceKept ↦ A.sourceReserve.2 j.val) hcount laws hprob hI
  refine ⟨κ,hκ,hκI,henergy,?_⟩
  intro i
  rw [hclasses (G.sourceCell i) measurableSet_Ico,hclass i]
  rfl

/-- Targets use their own original kept indices and Ioc classes. -/
theorem exists_originalUnused_targetArrivalFamily
    (A : OriginalOrientedStageResidualDensityData S w b R ell) (hR : 1 ≤ R)
    (P : OriginalOrientedPortAtomFamily b R A.targetPortMeasure)
    (G : OriginalStageClockGrid) {I : Type*} [Fintype I]
    (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
    (hcount : (∑ i, Measure.dirac (x i)) = A.targetPortMeasure +
      ∑ j : A.targetKept, Measure.dirac (A.targetReserve.2 j.val))
    (laws : A.targetKept → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    (hprob : ∀ j, IsProbabilityMeasure (laws j))
    (hI : ∀ j, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm
      (A.targetReserve.2 j.val).1) v^2) (laws j))
    (hclass : ∀ i : Fin G.count,
      (∑ j : A.targetKept, if (A.targetReserve.2 j.val).2 ∈ G.targetCell i then laws j else 0) =
        ENNReal.ofReal ((originalStageRemainingReserveClassCount A.targetReserve A.targetKept
          (G.targetCell i) : ℝ)/A.cubeVolume) • A.cubeMeasure.map (EuclideanSpace.equiv _ ℝ).symm) :
    ∃ κ : I → Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
      (∀ i, IsProbabilityMeasure (κ i)) ∧
      (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2) (κ i)) ∧
      (∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i) ≤
        A.targetPortMeasure.real univ +
          ∑ j : A.targetKept, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (A.targetReserve.2 j.val).1) v^2 ∂laws j ∧
      ∀ i : Fin G.count, (∑ j, if (x j).2 ∈ G.targetCell i then κ j else 0) =
        A.orientedTargetDepartureLaw (G.cut i.val) (G.cut (i.val+1)) := by
  obtain ⟨κ,hκ,hκI,henergy,hclasses⟩ := exists_originalUnusedAtomFamily_of_port_reserve b hR
    A.targetPortMeasure P x (fun j : A.targetKept ↦ A.targetReserve.2 j.val) hcount laws hprob hI
  refine ⟨κ,hκ,hκI,henergy,?_⟩
  intro i
  rw [hclasses (G.targetCell i) measurableSet_Ioc,hclass i]
  rfl

end OriginalOrientedStageResidualDensityData
end OTSelector.Reconstruction
