import OTSelector.Reconstruction.OriginalMarkSelectedPopulationCouplingOriginalUnusedFamiliesAlmostEverywhere
import OTSelector.Probability.UnusedAtomFamilyExtension

/-! Extend genuine unused arrival families to unchanged full original labels at zero cost. -/
open Set Function MeasureTheory Module Manifold
open scoped BigOperators ENNReal Classical ContDiff
noncomputable section
universe uE uM uI
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

/-- The full original family retains all unused arrivals and energy;
every other original label receives its own point mass and costs zero. -/
def OriginalFullUnusedArrivalFamilySpec {q N : ℕ} {I : Type*} [Fintype I]
    (U : Finset I) (x : I → LegalMarkedPhysicalPoint q) (cell : Fin N → Set ℝ)
    (arrival : Fin N → Measure (EuclideanSpace ℝ (Fin q))) (budget : ℝ)
    (κ : I → Measure (EuclideanSpace ℝ (Fin q))) : Prop :=
  (∀ i, IsProbabilityMeasure (κ i)) ∧
    (∀ i, Integrable (fun v ↦ dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2) (κ i)) ∧
    OriginalUnusedArrivalFamilySpec (fun i : U ↦ x i.val) cell arrival budget (fun i ↦ κ i.val) ∧
    (∑ i, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i) =
      (∑ i : U, ∫ v, dist ((EuclideanSpace.equiv _ ℝ).symm (x i.val).1) v^2 ∂κ i.val) ∧
    ∀ i, i ∉ U → κ i = Measure.dirac ((EuclideanSpace.equiv _ ℝ).symm (x i).1)

theorem exists_originalUnusedArrivalFamily_extension {q N : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (U : Finset I) (x : I → LegalMarkedPhysicalPoint q)
    (cell : Fin N → Set ℝ) (arrival : Fin N → Measure (EuclideanSpace ℝ (Fin q))) (budget : ℝ)
    (laws : U → Measure (EuclideanSpace ℝ (Fin q)))
    (h : OriginalUnusedArrivalFamilySpec (fun i : U ↦ x i.val) cell arrival budget laws) :
    ∃ κ, OriginalFullUnusedArrivalFamilySpec U x cell arrival budget κ := by
  obtain ⟨κ,hκ,hI,hagree,hout⟩ := exists_originalUnusedAtomFamily_extension U
    (fun i ↦ (EuclideanSpace.equiv _ ℝ).symm (x i).1) laws h.1 h.2.1
  have heq : (fun i : U ↦ κ i.val) = laws := funext fun i ↦ hagree i.val i.property
  refine ⟨κ,hκ,hI,?_,?_,hout⟩
  · rw [heq]
    exact h
  · rw [Finset.sum_coe_sort U (fun i ↦ ∫ v,
      dist ((EuclideanSpace.equiv _ ℝ).symm (x i).1) v^2 ∂κ i)]
    symm
    apply Finset.sum_subset (Finset.subset_univ U)
    intro i _ hi
    rw [hout i hi]
    simp

variable {E : Type uE} {M : Type uM} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
  {b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
    (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)))} {R ell : ℝ}
  {G : OriginalStageClockGrid} {μ ν : Measure ℝ}
  {h₀ : G.clockSlabSurplus μ ν 0 = 0} {hN : G.clockSlabSurplus μ ν G.count = 0}
  {p : LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker) ×
    TwoMarkedCloudSpace (finrank ℝ S.covector.ker) ℝ ℝ}

/-- The actual single-AE event constructs a source family on all original
FULL labels while retaining precisely its genuine unused arrivals. -/
theorem OriginalUnusedBlockArrivalFamilies.exists_source_fullFamily
    (hp : OriginalUnusedBlockArrivalFamilies.{uE, uM, uI, uI} S w b R ell G h₀ hN p)
    {I : Type uI} [Fintype I] [DecidableEq I] (U : Finset I)
    (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
    (hcount : (∑ i : U, Measure.dirac (x i.val)) =
      (originalUnusedBlockReserveData S w b R ell G h₀ hN p).sourcePortMeasure +
        ∑ j : (originalUnusedBlockReserveData S w b R ell G h₀ hN p).sourceKept,
          Measure.dirac ((originalUnusedBlockReserveData S w b R ell G h₀ hN p).sourceReserve.2 j.val)) :
    let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
    ∃ κ, OriginalFullUnusedArrivalFamilySpec U x G.sourceCell
      (fun i ↦ A.orientedSourceArrivalLaw (G.cut i.val) (G.cut (i.val+1)))
      (A.sourcePortMeasure.real univ + (G.sourceReserveFineBlockPartition h₀ hN).atomEnergy b R 0 1
        (originalSourceReserveExperimentSplice p)) κ := by
  obtain ⟨laws,hs⟩ := hp.1 ↥U (fun i : U ↦ x i.val) hcount
  exact exists_originalUnusedArrivalFamily_extension U x _ _ _ laws hs

/-- The target extension retains its separate Ioc arrivals and original
target labels, including arbitrary empty unused subsets. -/
theorem OriginalUnusedBlockArrivalFamilies.exists_target_fullFamily
    (hp : OriginalUnusedBlockArrivalFamilies.{uE, uM, uI, uI} S w b R ell G h₀ hN p)
    {I : Type uI} [Fintype I] [DecidableEq I] (U : Finset I)
    (x : I → LegalMarkedPhysicalPoint (finrank ℝ S.covector.ker))
    (hcount : (∑ i : U, Measure.dirac (x i.val)) =
      (originalUnusedBlockReserveData S w b R ell G h₀ hN p).targetPortMeasure +
        ∑ j : (originalUnusedBlockReserveData S w b R ell G h₀ hN p).targetKept,
          Measure.dirac ((originalUnusedBlockReserveData S w b R ell G h₀ hN p).targetReserve.2 j.val)) :
    let A := originalUnusedBlockReserveData S w b R ell G h₀ hN p
    ∃ κ, OriginalFullUnusedArrivalFamilySpec U x G.targetCell
      (fun i ↦ A.orientedTargetDepartureLaw (G.cut i.val) (G.cut (i.val+1)))
      (A.targetPortMeasure.real univ + (G.targetReserveFineBlockPartition h₀ hN).atomEnergy b R 1 0
        (originalTargetReserveExperimentSplice p)) κ := by
  obtain ⟨laws,hs⟩ := hp.2 ↥U (fun i : U ↦ x i.val) hcount
  exact exists_originalUnusedArrivalFamily_extension U x _ _ _ laws hs

end OTSelector.Reconstruction
