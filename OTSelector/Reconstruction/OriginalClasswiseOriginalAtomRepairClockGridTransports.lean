import OTSelector.Reconstruction.OriginalLegalScreeningComparatorClockBlockEndpointsTransport
import OTSelector.Reconstruction.OriginalStageClockSlabsLabels

/-! Simultaneous genuine transports on every actual half-open clock stage. -/
open Set Function Filter MeasureTheory Module Manifold TopologicalSpace
open scoped ENNReal Topology ContDiff Distributions
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace OTSelector.Reconstruction
open OTSelector.Geometry ContinuousFinslerNorm OTSelector.Probability
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {S : CalibratedLevelSeedPatch F u} {w : S.covector.ker}
namespace OriginalSeedConditionalMoments
variable {μ ν : Measure ℝ} (D : OriginalSeedConditionalMoments S w μ ν)
include D

/-- Each actual grid stage gets its real Neumann plan on one common scene
event. Local floors may differ by block, and no floor is imposed on zero stages. -/
theorem exists_originalClockGrid_stageTransports
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (hq : 2 < finrank ℝ S.covector.ker)
    {gap diameter : ℝ} (hbounds : ConditionalClockSupportBounds μ ν gap diameter)
    {g : ℝ → ℝ → ℝ}
    (Q : LegalWeightedStationaryPoissonMatching (finrank ℝ S.covector.ker) μ ν
      (D.originalFocalKinetic gap) g)
    (G : OriginalStageClockGrid)
    (b : OrthonormalBasis (Fin (finrank ℝ S.covector.ker)) ℝ
      (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))))
    {R ell : ℝ} (hell : 1 ≤ ell) (hR : 2*(originalStageFrameCollarFactor b*ell) ≤ R)
    (hj : ∀ i : Fin G.count, ∀ k, MemLp (fun scene ↦ originalSeedPathClockSetCurrent S w
      (originalEuclideanMollifier _) (Ioc (G.cut i.val) (G.cut (i.val+1))) scene k) 2
      (Q.law : Measure _)) :
    ∃ K : Fin G.count → Compacts (Fin (finrank ℝ S.covector.ker) → ℝ),
      (∀ i, originalCenteredPhysicalCubeRegion b (2*R) ⊆ interior (K i : Set _)) ∧
      ∀ᵐ scene ∂(Q.law : Measure (LegalMarkedOptimalInputScene (finrank ℝ S.covector.ker))),
      ∀ (i : Fin G.count) (A : OriginalOrientedStageResidualDensityData S w b R ell),
        A.scene = scene →
      0 ≤ A.gamma (G.cut i.val) → 0 ≤ A.gamma (G.cut (i.val+1)) →
      IsFiniteMeasure (A.orientedBackgroundLaw (G.cut i.val)) ∧
      IsFiniteMeasure (A.orientedBackgroundLaw (G.cut (i.val+1))) ∧
      ∀ ρ : ℝ, 0 < ρ →
        ρ ≤ A.gamma (G.cut i.val) +
          (originalStageRemainingReserveClassCount A.sourceReserve A.sourceKept (G.sourceCell i) : ℝ) / A.cubeVolume →
        ρ ≤ A.gamma (G.cut (i.val+1)) +
          (originalStageRemainingReserveClassCount A.targetReserve A.targetKept (G.targetCell i) : ℝ) / A.cubeVolume →
      ∀ ε : ℝ, 0 < ε → ∃ Γ : Measure (EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker)) ×
          EuclideanSpace ℝ (Fin (finrank ℝ S.covector.ker))),
        IsFiniteMeasure Γ ∧
        Γ.fst = A.orientedBackgroundLaw (G.cut i.val) + A.orientedSourceArrivalLaw (G.cut i.val) (G.cut (i.val+1)) ∧
        Γ.snd = A.orientedBackgroundLaw (G.cut (i.val+1)) + A.orientedTargetDepartureLaw (G.cut i.val) (G.cut (i.val+1)) ∧
        Integrable (fun z ↦ dist z.1 z.2^2) Γ ∧
        (∫ z, dist z.1 z.2^2 ∂Γ) ≤
          ρ⁻¹ * originalOrientedStageCurrentInputNeumannBudget S w Q b (K i) R ell
            (G.cut i.val) (G.cut (i.val+1)) (hj i) scene + ε := by
  have hh (i : Fin G.count) := D.ae_all_originalOrientedStageBackground_exists_quadratic_coupling
    hF hw hq hbounds Q b hell hR (G.strictMono.monotone (Nat.le_succ i.val)) (hj i)
  choose K hK hplans using hh
  refine ⟨K,hK,?_⟩
  filter_upwards [ae_all_iff.mpr hplans] with scene hscene
  intro i A hA hgs hgt
  exact hscene i A hA hgs hgt

end OriginalSeedConditionalMoments
end OTSelector.Reconstruction
