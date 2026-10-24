import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalActualGridExchange
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Exact stationarity of the actual same-input grid-exchange competitor -/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option linter.unusedSectionVars false
local instance originalGridExchangeStationarityPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance originalGridExchangeStationarityInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
variable {q : ℕ} {ell ε : ℝ} [Fact (0 < ell)]
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {probe : ℝ → ℝ → ℝ} {t : ℝ}

/-- The literal cell exchange commutes with physical rerooting and the
exact integer reindex of the original half-open grid. -/
theorem originalExchangedGridPiece_reroot
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u v : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell)
    (s : LegalMarkedOptimalInputScene q) :
    originalExchangedGridPiece S (g + cavityGridCanonicalOffset (Fin q) ell (u - v))
      (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) =
      localFiniteMapHomeomorph (physicalSceneEdgeReroot v)
        (originalExchangedGridPiece S g (s, u)) := by
  have ho : originalGridRelativeObservation q ell
      (g + cavityGridCanonicalOffset (Fin q) ell (u - v))
      (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) =
      ((g +ᵥ u) - v, legalMarkedInputSceneReroot q v s) := by
    exact Prod.ext (cavityGrid_reindex_base (Fin q) ell g u v) rfl
  have ha := S.relativeActive_reroot (g +ᵥ u) v s
  dsimp only [originalExchangedGridPiece]
  rw [ho]
  dsimp only [originalGridRelativeObservation]
  by_cases h : (g +ᵥ u, s) ∈ S.relativeActive
  · rw [ite_eq_left (ha.mpr h), ite_eq_left h,
      originalCompleteGridPiece_reroot, S.relativePair_reroot,
      originalTwoEdgeSwapPlan_reroot]
  · rw [ite_eq_right (ha.not.mpr h), ite_eq_right h, originalCompleteGridPiece_reroot]

/-- The union of all complete cells is transported exactly, including the
unchanged crossing-edge complement. -/
theorem originalCompleteGridUnion_reroot_iff
    (u v : Fin q → ℝ) (e : LegalMarkedPhysicalEdge q) :
    physicalSceneEdgeReroot v e ∈ ⋃ g,
      originalCompleteGridCell q ell (cavityGridPhaseReroot (Fin q) ell v u) g ↔
      e ∈ ⋃ g, originalCompleteGridCell q ell u g := by
  simp only [mem_iUnion]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g - cavityGridCanonicalOffset (Fin q) ell (u - v), ?_⟩
    apply (originalCompleteGridCell_reroot_iff q ell u v _ e).mp
    simpa only [sub_add_cancel] using hg
  · rintro ⟨g, hg⟩
    exact ⟨_, (originalCompleteGridCell_reroot_iff q ell u v g e).mpr hg⟩

/-- Every original crossing edge is transported without modification. -/
theorem originalCrossingGridPiece_reroot (u v : Fin q → ℝ)
    (s : LegalMarkedOptimalInputScene q) :
    originalCrossingGridPiece q ell
      (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) =
      localFiniteMapHomeomorph (physicalSceneEdgeReroot v)
        (originalCrossingGridPiece q ell (s, u)) := by
  apply Subtype.ext
  change ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).map (physicalSceneEdgeReroot v)).restrict
    (⋃ g, originalCompleteGridCell q ell (cavityGridPhaseReroot (Fin q) ell v u) g)ᶜ =
      ((s.1.1 : Measure (LegalMarkedPhysicalEdge q)).restrict
        (⋃ g, originalCompleteGridCell q ell u g)ᶜ).map (physicalSceneEdgeReroot v)
  rw [Measure.restrict_map (physicalSceneEdgeReroot v).measurable
    (MeasurableSet.iUnion (measurableSet_originalCompleteGridCell _ _ _)).compl]
  have hpre : physicalSceneEdgeReroot v ⁻¹'
      (⋃ g, originalCompleteGridCell q ell (cavityGridPhaseReroot (Fin q) ell v u) g)ᶜ =
      (⋃ g, originalCompleteGridCell q ell u g)ᶜ := by
    ext e
    exact not_congr (originalCompleteGridUnion_reroot_iff u v e)
  rw [hpre]

/-- The actual countable sum transports through the same bijection of all
original lattice cells. -/
theorem originalExchangedGridPiece_sum_reroot
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u v : Fin q → ℝ) (s : LegalMarkedOptimalInputScene q) :
    Measure.sum (fun g ↦ (originalExchangedGridPiece S g
      (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) :
        Measure (LegalMarkedPhysicalEdge q))) =
      (Measure.sum (fun g ↦ (originalExchangedGridPiece S g (s, u) :
        Measure (LegalMarkedPhysicalEdge q)))).map (physicalSceneEdgeReroot v) := by
  let off := cavityGridCanonicalOffset (Fin q) ell (u - v)
  calc
    _ = Measure.sum ((fun g ↦ (originalExchangedGridPiece S g
        (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) :
          Measure (LegalMarkedPhysicalEdge q))) ∘ Equiv.addRight off) :=
      (Measure.sum_comp_equiv (Equiv.addRight off) _).symm
    _ = Measure.sum (fun g ↦ (originalExchangedGridPiece S g (s, u) :
        Measure (LegalMarkedPhysicalEdge q)).map (physicalSceneEdgeReroot v)) := by
      apply congrArg Measure.sum
      funext g
      exact congrArg Subtype.val (originalExchangedGridPiece_reroot S u v g s)
    _ = _ := (Measure.map_sum (physicalSceneEdgeReroot v).measurable.aemeasurable).symm

/-- The entire literal original competitor is covariant under every physical
spatial translation, with its exact same original input and second scene slot. -/
theorem originalGridExchangeScene_reroot
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u v : Fin q → ℝ) (s : LegalMarkedOptimalInputScene q) :
    originalGridExchangeScene S
      (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) =
      legalMarkedInputSceneReroot q v (originalGridExchangeScene S (s, u)) := by
  apply Prod.ext
  · apply Prod.ext
    · apply Subtype.ext
      change (originalCrossingGridPiece q ell
        (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) :
          Measure (LegalMarkedPhysicalEdge q)) + Measure.sum (fun g ↦
            (originalExchangedGridPiece S g
              (legalMarkedInputSceneReroot q v s, cavityGridPhaseReroot (Fin q) ell v u) :
                Measure (LegalMarkedPhysicalEdge q))) =
        ((originalCrossingGridPiece q ell (s, u) : Measure (LegalMarkedPhysicalEdge q)) +
          Measure.sum (fun g ↦ (originalExchangedGridPiece S g (s, u) :
            Measure (LegalMarkedPhysicalEdge q)))).map (physicalSceneEdgeReroot v)
      rw [originalCrossingGridPiece_reroot, originalExchangedGridPiece_sum_reroot,
        Measure.map_add _ _ (physicalSceneEdgeReroot v).measurable]
      rfl
    · rfl
  · rfl

/-- The exact original law times its independent normalized Haar phase,
pushed through the concrete same-input full exchange. -/
def originalGridExchangeLaw
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q)) :
    ProbabilityMeasure (LegalMarkedOptimalInputScene q) :=
  ⟨((Q : Measure (LegalMarkedOptimalInputScene q)).prod
      (cavityGridPhaseLaw (Fin q) ell)).map (originalGridExchangeScene S),
    Measure.isProbabilityMeasure_map (measurable_originalGridExchangeScene S).aemeasurable⟩

/-- Haar phase invariance and exact covariance produce actual stationarity
of the whole same-original-input competitor law. -/
theorem measurePreserving_originalGridExchangeLaw
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hstat : ∀ v : Fin q → ℝ, MeasurePreserving (legalMarkedInputSceneReroot q v)
      (Q : Measure (LegalMarkedOptimalInputScene q)) (Q : Measure (LegalMarkedOptimalInputScene q)))
    (v : Fin q → ℝ) :
    MeasurePreserving (legalMarkedInputSceneReroot q v)
      (originalGridExchangeLaw S Q : Measure (LegalMarkedOptimalInputScene q))
      (originalGridExchangeLaw S Q : Measure (LegalMarkedOptimalInputScene q)) := by
  have hΦ : MeasurePreserving (originalGridExchangeScene S)
      ((Q : Measure (LegalMarkedOptimalInputScene q)).prod (cavityGridPhaseLaw (Fin q) ell))
      (originalGridExchangeLaw S Q : Measure (LegalMarkedOptimalInputScene q)) :=
    ⟨measurable_originalGridExchangeScene S, rfl⟩
  exact hΦ.of_semiconj ((hstat v).prod (measurePreserving_cavityGridPhaseReroot (Fin q) ell v))
    (fun p ↦ originalGridExchangeScene_reroot S p.2 v p.1)
    (continuous_legalMarkedInputSceneReroot q v).measurable

end OTSelector.Reconstruction
