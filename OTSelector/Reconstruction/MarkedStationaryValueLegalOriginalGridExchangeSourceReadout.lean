import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalActualGridExchange
import OTSelector.Reconstruction.MarkedStationaryValueLegalOriginalGridPhaseMeanSaving
import Mathlib.Topology.Compactness.LocallyFinite

/-! The literal global competitor has the exact source-window signed readout. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option linter.unusedSectionVars false

variable {q : ℕ} {ell ε : ℝ}
  {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ} {probe : ℝ → ℝ → ℝ} {t : ℝ}

/-- An actual compact physical observation window meets only finitely many
of the existing closed spatial cell envelopes. -/
theorem finite_originalGridSourceWindowCells (u : Fin q → ℝ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K) :
    {g : CavityGridLattice (Fin q) ell |
      (originalClosedSpatialGridCell q ell u g ∩ K).Nonempty}.Finite :=
  (locallyFinite_originalClosedSpatialGridCell q ell u).finite_nonempty_inter_compact hK

/-- A single actual complete-cell exchange has precisely its literal signed
source-atom gain, using only the original occupied unit atoms. -/
theorem IsFullOriginalInputMatching.exchangedGridPiece_sourceWindow_gain
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u : Fin q → ℝ) (g : CavityGridLattice (Fin q) ell)
    (w : (Fin q → ℝ) → ℝ)
    (hi : Integrable (fun e : LegalMarkedPhysicalEdge q ↦
      w e.1.1 * originalWeightedEdgeCost kin probe t e)
      (originalCompleteGridPiece q ell g (s, u) : Measure (LegalMarkedPhysicalEdge q))) :
    (∫ e : LegalMarkedPhysicalEdge q, w e.1.1 * originalWeightedEdgeCost kin probe t e
      ∂(originalCompleteGridPiece q ell g (s, u) : Measure (LegalMarkedPhysicalEdge q))) -
      (∫ e : LegalMarkedPhysicalEdge q, w e.1.1 * originalWeightedEdgeCost kin probe t e
        ∂(originalExchangedGridPiece S g (s, u) : Measure (LegalMarkedPhysicalEdge q))) =
      S.sourceWindowGain w (g +ᵥ u, s) := by
  let o := originalGridRelativeObservation q ell g (s, u)
  by_cases ha : (g +ᵥ u, s) ∈ S.relativeActive
  · have hc := originalExchangedGridPiece_certificate S g (s, u) ha
    have hp := S.relativePair_support (g +ᵥ u) s hs ha
    have he := hs.completeGridPiece_singleton_eq_one ell u g hp.1 hc.2.1
    have hf := hs.completeGridPiece_singleton_eq_one ell u g hp.2 hc.2.2.1
    rw [S.sourceWindowGain_eq_relativePair]
    rw [ite_eq_left ha]
    have hn : originalExchangedGridPiece S g (s, u) =
        originalTwoEdgeSwapPlan (originalCompleteGridPiece q ell g (s, u))
          (S.relativePair o).1 (S.relativePair o).2 := by
      exact ite_eq_left ha
    rw [hn]
    exact integral_originalTwoEdgeSwapPlan_sourceWindow_gain _ hc.1 he hf _ _ hi
  · rw [S.sourceWindowGain_eq_relativePair, ite_eq_right ha]
    have hn : originalExchangedGridPiece S g (s, u) =
        originalCompleteGridPiece q ell g (s, u) := ite_eq_right ha
    rw [hn, sub_self]

/-- No complete-cell exchange can destroy integrability of an original
physical source observable. -/
theorem integrable_originalExchangedGridPiece_sourceWindow
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (s : LegalMarkedOptimalInputScene q) (u : Fin q → ℝ)
    (g : CavityGridLattice (Fin q) ell) (w : (Fin q → ℝ) → ℝ)
    (hi : Integrable (fun e : LegalMarkedPhysicalEdge q ↦
      w e.1.1 * originalWeightedEdgeCost kin probe t e)
      (originalCompleteGridPiece q ell g (s, u) : Measure (LegalMarkedPhysicalEdge q))) :
    Integrable (fun e : LegalMarkedPhysicalEdge q ↦
      w e.1.1 * originalWeightedEdgeCost kin probe t e)
      (originalExchangedGridPiece S g (s, u) : Measure (LegalMarkedPhysicalEdge q)) := by
  dsimp only [originalExchangedGridPiece]
  split_ifs
  · exact integrable_originalTwoEdgeSwapPlan _ _ _ hi
  · exact hi

/-- The actual countable glued matching retains source-window integrability,
and its exact signed difference is the already averaged literal cell gain.
The finite set of affected cells is produced from the compact window. -/
theorem IsFullOriginalInputMatching.gridExchange_sourceWindow_integrable_and_gain
    {s : LegalMarkedOptimalInputScene q} (hs : IsFullOriginalInputMatching q s)
    (hell : 0 < ell)
    (S : OriginalOriginCycleSelector q (originalWeightedEdgeCost kin probe t) ell ε)
    (u : Fin q → ℝ) (w : (Fin q → ℝ) → ℝ)
    {K : Set (Fin q → ℝ)} (hK : IsCompact K)
    (hw : ∀ x ∉ K, w x = 0)
    (hi : Integrable (fun e : LegalMarkedPhysicalEdge q ↦
      w e.1.1 * originalWeightedEdgeCost kin probe t e)
      (s.1.1 : Measure (LegalMarkedPhysicalEdge q))) :
    Integrable (fun e : LegalMarkedPhysicalEdge q ↦
      w e.1.1 * originalWeightedEdgeCost kin probe t e)
      ((originalGridExchangeScene S (s, u)).1.1 : Measure (LegalMarkedPhysicalEdge q)) ∧
      originalWeightedSourceReadout kin probe t w s -
        originalWeightedSourceReadout kin probe t w (originalGridExchangeScene S (s, u)) =
        ∑' g : CavityGridLattice (Fin q) ell, S.sourceWindowGain w (g +ᵥ u, s) := by
  let f : LegalMarkedPhysicalEdge q → ℝ :=
    fun e ↦ w e.1.1 * originalWeightedEdgeCost kin probe t e
  let μ₀ : Measure (LegalMarkedPhysicalEdge q) := originalCrossingGridPiece q ell (s, u)
  let μ : CavityGridLattice (Fin q) ell → Measure (LegalMarkedPhysicalEdge q) :=
    fun g ↦ originalCompleteGridPiece q ell g (s, u)
  let ν : CavityGridLattice (Fin q) ell → Measure (LegalMarkedPhysicalEdge q) :=
    fun g ↦ originalExchangedGridPiece S g (s, u)
  have hdec : (s.1.1 : Measure (LegalMarkedPhysicalEdge q)) = μ₀ + Measure.sum μ :=
    measure_eq_crossing_add_completeGridPieces q hell u _
  have hold : Integrable f (μ₀ + Measure.sum μ) := hdec ▸ hi
  have h₀ := (integrable_add_measure.mp hold).1
  have hμ := (integrable_add_measure.mp hold).2
  have hν (g : CavityGridLattice (Fin q) ell) : Integrable f (ν g) :=
    integrable_originalExchangedGridPiece_sourceWindow S s u g w
      (hμ.mono_measure (Measure.le_sum _ g))
  let A := {g : CavityGridLattice (Fin q) ell |
    (originalClosedSpatialGridCell q ell u g ∩ K).Nonempty}
  have hA : A.Finite := finite_originalGridSourceWindowCells u hK
  have hz (g : CavityGridLattice (Fin q) ell) (hg : g ∉ A) : f =ᵐ[ν g] 0 := by
    filter_upwards [(ν g).support_mem_ae] with e he
    have hcell := support_originalExchangedGridPiece_subset_closed S g (s, u) he
    have hnot : e.1.1 ∉ K := fun heK ↦ hg ⟨e.1.1, hcell.1, heK⟩
    exact mul_eq_zero_of_left (hw e.1.1 hnot) _
  have hsumν : Summable (fun g ↦ ∫ e, ‖f e‖ ∂ν g) := by
    apply summable_of_ne_finset_zero (s := hA.toFinset)
    intro g hg
    apply integral_eq_zero_of_ae
    filter_upwards [hz g (by simpa only [Set.Finite.mem_toFinset] using hg)] with e he
    simp only [he, Pi.zero_apply, norm_zero]
  have hνsum : Integrable f (Measure.sum ν) := integrable_sum_measure hν hsumν
  have hnew : Integrable f (μ₀ + Measure.sum ν) := h₀.add_measure hνsum
  refine ⟨hnew, ?_⟩
  change (∫ e, f e ∂(s.1.1 : Measure (LegalMarkedPhysicalEdge q))) -
    (∫ e, f e ∂(μ₀ + Measure.sum ν)) = _
  rw [hdec, integral_add_measure h₀ hμ, integral_add_measure h₀ hνsum]
  rw [add_sub_add_left_eq_sub, integral_sum_measure hμ, integral_sum_measure hνsum]
  rw [← (hasSum_integral_measure hμ).summable.tsum_sub
    (hasSum_integral_measure hνsum).summable]
  apply tsum_congr
  intro g
  exact hs.exchangedGridPiece_sourceWindow_gain S u g w
    (hμ.mono_measure (Measure.le_sum _ g))

end OTSelector.Reconstruction
