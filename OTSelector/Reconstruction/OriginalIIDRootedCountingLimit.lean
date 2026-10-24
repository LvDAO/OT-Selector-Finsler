import OTSelector.Reconstruction.OriginalIIDRootedInputCounts
import OTSelector.Reconstruction.FinslerPhysicalSceneLimitClock
import OTSelector.Reconstruction.OriginalIIDBipartiteMacroScene
import OTSelector.Reconstruction.MarkedStationaryValueLegalInputCounting

/-! Integer edge counts of the unchanged original iid optimizer survive its
actual source mask, sample-size rooting, and any existing joint weak limit. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false
variable {M ι : Type*} [MeasurableSpace M] [Fintype ι]
local instance rootedCountingPlanPolish : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance rootedCountingConfigurationTopology
    {X : Type*} [MetricSpace X] [ProperSpace X] (base : X) :
    TopologicalSpace (LocalConfiguration base) := vagueTopology base

/-- The original source mask selects precisely the original optimizer's
unit edge atoms, even when the coordinate map is not injective. -/
theorem originalIIDOptimalPhysicalPlan_restricted_rooted_eq_counted_edges
    {n : ℕ} [NeZero n] (cost : M → M → ℝ) (scale : ℝ)
    (ξ : (Fin n → M) × (Fin n → M))
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (z : ι → ℝ) :
    physicalSceneRootedPlan
      ((originalIIDOptimalPhysicalPlan cost scale ξ).restrict (H ×ˢ univ))
      coord u (n : ℝ) z =
      ∑ i ∈ Finset.univ.filter (fun i ↦ ξ.1 i ∈ H),
        Measure.dirac (physicalSceneRootedObservation coord u z
          (ξ.1 i, ξ.2 (firstOptimalAssignment
            (fun i j ↦ scale * cost (ξ.1 i) (ξ.2 j)) i))) := by
  classical
  ext V hV
  rw [physicalSceneRootedPlan, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_physicalSceneRootedObservation coord hcoord u hu z) hV,
    Measure.restrict_apply (hV.preimage
      (measurable_physicalSceneRootedObservation coord hcoord u hu z))]
  simp only [originalIIDOptimalPhysicalPlan, empiricalMeasure, Measure.smul_apply,
    smul_eq_mul, Measure.finsetSum_apply]
  rw [← mul_assoc, ENNReal.ofReal_natCast, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top n), one_mul]
  have hmask := (hV.preimage
    (measurable_physicalSceneRootedObservation coord hcoord u hu z)).inter
      (hH.prod MeasurableSet.univ)
  simp only [Finset.sum_filter, Measure.dirac_apply' _ hmask,
    Measure.dirac_apply' _ hV]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : ξ.1 i ∈ H <;> simp [Set.indicator_apply, hi]

/-- Finite original masked optimizer observations are integer measures. -/
theorem isLegalCountingMeasure_originalIIDOptimalPhysicalPlan_rooted_restrict
    {n : ℕ} [NeZero n] (cost : M → M → ℝ) (scale : ℝ)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (w : ((Fin n → M) × (Fin n → M)) × (ι → ℝ)) :
    IsLegalCountingMeasure (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
      (physicalSceneRootedLocalPlan
        (fun ξ ↦ (originalIIDOptimalPhysicalPlan cost scale ξ).restrict (H ×ˢ univ))
        coord u (n : ℝ) w) := by
  classical
  let J := Finset.univ.filter (fun i : Fin n ↦ w.1.1 i ∈ H)
  let edge := fun i : J ↦ physicalSceneRootedObservation coord u w.2
    (w.1.1 i, w.1.2 (firstOptimalAssignment
      (fun i j ↦ scale * cost (w.1.1 i) (w.1.2 j)) i))
  let e := (Fintype.equivFin J).symm
  refine ⟨ofTuple 0 (fun i ↦ edge (e i)), ?_⟩
  apply Subtype.ext
  change countingMeasure (ofTuple 0 (fun i ↦ edge (e i))) =
    physicalSceneRootedPlan
      ((originalIIDOptimalPhysicalPlan cost scale w.1).restrict (H ×ˢ univ))
      coord u (n : ℝ) w.2
  rw [countingMeasure_ofTuple,
    originalIIDOptimalPhysicalPlan_restricted_rooted_eq_counted_edges
      cost scale w.1 H hH coord hcoord u hu w.2]
  exact (e.sum_comp (fun i ↦ Measure.dirac (edge i))).trans
    (Finset.sum_coe_sort J (fun i ↦ Measure.dirac
      (physicalSceneRootedObservation coord u w.2
        (w.1.1 i, w.1.2 (firstOptimalAssignment
          (fun i j ↦ scale * cost (w.1.1 i) (w.1.2 j)) i)))))

/-- A continuous readout of any joint weak limit retains its closed integer
measure carrier; the original scene law and all correlations are unchanged. -/
theorem ae_isLegalCountingMeasure_of_continuous_readout_tendsto
    {X S : Type*} [MetricSpace X] [ProperSpace X] [MeasurableSpace X]
    [BorelSpace X] [SecondCountableTopology X]
    [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S] [HasOuterApproxClosed S]
    (base : X) (read : S → LocalFiniteMeasure X) (hread : Continuous read)
    (P : ℕ → ProbabilityMeasure S) (Q : ProbabilityMeasure S)
    (hweak : Tendsto P atTop (𝓝 Q))
    (hcount : ∀ n, ∀ᵐ s ∂(P n : Measure S), IsLegalCountingMeasure base (read s)) :
    ∀ᵐ s ∂(Q : Measure S), IsLegalCountingMeasure base (read s) := by
  let K : Set S := {s | IsLegalCountingMeasure base (read s)}
  have hK : IsClosed K := (isClosed_isLegalCountingMeasure base).preimage hread
  have hn (n : ℕ) : (P n : Measure S) Kᶜ = 0 := hcount n
  have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hweak hK.isOpen_compl
  change (Q : Measure S) Kᶜ ≤ atTop.liminf (fun n ↦ (P n : Measure S) Kᶜ) at hle
  simp only [hn, liminf_const] at hle
  exact le_antisymm hle bot_le

/-- The actual rooted iid law, with the original source mask, is carried by
integer edge measures in both copies of its unchanged optimal plan. -/
theorem ae_isLegalCountingMeasure_originalIID_restricted_rooted_law
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u)
    (D : Set (ι → ℝ)) (hD : volume D = ENNReal.ofReal ((n : ℝ) + 1)) :
    let P := (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := originalIIDOptimalPhysicalPlan (n := n + 1) cost scale
    let hΓ := measurable_originalIIDOptimalPhysicalPlan (n := n + 1) cost hcost scale
    ∀ᵐ s ∂(physicalSceneRestrictedRootedLocalSceneLaw P Γ Γ hΓ hΓ H hH
      coord hcoord u hu ((n : ℝ) + 1) (by positivity) D hD :
        Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      IsLegalCountingMeasure (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) s.1 ∧
      IsLegalCountingMeasure (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) s.2 := by
  intro P Γ hΓ
  let Γr := fun ξ ↦ (Γ ξ).restrict (H ×ˢ univ)
  have hr : Measurable Γr := measurable_physicalPlan_sourceRestriction Γ hΓ H hH
  let K : Set (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) := {s |
    IsLegalCountingMeasure 0 s.1 ∧ IsLegalCountingMeasure 0 s.2}
  have hK : IsClosed K :=
    ((isClosed_isLegalCountingMeasure (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))).preimage
      continuous_fst).inter
      ((isClosed_isLegalCountingMeasure (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))).preimage
        continuous_snd)
  apply (ae_map_iff (measurable_physicalSceneRootedLocalScene Γr Γr hr hr
    coord hcoord u hu ((n : ℝ) + 1)).aemeasurable hK.measurableSet).mpr
  apply Eventually.of_forall
  intro w
  have hc := isLegalCountingMeasure_originalIIDOptimalPhysicalPlan_rooted_restrict
    cost scale H hH coord hcoord u hu w
  have hc' : IsLegalCountingMeasure 0
      (physicalSceneRootedLocalPlan Γr coord u ((n : ℝ) + 1) w) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hc
  exact ⟨hc', hc'⟩

/-- Every existing weak subsequence of the actual sample-size rooted laws
retains integer edges. No new compactness or extraction assumption is used. -/
theorem ae_isLegalCountingMeasure_of_originalIID_rooted_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (scale : ℕ → ℝ) (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (D : ℕ → Set (ι → ℝ))
    (hD : ∀ n, volume (D n) = ENNReal.ofReal ((n : ℝ) + 1))
    (φ : ℕ → ℕ)
    (Q : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))) :
    let P := fun n ↦ (Measure.pi (fun _ : Fin (n + 1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n + 1) ↦ ν))
    let Γ := fun n ↦ originalIIDOptimalPhysicalPlan (n := n + 1) (cost n) (scale n)
    let hΓ := fun n ↦ measurable_originalIIDOptimalPhysicalPlan
      (n := n + 1) (cost n) (hcost n) (scale n)
    let laws := fun n ↦ physicalSceneRestrictedRootedLocalSceneLaw
      (P n) (Γ n) (Γ n) (hΓ n) (hΓ n) (H n) (hH n)
      (coord n) (hcoord n) u hu ((n : ℝ) + 1) (by positivity) (D n) (hD n)
    Tendsto (fun n ↦ laws (φ n)) atTop (𝓝 Q) →
    ∀ᵐ s ∂(Q : Measure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))),
      IsLegalCountingMeasure (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) s.1 ∧
      IsLegalCountingMeasure (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) s.2 := by
  intro P Γ hΓ laws hweak
  have hn (n : ℕ) := ae_isLegalCountingMeasure_originalIID_restricted_rooted_law
    μ ν (cost (φ n)) (hcost (φ n)) (scale (φ n)) (φ n) (H (φ n)) (hH (φ n))
    (coord (φ n)) (hcoord (φ n)) u hu (D (φ n)) (hD (φ n))
  filter_upwards [ae_isLegalCountingMeasure_of_continuous_readout_tendsto
    0 Prod.fst continuous_fst (fun n ↦ laws (φ n)) Q hweak (fun n ↦ (hn n).mono fun _ h ↦ h.1),
    ae_isLegalCountingMeasure_of_continuous_readout_tendsto
    0 Prod.snd continuous_snd (fun n ↦ laws (φ n)) Q hweak (fun n ↦ (hn n).mono fun _ h ↦ h.2)]
    with s hs ht
  exact ⟨hs, ht⟩

section BipartiteMacro
variable (base : (ι → ℝ) × ℝ)
local instance rootedCountingMacroStandardBorel : StandardBorelSpace ((ι → ℝ) × ℝ) :=
  inferInstance
local instance rootedCountingMacroConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace
local instance rootedCountingMacroConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace
set_option quotPrecheck false
local notation "Macro" => (ι → ℝ) ×
  (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) × LocalConfiguration base)
local instance rootedCountingMacroMetrizable : MetrizableSpace (Macro × Macro) :=
  inferInstance
local instance rootedCountingMacroPseudoMetrizable : PseudoMetrizableSpace (Macro × Macro) :=
  MetrizableSpace.toPseudoMetrizableSpace (X := Macro × Macro)

/-- Both full input observations retain the same original masked integer
optimizer in each plan coordinate, before averaging over any iid or root law. -/
theorem isLegalCountingMeasure_originalIIDBipartiteMacroObservation
    (cost : M → M → ℝ) (scale : ℝ) (n : ℕ)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (spatialScale : ℝ)
    (w : ((Fin (n + 1) → M) × (Fin (n + 1) → M)) × (ι → ℝ)) :
    let s := originalIIDBipartiteMacroObservation base cost scale n H coord u spatialScale w
    IsLegalCountingMeasure 0 s.1.2.1.1 ∧ IsLegalCountingMeasure 0 s.1.2.1.2 ∧
      IsLegalCountingMeasure 0 s.2.2.1.1 ∧ IsLegalCountingMeasure 0 s.2.2.1.2 := by
  have hc := isLegalCountingMeasure_originalIIDOptimalPhysicalPlan_rooted_restrict
    cost scale H hH coord hcoord u hu w
  simpa only [originalIIDBipartiteMacroObservation, physicalSceneRootedMacroscopicObservation,
    physicalSceneRootedCountableObservation, physicalSceneRootedLocalScene,
    Nat.cast_add, Nat.cast_one] using And.intro hc (And.intro hc (And.intro hc hc))

/-- Every actual joint iid/input/macro law is carried by integer edge plans,
with its original source mask and original optimizer/input correlations. -/
theorem ae_isLegalCountingMeasure_originalIIDBipartiteMacroLaw
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (scale : ℝ) (n : ℕ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) :
    ∀ᵐ s ∂(originalIIDBipartiteMacroLaw base μ ν hq cost hcost scale n H hH
      coord hcoord u hu : Measure (Macro × Macro)),
      IsLegalCountingMeasure 0 s.1.2.1.1 ∧ IsLegalCountingMeasure 0 s.1.2.1.2 ∧
      IsLegalCountingMeasure 0 s.2.2.1.1 ∧ IsLegalCountingMeasure 0 s.2.2.1.2 := by
  let K : Set (Macro × Macro) := {s |
    IsLegalCountingMeasure 0 s.1.2.1.1 ∧ IsLegalCountingMeasure 0 s.1.2.1.2 ∧
      IsLegalCountingMeasure 0 s.2.2.1.1 ∧ IsLegalCountingMeasure 0 s.2.2.1.2}
  have hc := isClosed_isLegalCountingMeasure
    (0 : (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)))
  have hK : IsClosed K :=
    (hc.preimage continuous_fst.snd.fst.fst).inter
      ((hc.preimage continuous_fst.snd.fst.snd).inter
        ((hc.preimage continuous_snd.snd.fst.fst).inter
          (hc.preimage continuous_snd.snd.fst.snd)))
  apply (ae_map_iff (measurable_originalIIDBipartiteMacroObservation base
    cost hcost scale n H hH coord hcoord u hu _).aemeasurable hK.measurableSet).mpr
  exact Eventually.of_forall fun w ↦
    isLegalCountingMeasure_originalIIDBipartiteMacroObservation base
      cost scale n H hH coord hcoord u hu _ w

/-- Any already extracted common bipartite macro weak limit retains all four
plan-coordinate integer carriers at the actual sample-size prefactor. -/
theorem ae_isLegalCountingMeasure_of_originalIIDBipartiteMacroLaw_tendsto
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hq : 0 < Fintype.card ι)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (scale : ℕ → ℝ) (H : ℕ → Set M) (hH : ∀ n, MeasurableSet (H n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (φ : ℕ → ℕ)
    (Q : ProbabilityMeasure (Macro × Macro))
    (hweak : Tendsto (fun n ↦ originalIIDBipartiteMacroLaw base μ ν hq
      (cost (φ n)) (hcost (φ n)) (scale (φ n)) (φ n) (H (φ n)) (hH (φ n))
      (coord (φ n)) (hcoord (φ n)) u hu) atTop (𝓝 Q)) :
    ∀ᵐ s ∂(Q : Measure (Macro × Macro)),
      IsLegalCountingMeasure 0 s.1.2.1.1 ∧ IsLegalCountingMeasure 0 s.1.2.1.2 ∧
      IsLegalCountingMeasure 0 s.2.2.1.1 ∧ IsLegalCountingMeasure 0 s.2.2.1.2 := by
  let laws := fun n ↦ originalIIDBipartiteMacroLaw base μ ν hq
    (cost (φ n)) (hcost (φ n)) (scale (φ n)) (φ n) (H (φ n)) (hH (φ n))
    (coord (φ n)) (hcoord (φ n)) u hu
  have hn (n : ℕ) := ae_isLegalCountingMeasure_originalIIDBipartiteMacroLaw base
    μ ν hq (cost (φ n)) (hcost (φ n)) (scale (φ n)) (φ n) (H (φ n)) (hH (φ n))
    (coord (φ n)) (hcoord (φ n)) u hu
  filter_upwards [ae_isLegalCountingMeasure_of_continuous_readout_tendsto
      0 (fun s : Macro × Macro ↦ s.1.2.1.1) continuous_fst.snd.fst.fst laws Q hweak
      (fun n ↦ (hn n).mono fun _ h ↦ h.1),
    ae_isLegalCountingMeasure_of_continuous_readout_tendsto
      0 (fun s : Macro × Macro ↦ s.1.2.1.2) continuous_fst.snd.fst.snd laws Q hweak
      (fun n ↦ (hn n).mono fun _ h ↦ h.2.1),
    ae_isLegalCountingMeasure_of_continuous_readout_tendsto
      0 (fun s : Macro × Macro ↦ s.2.2.1.1) continuous_snd.snd.fst.fst laws Q hweak
      (fun n ↦ (hn n).mono fun _ h ↦ h.2.2.1),
    ae_isLegalCountingMeasure_of_continuous_readout_tendsto
      0 (fun s : Macro × Macro ↦ s.2.2.1.2) continuous_snd.snd.fst.snd laws Q hweak
      (fun n ↦ (hn n).mono fun _ h ↦ h.2.2.2)] with s h1 h2 h3 h4
  exact ⟨h1,h2,h3,h4⟩
end BipartiteMacro

end OTSelector.Reconstruction
