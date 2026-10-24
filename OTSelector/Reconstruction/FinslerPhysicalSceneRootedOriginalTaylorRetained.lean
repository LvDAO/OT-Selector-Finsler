import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMaskedRetainedPacking
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCoreCarrierInclusion
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicTaylorPackingCertificate

/-!
# Original Taylor certificates give loss-free retained-scene packing

The retained original near-event union is recorded jointly with the same full
physical scene. Actual original Taylor control and finite core isolation produce
its local packing budget without a physical-gap or event-inclusion oracle.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold OTSelector.Geometry
  OTSelector.Probability TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators Classical
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore
variable (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
  (i : Fin D.haar.continuous.count)
variable (base : ((D.coreSpatialCoordinateSpace i) × ℝ))


local instance originalTaylorRetainedBudgetStandardBorel :
    StandardBorelSpace ((D.coreSpatialCoordinateSpace i) × ℝ) := inferInstance
local instance originalTaylorRetainedBudgetConfigTopology :
    TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance originalTaylorRetainedBudgetConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace (base := base)
local instance originalTaylorRetainedBudgetConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace (base := base)
local instance originalTaylorRetainedBudgetPlanPolish : PolishSpace
    (LocalFiniteMeasure (((D.coreSpatialCoordinateSpace i) × ℝ) ×
      ((D.coreSpatialCoordinateSpace i) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The actual retained-pair packing budget of one original macro-localized
rectangle. Both indices and original opposite global optimizers are quantified
after the geometric constants; no original population loss is charged. -/
def OriginalFixedSeedMacroRetainedRectangleBudget
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (A B : Set M) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (nearRadius threshold ε phaseSize : ℝ)
    (Emacro : Set (D.coreSpatialCoordinateSpace i))
    (A₀ A₁ B₀ B₁ : Set ((D.coreSpatialCoordinateSpace i) × ℝ)) : Prop :=
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex
  ∀ n : ℕ, ∀ scale : ℝ, threshold ≤ scale →
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
    (D.haar.continuous.coefficient i).seedIndex scale
  ∀ probe : M → M → ℝ, Measurable (Function.uncurry probe) →
  ∀ G : ℝ≥0, (∀ x y, |probe x y| ≤ G) → ∀ t : ℝ, 0 ≤ t →
  ∀ ap am : ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) → M → Fin (n + 1) → ℝ,
  ∀ hpm : ∀ j, Measurable (fun z :
    ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ ap z.1 z.2 j),
  ∀ hmm : ∀ j, Measurable (fun z :
    ((Fin (n + 1) → M) × (Fin (n + 1) → ℝ)) × M ↦ am z.1 z.2 j),
    (∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
        scale ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
          t * probe x (w.1 j)) (ap w)) →
    (∀ᵐ w ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)),
      IsOptimalSemidiscreteAllocation μ w.2 (fun x j ↦
        scale ^ 2 * ((F.lengthEDist x (w.1 j)).toReal - u (w.1 j) + u x) +
          (-t) * probe x (w.1 j)) (am w)) →
  ∀ rootDomain : Set (D.coreSpatialCoordinateSpace i),
  ∀ hrootDomain : volume rootDomain = ENNReal.ofReal ((n : ℝ) + 1),
    (∫⁻ s, ENNReal.ofReal ε * physicalSceneMaskedRetainedAverageWitness base
        Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s
      ∂(actualAllocationRootedMaskedMacroscopicSceneLaw base
        ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ ap am hpm hmm
        (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
        H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
        (D.retainedNearCarrierEvent A B nearRadius)
        (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
        coord (measurable_physicalSceneOriginalSeedScaledPosition
          hF hcomplete hu ha hinj _ scale)
        u (by
          let _inst : MetricSpace M := F.metricSpace
          exact hu.continuous.measurable) scale rootDomain hrootDomain : Measure _)) ≤
      ENNReal.ofReal (t * G) * ENNReal.ofReal phaseSize ^
        Fintype.card (Fin (Module.finrank ℝ
          (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker))

/-- Original Taylor control and original finite-core isolation produce a pure
packing budget for the actual retained pair. Both the physical four-edge gap
and literal event inclusion are constructed internally before either index. -/
theorem exists_original_macroscopic_taylor_retained_witness_budget
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hdim : 2 ≤ Module.finrank ℝ E) (m : Measure E) [m.IsAddHaarMeasure]
    (hμchart : ∀ old : M, (μ.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    (hνchart : ∀ old : M, (ν.restrict (extChartAt 𝓘(ℝ, E) old).source).map
      (extChartAt 𝓘(ℝ, E) old) ≪ m)
    {Acompact A B : Set M}
    (hAcompact : IsCompact Acompact) (hμAcompact : ∀ᵐ x ∂μ, x ∈ Acompact)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAreg : A ⊆ F.potentialRegularDomain u) (hBreg : B ⊆ F.potentialRegularDomain u)
    (nearRadius : ℝ)
    {macroCenter : ℚ → M} (hmacroCenter : macroCenter ∈ (D.haar.continuous.coefficient i).roots)
    (R sL sR tL tR : ℝ)
    (hs : Icc sL sR ⊆ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
      ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))
    (ht : Icc tL tR ⊆ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
      ((D.haar.continuous.coefficient i).window.val.2.1 : ℝ))
    (hclockgap : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ tL - sR)
    (γ : ℝ) (hγ : 0 < γ) :
    ∃ ε > 0, ∃ T : (D.haar.continuous.coefficient i).TaylorRootCover ε,
    ∃ Acert : (D.haar.continuous.coefficient i).ActualMacroscopicTaylorCertificate
      T (D.haar.continuous.coefficient i).roots macroCenter,
    ∃ macroRadius > 0, ∃ threshold > 0,
    ∀ ξ η : Fin 2 → ((D.coreSpatialCoordinateSpace i) × ℝ),
      (∀ k, ‖(ξ k).1‖ < R) → (∀ k, ‖(η k).1‖ < R) →
      (∀ k, (ξ k).2 ∈ Ioo sL sR) → (∀ k, (η k).2 ∈ Ioo tL tR) →
      γ < (D.haar.continuous.coefficient i).frozenQuadraticCost Acert.frozenCenter (ξ 0) (η 0) +
        (D.haar.continuous.coefficient i).frozenQuadraticCost Acert.frozenCenter (ξ 1) (η 1) -
        (D.haar.continuous.coefficient i).frozenQuadraticCost Acert.frozenCenter (ξ 0) (η 1) -
        (D.haar.continuous.coefficient i).frozenQuadraticCost Acert.frozenCenter (ξ 1) (η 0) →
      ∃ idx : CavityBasisCycleIndex
        (cavitySpatialBasis (ι := Fin (Module.finrank ℝ
          (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) (A := ℝ))
        (cavitySpatialBasis (ι := Fin (Module.finrank ℝ
          (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) (A := ℝ)),
        γ < (idx.2 : ℝ) ∧
        CavityLegalBasisCycleValid
          ((D.haar.continuous.coefficient i).frozenQuadraticCost Acert.frozenCenter)
          ((D.haar.continuous.coefficient i).frozenClockRadiusOpenRectangle R sL sR tL tR) idx ∧
        (ξ 0, η 0) ∈ idx.1.1.1.val ×ˢ idx.1.1.2.val ∧
        (ξ 1, η 1) ∈ idx.1.2.1.val ×ˢ idx.1.2.2.val ∧
        ∃ phaseSize > 0, ∃ offset : D.coreSpatialCoordinateSpace i,
          (∀ s ∈ idx.1.1.1.val ∪ idx.1.2.1.val,
            s.1 - offset ∈ cavityGridPhaseCell _ phaseSize) ∧
          D.OriginalFixedSeedMacroRetainedRectangleBudget i base hF hcomplete hu ha hinj
            A B hA hB nearRadius threshold (γ / 2) phaseSize
            (Metric.ball (D.coreMacroLabel i macroCenter) macroRadius)
            idx.1.1.1.val idx.1.2.1.val idx.1.1.2.val idx.1.2.2.val := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := lambda) C.seedIndex
  let Ks := a ⁻¹' C.roots ∩ A
  let Kt := a ⁻¹' C.roots ∩ B
  obtain ⟨ρ, hρ, S, hS, hinc⟩ :=
    D.exists_rooted_retainedNearCarrier_inclusion_selectedCoreProduct
      hF hcomplete hu ha hinj i A B R nearRadius
  have hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    rw [← D.haar.intensity_roots i]
    exact (D.haar.intensity i).continuous_label
  have hsource : ∀ x ∈ H ∩ Ks, a x ∈ C.roots ∧ x ∈ F.potentialRegularDomain u :=
    fun _ hx ↦ ⟨hx.2.1, hAreg hx.2.2⟩
  have htarget : ∀ y ∈ Kt, a y ∈ C.roots ∧ y ∈ F.potentialRegularDomain u :=
    fun _ hy ↦ ⟨hy.1, hBreg hy.2⟩
  obtain ⟨ε, hε, T, Acert, ST, hST, hcertificate⟩ :=
    C.exists_actualMacroscopicTaylor_legal_masked_packing_certificate hF hcomplete hu ha hinj
      hlabel (D.source_remainder_on_piece hF hcomplete hu ha hinj i) horder
      C.roots_compact Subset.rfl hmacroCenter H Ks Kt hsource htarget
      R sL sR tL tR hs ht hclockgap γ hγ
  let macroRadius := min Acert.macroRadius ρ
  have hmacroRadius : 0 < macroRadius := lt_min Acert.macroRadius_pos hρ
  let threshold := max S ST
  have hthreshold : 0 < threshold := hS.trans_le (le_max_left _ _)
  refine ⟨ε, hε, T, Acert, macroRadius, hmacroRadius, threshold, hthreshold, ?_⟩
  intro ξ η hξR hηR hξclock hηclock hcycle
  obtain ⟨idx, hidxgap, hlegal, hleft, hright, hdisj, hdisjt,
      ⟨phaseSize, hphaseSize, offset, hbox⟩, hphysical⟩ :=
    hcertificate ξ η hξR hηR hξclock hηclock hcycle
  refine ⟨idx, hidxgap, hlegal, hleft, hright, phaseSize, hphaseSize, offset, hbox, ?_⟩
  have hsourceR : ∀ s ∈ idx.1.1.1.val ∪ idx.1.2.1.val, ‖s.1‖ ≤ R := by
    intro s hs
    rcases hs with hs | hs
    · exact (hlegal.2 s hs (η 0) hleft.2 (ξ 1) hright.1 (η 1) hright.2).1.2.1.le
    · exact (hlegal.2 (ξ 0) hleft.1 (η 0) hleft.2 s hs (η 1) hright.2).2.1.2.1.le
  let Emacro := Metric.ball (D.coreMacroLabel i macroCenter) macroRadius
  have hmacroSub : Emacro ⊆ D.coreMacroLabelWindow i ρ := by
    intro z hz
    apply Set.mem_iUnion.mpr ⟨macroCenter, ?_⟩
    apply Set.mem_iUnion.mpr ⟨hmacroCenter, ?_⟩
    exact (Metric.mem_ball.mp hz).trans_le (min_le_right _ _)
  dsimp only [OriginalFixedSeedMacroRetainedRectangleBudget]
  intro n scale hscale probe hprobe G hprobeBound t ht0 ap am hpm hmm hp hm
    rootDomain hrootDomain
  have hscaleS : S ≤ scale := (le_max_left S ST).trans hscale
  have hscaleT : ST ≤ scale := (le_max_right S ST).trans hscale
  apply lintegral_original_iid_finsler_masked_retained_macroscopic_witness_le base
    hF hcomplete hdim m μ ν hμchart hνchart hAcompact hμAcompact u hu
    (scale ^ 2) (pow_ne_zero _ (ne_of_gt (hthreshold.trans_le hscale)))
    probe hprobe G hprobeBound t ht0 ap am hpm hmm hp hm H Ks Kt
    (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
    ((C.roots_compact.measurableSet.preimage ha).inter hA)
    ((C.roots_compact.measurableSet.preimage ha).inter hB)
    (physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale)
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ scale)
    idx.1.1.1.val idx.1.2.1.val idx.1.1.2.val idx.1.2.2.val
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.1.1.property)
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.2.1.property)
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.1.2.property)
    (isTopologicalBasis_cavitySpatialBasis.isOpen idx.1.2.2.property)
    hdisj phaseSize hphaseSize offset hbox Emacro Metric.isOpen_ball scale
    (γ / 2) (by positivity) ?_
    (D.retainedNearCarrierEvent A B nearRadius)
    (D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA hB nearRadius)
    (fun root hroot e he hobs ↦
      hinc (idx.1.1.1.val ×ˢ idx.1.1.2.val) (idx.1.2.1.val ×ˢ idx.1.2.2.val)
        (fun q hq ↦ hsourceR q.1
          (hq.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1))) scale hscaleS root
        (by simpa only [← physicalSceneMacroscopicRoot_eq_inv_smul] using hmacroSub hroot)
        e he hobs) rootDomain hrootDomain
  apply Eventually.of_forall
  intro Y root hroot x hx x' hx' hAx hAx' j hj hBy l hl hBy'
  have hmacro : dist (physicalSceneMacroscopicRoot scale root)
      ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFun
        (populationSeedRootLabelValue (P C.seedIndex).seed a macroCenter)) < Acert.macroRadius :=
    (Metric.mem_ball.mp hroot).trans_le (min_le_left _ _)
  exact hphysical scale hscaleT root hmacro n Y x hx x' hx' hAx hAx' j hj hBy l hl hBy'

end PopulationLocalPressureCore
end OTSelector.Reconstruction
