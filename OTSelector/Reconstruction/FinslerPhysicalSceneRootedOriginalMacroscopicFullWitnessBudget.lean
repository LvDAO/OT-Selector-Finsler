import OTSelector.Reconstruction.FinslerPhysicalSceneRootedRetainedCoreCarrierInclusion
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedNonNearFullMass
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicEventWitnessBudget

/-!
# Actual full macroscopic witness budget from original union loss and true energy

One positive physical non-near gap, one macroscopic isolation window, and one
spatial scale threshold are selected before the sample size and actual global
allocation families. The actual retained-edge mass and rooted inclusion are
produced internally. The remaining geometric premise is the original physical
four-edge certificate on the selected endpoint core product.
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


local instance originalFullBudgetStandardBorel :
    StandardBorelSpace ((D.coreSpatialCoordinateSpace i) × ℝ) := inferInstance
local instance originalFullBudgetConfigTopology : TopologicalSpace (LocalConfiguration base) :=
  vagueTopology base
local instance originalFullBudgetConfigBorel : BorelSpace (LocalConfiguration base) :=
  vagueBorelSpace (base := base)
local instance originalFullBudgetConfigPolish : PolishSpace (LocalConfiguration base) :=
  vaguePolishSpace (base := base)
local instance originalFullBudgetPlanPolish : PolishSpace
    (LocalFiniteMeasure (((D.coreSpatialCoordinateSpace i) × ℝ) ×
      ((D.coreSpatialCoordinateSpace i) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- Original full non-near mass and actual macroscopic isolation eliminate both
exceptional-mass and retained-edge inclusion premises from the full witness budget.
All population losses refer to the complete original finite union of physical cores. -/
theorem exists_original_fixed_seed_macroscopic_full_witness_budget
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
    {A B : Set M} (hA : IsCompact A) (hB : MeasurableSet B)
    (hμA : μ Aᶜ = 0) (hνB : ν Bᶜ = 0)
    {gap nearRadius : ℝ} (hgap_pos : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (hnearRadius : 0 < nearRadius)
    (hwindow : ∀ j, ((D.haar.continuous.coefficient j).window.val.2.2 : ℝ) ≤ gap / 2)
    (R : ℝ) :
    ∃ c > 0, ∃ macroRadius > 0, ∃ threshold > 0,
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) (D.haar.continuous.coefficient i).seedIndex
    let Ks := a ⁻¹' (D.haar.continuous.coefficient i).roots ∩ A
    let Kt := a ⁻¹' (D.haar.continuous.coefficient i).roots ∩ B
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
    ∀ Energy : ℝ≥0∞,
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ ap (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy →
      (∫⁻ w, ∫⁻ p, ENNReal.ofReal (scale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
        ∂physicalSceneGlobalAllocationFamily μ am (fun w ↦ w.1) w
        ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Energy →
    ∀ A₀ A₁ B₀ B₁ : Set ((D.coreSpatialCoordinateSpace i) × ℝ),
      IsOpen A₀ → IsOpen A₁ → IsOpen B₀ → IsOpen B₁ → Disjoint A₀ A₁ →
      (∀ s ∈ A₀ ∪ A₁, ‖s.1‖ ≤ R) →
    ∀ phaseSize : ℝ, 0 < phaseSize → ∀ offset : D.coreSpatialCoordinateSpace i,
      (∀ s ∈ A₀ ∪ A₁, s.1 - offset ∈ cavityGridPhaseCell _ phaseSize) →
    ∀ U : Set (D.coreSpatialCoordinateSpace i), MeasurableSet U → volume U ≠ ⊤ →
      (∀ s ∈ A₀, s.1 ∈ U) → (∀ s ∈ A₁, s.1 ∈ U) →
    ∀ Emacro : Set (D.coreSpatialCoordinateSpace i), IsOpen Emacro →
      Emacro ⊆ D.coreMacroLabelWindow i macroRadius →
    ∀ ε : ℝ, 0 ≤ ε →
      (∀ᵐ Y ∂Measure.pi (fun _ : Fin (n + 1) ↦ ν),
        ∀ z ∈ physicalSceneMacroscopicRoot scale ⁻¹' Emacro,
        ∀ x ∈ H ∩ Ks, ∀ x' ∈ H ∩ Ks,
          (coord x - z, u x) ∈ A₀ → (coord x' - z, u x') ∈ A₁ →
        ∀ j, Y j ∈ Kt → (coord (Y j) - z, u (Y j)) ∈ B₀ →
        ∀ l, Y l ∈ Kt → (coord (Y l) - z, u (Y l)) ∈ B₁ →
          ε ≤ scale ^ 2 * ((F.lengthEDist x (Y j)).toReal - u (Y j) + u x) +
            scale ^ 2 * ((F.lengthEDist x' (Y l)).toReal - u (Y l) + u x') -
            scale ^ 2 * ((F.lengthEDist x (Y l)).toReal - u (Y l) + u x) -
            scale ^ 2 * ((F.lengthEDist x' (Y j)).toReal - u (Y j) + u x')) →
    ∀ rootDomain : Set (D.coreSpatialCoordinateSpace i),
    ∀ hrootDomain : volume rootDomain = ENNReal.ofReal ((n : ℝ) + 1),
      (∫⁻ s, ENNReal.ofReal ε * physicalSceneMacroscopicAverageWitness base
          Emacro (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) s
        ∂(actualAllocationRootedMacroscopicSceneLaw base
          ((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n)) μ ap am hpm hmm
          (fun w ↦ w.1) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
          H (measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj _)
          coord (measurable_physicalSceneOriginalSeedScaledPosition
            hF hcomplete hu ha hinj _ scale)
          u (by
            let _inst : MetricSpace M := F.metricSpace
            exact hu.continuous.measurable) scale rootDomain hrootDomain : Measure _)) ≤
        ENNReal.ofReal (t * G) * ENNReal.ofReal phaseSize ^
          Fintype.card (Fin (Module.finrank ℝ
            (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) +
          ENNReal.ofReal ε * (volume U *
            (μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
              Energy / ENNReal.ofReal (scale ^ 2 * c))) := by
  let _inst : MetricSpace M := F.metricSpace
  let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instPolish : PolishSpace M := inferInstance
  let C := D.haar.continuous.coefficient i
  let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
    (lambda := lambda) C.seedIndex
  let Ks := a ⁻¹' C.roots ∩ A
  let Kt := a ⁻¹' C.roots ∩ B
  have hμAae : ∀ᵐ x ∂μ, x ∈ A := by
    apply ae_iff.mpr
    exact hμA
  have hH : MeasurableSet H :=
    measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
  have hroots := C.roots_compact.measurableSet.preimage ha
  have hKs : MeasurableSet Ks := hroots.inter hA.measurableSet
  have hKt : MeasurableSet Kt := hroots.inter hB
  obtain ⟨c, hc, hmass⟩ := D.exists_original_fullNonNear_mass_bound
    hF hcomplete hu ha hinj horder hA.measurableSet hB hμA hνB
      hgap_pos hdist hnearRadius hwindow
  obtain ⟨macroRadius, hmacroRadius, threshold, hthreshold, hinc⟩ :=
    D.exists_rooted_retainedNearCarrier_inclusion_selectedCoreProduct
      hF hcomplete hu ha hinj i A B R nearRadius
  refine ⟨c, hc, macroRadius, hmacroRadius, threshold, hthreshold, ?_⟩
  dsimp only
  intro n scale hs probe hprobe G hprobeBound t ht ap am hpm hmm hp hm Energy hEp hEm
    A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj hR phaseSize hphase offset hbox
    U hU hUf hA₀U hA₁U Emacro hEmacro hEmacroSub ε hε hgap rootDomain hrootDomain
  have hscale : 0 < scale := hthreshold.trans_le hs
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj C.seedIndex scale
  let Egood := D.retainedNearCarrierEvent A B nearRadius
  let Cbad := μ (⋃ j, D.physicalCoreDomain j)ᶜ + ν (⋃ j, D.physicalCoreDomain j)ᶜ +
    Energy / ENNReal.ofReal (scale ^ 2 * c)
  have hEgood : MeasurableSet Egood :=
    D.measurableSet_retainedNearCarrierEvent hF hcomplete hu ha hinj hA.measurableSet hB nearRadius
  have hCp : (∫⁻ w, physicalSceneGlobalAllocationFamily μ ap (fun w ↦ w.1) w Egoodᶜ
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Cbad :=
    hmass n ap hpm (hp.mono fun _ h ↦ h.1) (scale ^ 2) (sq_pos_of_pos hscale) Energy hEp
  have hCm : (∫⁻ w, physicalSceneGlobalAllocationFamily μ am (fun w ↦ w.1) w Egoodᶜ
      ∂((Measure.pi (fun _ : Fin (n + 1) ↦ ν)).prod (dirichletOne n))) ≤ Cbad :=
    hmass n am hmm (hm.mono fun _ h ↦ h.1) (scale ^ 2) (sq_pos_of_pos hscale) Energy hEm
  have hsource : ∀ q ∈ (A₀ ×ˢ B₀) ∪ (A₁ ×ˢ B₁), ‖q.1.1‖ ≤ R := by
    intro q hq
    exact hR q.1 (hq.elim (fun h ↦ Or.inl h.1) (fun h ↦ Or.inr h.1))
  have hinc' : ∀ z ∈ physicalSceneMacroscopicRoot scale ⁻¹' Emacro, ∀ e ∈ Egood ∩ (H ×ˢ univ),
      physicalSceneRootedObservation coord u z e ∈ (A₀ ×ˢ B₀) ∪ (A₁ ×ˢ B₁) →
      e ∈ Ks ×ˢ Kt := by
    intro z hz e he hobs
    have hmacroEq : physicalSceneMacroscopicRoot scale z = scale⁻¹ • z := by
      ext k
      simp [physicalSceneMacroscopicRoot, div_eq_mul_inv, mul_comm]
    have hz' : scale⁻¹ • z ∈ D.coreMacroLabelWindow i macroRadius := by
      rw [← hmacroEq]
      exact hEmacroSub hz
    exact hinc (A₀ ×ˢ B₀) (A₁ ×ˢ B₁) hsource scale hs z hz' e he hobs
  exact lintegral_original_iid_finsler_macroscopic_average_cycle_witness_le_event_mass base
    hF hcomplete hdim m μ ν hμchart hνchart hA hμAae u hu
    (scale ^ 2) (pow_ne_zero 2 hscale.ne') probe hprobe G hprobeBound t ht
    ap am hpm hmm hp hm H Ks Kt hH hKs hKt coord hcoord
    A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁ hdisj phaseSize hphase offset hbox
    Emacro hEmacro scale
    U hU hUf hA₀U hA₁U ε hε hgap Egood hEgood Cbad hCp hCm hinc' rootDomain hrootDomain

end PopulationLocalPressureCore
end OTSelector.Reconstruction
