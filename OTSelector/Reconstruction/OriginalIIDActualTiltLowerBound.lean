import OTSelector.Reconstruction.OriginalIIDActualKineticBound
import OTSelector.Reconstruction.OriginalIIDShiftedTiltLocalReadout
import OTSelector.Reconstruction.FinslerOriginalAtlasEnergyBudget
import OTSelector.Reconstruction.OriginalIIDSeedMaskedEnergyBudget
import OTSelector.Reconstruction.OriginalIIDTranslatedCoreEscape
import OTSelector.Reconstruction.OriginalIIDSharpWindowExhaustion
import OTSelector.MeasureTheory.ShiftedIntegralMassCancellation

/-! Sharp signed tilt lower passage for one unchanged original iid experiment.
The physical readout is localized to the original root cell before its bounded
shift is cancelled, so no core/global mass difference is silently discarded. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [local instance] kineticFinitePlanPolish kineticFinitePlanNonempty

/-- A bounded readout may be restricted to its actual source cell at the
price of its literal window mass outside that cell. No unbounded physical
energy is used to pay the discarded bounded readout. -/
theorem cavityRootWindowReadout_restrict_le_add_outside_mass
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Γ : Measure Ω) (coord : Ω → (ι → ℝ)) (hcoord : Measurable coord)
    (readout : Ω → ℝ≥0∞) (B : ℝ≥0∞) (hB : ∀ p, readout p ≤ B)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (root : ι → ℝ)
    (S : Set Ω) (hS : MeasurableSet S) :
    cavityRootWindowReadout Γ coord readout U root ≤
      cavityRootWindowReadout (Γ.restrict S) coord readout U root +
        B*Γ ({p | coord p-root ∈ U} ∩ Sᶜ) := by
  let W := {p | coord p-root ∈ U}
  have hW : MeasurableSet W := hU.preimage (hcoord.sub_const root)
  have heq : Γ.restrict S+Γ.restrict Sᶜ = Γ := Measure.restrict_add_restrict_compl hS
  have hsplit : cavityRootWindowReadout Γ coord readout U root =
      cavityRootWindowReadout (Γ.restrict S) coord readout U root +
        cavityRootWindowReadout (Γ.restrict Sᶜ) coord readout U root := by
    change (∫⁻ p, W.indicator readout p ∂Γ) = _
    conv_lhs => rw [← heq]
    exact lintegral_add_measure _ _ _
  rw [hsplit]
  apply add_le_add le_rfl
  calc
    _ ≤ ∫⁻ p, W.indicator (fun _ ↦ B) p ∂Γ.restrict Sᶜ := by
      apply lintegral_mono
      intro p
      change W.indicator readout p ≤ W.indicator (fun _ ↦ B) p
      by_cases hp : p ∈ W
      · simpa only [Set.indicator_of_mem hp] using hB p
      · simp only [Set.indicator_of_notMem hp,le_refl]
    _ = _ := by
      rw [lintegral_indicator hW,lintegral_const,Measure.restrict_apply_univ,Measure.restrict_apply hW]


/-- The literal discarded source-window count is itself a measurable
window readout, with the original measure and exact source complement. -/
theorem cavityRootWindowReadout_indicator_eq_mass
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (Γ : Measure Ω) (coord : Ω → (ι → ℝ)) (hcoord : Measurable coord)
    (S : Set Ω) (hS : MeasurableSet S)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (root : ι → ℝ) :
    cavityRootWindowReadout Γ coord (S.indicator (fun _ ↦ (1 : ℝ≥0∞))) U root =
      Γ ({p | coord p-root ∈ U} ∩ S) := by
  let W := {p | coord p-root ∈ U}
  have hW : MeasurableSet W := hU.preimage (hcoord.sub_const root)
  change (∫⁻ p, W.indicator (S.indicator (fun _ ↦ (1 : ℝ≥0∞))) p ∂Γ) = _
  rw [lintegral_indicator hW,lintegral_indicator hS,lintegral_one,
    Measure.restrict_apply_univ,Measure.restrict_apply hS,inter_comm]

/-- The actual measurable source escape may be added to an arbitrary old
Taylor guard without assuming measurability of that old guard. -/
theorem lintegral_originalIID_guard_add_source_escape
    {M : Type*} [MeasurableSpace M] {q n : ℕ}
    (μ ν : Measure M) (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (Fin q → ℝ)) (hcoord : Measurable coord)
    (S : Set M) (hS : MeasurableSet S)
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (offset : Fin q → ℝ) (N : ℝ) (roots : Set (Fin q → ℝ))
    (guard : ((Fin (n+1) → M) × (Fin (n+1) → M)) → (Fin q → ℝ) → ℝ≥0∞) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let escape := fun ξ root ↦ ENNReal.ofReal N*
      ((originalIIDOptimalPhysicalPlan (n := n+1) cost k ξ).restrict (H ×ˢ univ))
        ({p | coord p.1-(root+offset) ∈ U} ∩ (S ×ˢ univ)ᶜ)
    (∫⁻ ξ, ∫⁻ root, guard ξ root+escape ξ root
      ∂cavityRootMeasure volume roots N ∂law) =
      (∫⁻ ξ, ∫⁻ root, guard ξ root ∂cavityRootMeasure volume roots N ∂law) +
      (∫⁻ ξ, ∫⁻ root, escape ξ root ∂cavityRootMeasure volume roots N ∂law) := by
  intro law escape
  have hsplit := lintegral_originalIID_physical_window_add_guard μ ν cost hcost k H hH coord hcoord
    ((S ×ˢ univ)ᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞)))
    (measurable_const.indicator (hS.prod MeasurableSet.univ).compl) U hU offset N 1 roots guard
  have heq (ξ : (Fin (n+1) → M) × (Fin (n+1) → M)) (root : Fin q → ℝ) :
      ENNReal.ofReal N*cavityRootWindowReadout
        ((originalIIDOptimalPhysicalPlan (n := n+1) cost k ξ).restrict (H ×ˢ univ))
        (fun p ↦ coord p.1) ((S ×ˢ univ)ᶜ.indicator (fun _ ↦ (1 : ℝ≥0∞))) U (root+offset) = escape ξ root := by
    exact congrArg (fun z : ℝ≥0∞ ↦ ENNReal.ofReal N*z)
      (cavityRootWindowReadout_indicator_eq_mass _ (fun p : M × M ↦ coord p.1)
        (hcoord.comp measurable_fst) _ (hS.prod MeasurableSet.univ).compl U hU (root+offset))
  simp_rw [heq] at hsplit
  simp only [ENNReal.ofReal_one,one_mul] at hsplit
  calc
    _ = ∫⁻ ξ, ∫⁻ root, escape ξ root+guard ξ root
        ∂cavityRootMeasure volume roots N ∂law := by
      apply lintegral_congr
      intro ξ
      exact lintegral_congr (fun root ↦ add_comm _ _)
    _ = _ := hsplit.trans (add_comm _ _)

/-- The finite actual readouts retain their physical source-mask energy
inside the liminf. Every finite auxiliary cell shares this budget once. -/
theorem originalIID_finite_cell_readouts_le_masked_liminf
    {I M : Type*} [Fintype I] [MeasurableSpace M] {q : ℕ}
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (Fin q → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (physicalEnergy : ℕ → M × M → ℝ) (he : ∀ n, Measurable (physicalEnergy n))
    (ε B : ℝ) (s : ℕ → ℝ) (hs : ∀ n, s n ≠ 0)
    (center : I → (Fin q → ℝ))
    (domains : ℕ → I → Set (Fin q → ℝ)) (hdomains : ∀ n i, MeasurableSet (domains n i))
    (cells : I → Set (Fin q → ℝ)) (hcells : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j)))
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ (∞ : ℝ≥0∞))
    (guard : I → (n : ℕ) → ((Fin (n+1) → M) × (Fin (n+1) → M)) → (Fin q → ℝ) → ℝ≥0∞)
    (guardBudget : I → ℝ≥0∞)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (cell : I → ℝ≥0∞) :
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := fun n ξ ↦ originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
    let roots := fun n i ↦ domains n i ∩
      (fun root ↦ center i+physicalSceneMacroscopicRoot (s n) root) ⁻¹' cells i
    (∀ᶠ n in atTop, ∀ i, (∫⁻ ξ, ∫⁻ root, guard i n ξ root
      ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n) ≤ guardBudget i) →
    (∀ i, cell i ≤ liminf (fun r ↦ ∫⁻ ξ, ∫⁻ root,
      ENNReal.ofReal ((m r : ℝ)+1)*cavityRootWindowReadout
        ((Γ (m r) ξ).restrict (H ×ˢ univ)) (fun e ↦ coord (m r) e.1)
        (fun e ↦ ENNReal.ofReal (physicalEnergy (m r) e+ε)) U (root+s (m r) • center i) +
          ENNReal.ofReal B*guard i (m r) ξ root
        ∂cavityRootMeasure volume (roots (m r) i) ((m r : ℝ)+1) ∂law (m r)) atTop) →
    (∑ i, cell i) ≤ volume U*((liminf (fun r ↦ ∫⁻ ξ, ∫⁻ e, ENNReal.ofReal (physicalEnergy (m r) e)
        ∂(Γ (m r) ξ).restrict (H ×ˢ univ) ∂law (m r)) atTop)+ENNReal.ofReal ε*μ H) +
      ENNReal.ofReal B*∑ i, guardBudget i := by
  intro law Γ roots hguard hlocal
  let f := fun i n ↦ ∫⁻ ξ, ∫⁻ root,
    ENNReal.ofReal ((n : ℝ)+1)*cavityRootWindowReadout
      ((Γ n ξ).restrict (H ×ˢ univ)) (fun e ↦ coord n e.1)
      (fun e ↦ ENNReal.ofReal (physicalEnergy n e+ε)) U (root+s n • center i) +
        ENNReal.ofReal B*guard i n ξ root
      ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n
  let actualEnergy := fun n ↦ ∫⁻ ξ, ∫⁻ e, ENNReal.ofReal (physicalEnergy n e)
    ∂(Γ n ξ).restrict (H ×ˢ univ) ∂law n
  let total := fun n ↦ volume U*(actualEnergy n+ENNReal.ofReal ε*μ H) +
    ENNReal.ofReal B*∑ i, guardBudget i
  have hsplit (i : I) (n : ℕ) : f i n =
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1)*cavityRootWindowReadout
        ((Γ n ξ).restrict (H ×ˢ univ)) (fun e ↦ coord n e.1)
        (fun e ↦ ENNReal.ofReal (physicalEnergy n e+ε)) U (root+s n • center i)
        ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n) +
      ENNReal.ofReal B*(∫⁻ ξ, ∫⁻ root, guard i n ξ root
        ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n) :=
    lintegral_originalIID_physical_window_add_guard μ ν (cost n) (hcost n) (k n) H hH
      (coord n) (hcoord n) (fun e ↦ ENNReal.ofReal (physicalEnergy n e+ε))
      ((he n).add_const ε).ennreal_ofReal U hU (s n • center i) ((n : ℝ)+1) B
      (roots n i) (guard i n)
  have hshared : ∀ᶠ n in atTop, (∑ i, f i n) ≤ total n := by
    filter_upwards [hguard] with n hg
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    apply add_le_add
    · exact (lintegral_originalIID_translated_window_sum_le_masked μ ν n (cost n) (hcost n) (k n)
        H hH (coord n) (hcoord n) (physicalEnergy n) (he n) ε (hs n) center
        (domains n) (hdomains n) cells hcells hdisjoint U hU hUf)
    · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hg i)) bot_le
  have hresult := fixedCandidate_sum_cell_liminf_le_shared_budget cell
    (fun i n ↦ f i (m n)) (fun r ↦ total (m r)) hlocal (hm.eventually hshared)
  change _ ≤ liminf (fun r ↦ volume U*(actualEnergy (m r)+ENNReal.ofReal ε*μ H) +
    ENNReal.ofReal B*∑ i, guardBudget i) atTop at hresult
  rw [liminf_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault),
    ENNReal.liminf_const_mul_of_ne_top hUf,
    liminf_add_const atTop _ _ (by isBoundedDefault) (by isBoundedDefault)] at hresult
  exact hresult


variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


/-- The actual sharp finite comparison keeps only the original root cell in
its physical RHS. Its new guard is the literal bounded-window source escape. -/
theorem PopulationLocalPressureCore.exists_uniform_original_shifted_tilt_cell_restricted_local_readout_le
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (i : Fin D.haar.continuous.count)
    (energy : (ℚ → M) × PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) → ℝ)
    (heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t * g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖)
    (ψ : ℝ × ℝ → ℝ≥0∞) (hψ : ∀ clocks, ψ clocks ≤ 1)
    (hψzero : ∀ clocks, clocks ∉ (D.haar.continuous.coefficient i).window.region →
      ψ clocks = 0)
    (center : D.coreSpatialCoordinateSpace i) (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ],
      ∀ (S : Set (M × M)), MeasurableSet S → ∀ B : ℝ,
      ∀ U : Set (D.coreSpatialCoordinateSpace i), MeasurableSet U →
      ∀ (z : ℚ → M) (root : D.coreSpatialCoordinateSpace i),
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex scale
      let shifted := fun x ↦ coord x-scale • center
      let Γclock := Γ.restrict {p | (u p.1,u p.2) ∈
        (D.haar.continuous.coefficient i).window.region}
      cavityRootWindowReadout Γ (fun p ↦ shifted p.1)
        (fun p ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (z,((u p.1,u p.2),shifted p.2-shifted p.1))))) U root ≤
      cavityRootWindowReadout (Γ.restrict S) (fun p ↦ coord p.1)
        (fun p ↦ ENNReal.ofReal (scale^2 *
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)) U (root+scale • center) +
      ENNReal.ofReal B * (D.originalTaylorGuardMass i R scale U z (root+scale • center) Γclock +
        Γ ({p | coord p.1-(root+scale • center) ∈ U} ∩ Sᶜ)) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  obtain ⟨threshold,hthreshold,hpoint⟩ :=
    D.exists_uniform_original_shifted_tilt_clock_cutoff_translated_local_readout_le
      hF hcomplete hu ha hinj horder g t i energy heq ψ hψ hψzero center R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ S hS B U hU z root coord shifted Γclock
  let readout := fun p : M × M ↦ ψ (u p.1,u p.2)*min (ENNReal.ofReal B)
    (ENNReal.ofReal (energy (z,((u p.1,u p.2),shifted p.2-shifted p.1))))
  have hcap (p : M × M) : readout p ≤ ENNReal.ofReal B := by
    exact (mul_le_mul (hψ _) (min_le_left _ _) bot_le bot_le).trans_eq (one_mul _)
  have hcoord : Measurable (fun p : M × M ↦ shifted p.1) :=
    ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ scale).sub
      measurable_const).comp measurable_fst
  have hsplit := cavityRootWindowReadout_restrict_le_add_outside_mass Γ (fun p ↦ shifted p.1)
    hcoord readout (ENNReal.ofReal B) hcap U hU root S hS
  have hsets : {p : M × M | shifted p.1-root ∈ U} =
      {p | coord p.1-(root+scale • center) ∈ U} := by
    ext p
    have heq : shifted p.1-root = coord p.1-(root+scale • center) := by
      dsimp only [shifted]
      abel
    exact (congrArg (fun x ↦ x ∈ U) heq).to_iff
  rw [hsets] at hsplit
  have hlocal := hpoint scale hs (Γ.restrict S) B U hU z root
  let C := {p : M × M | (u p.1,u p.2) ∈ (D.haar.continuous.coefficient i).window.region}
  have hguard : D.originalTaylorGuardMass i R scale U z (root+scale • center)
      ((Γ.restrict S).restrict C) ≤ D.originalTaylorGuardMass i R scale U z (root+scale • center) Γclock :=
    Measure.restrict_mono_measure Measure.restrict_le_self C _
  have hlocal' := add_le_add hlocal (le_rfl : ENNReal.ofReal B *
    Γ ({p | coord p.1-(root+scale • center) ∈ U} ∩ Sᶜ) ≤ _)
  apply hsplit.trans (hlocal'.trans ?_)
  rw [mul_add,←add_assoc]
  exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hguard bot_le)) le_rfl

/-- Actual tagged LSC and sharp Taylor readout with literal source-cell
restriction. The extra bounded source escape stays in the true finite guard. -/
theorem PopulationLocalPressureCore.exists_translated_fixed_candidate_cell_restricted_tilt_liminf
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (i : Fin D.haar.continuous.count)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (H : Set M) (hH : MeasurableSet H)
    (S : Set (M × M)) (hS : MeasurableSet S)
    (ψ : C(ℝ × ℝ,ℝ)) (hψrange : ∀ clocks, ψ clocks ∈ Icc 0 1)
    (hψsupport : tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region)
    (center : D.coreSpatialCoordinateSpace i) (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) :
    let q := finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker
    let s := physicalSceneCanonicalHaarScale q
    let rootDomain := physicalSceneCanonicalHaarDomain q
    let tag := fun n ↦ physicalSceneMacroscopicRoot (s n)
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ :=
      fun n ξ ↦ (originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)
    let Γcell := fun n ξ ↦ (Γ n ξ).restrict S
    let Γclock := fun n ξ ↦ (Γ n ξ).restrict {p | (u p.1,u p.2) ∈
      (D.haar.continuous.coefficient i).window.region}
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (s n)
    let shifted := fun n x ↦ coord n x-s n • center
    let rootValue := physicalSceneOriginalMacroRootValue (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex
    ∃ energy : C(D.coreSpatialCoordinateSpace i × PhysicalPairPalmMark (Fin q),ℝ),
      (∀ p, 0 ≤ energy p) ∧
      (∀ z ∈ (D.haar.continuous.coefficient i).roots,
        ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
          energy (D.coreMacroLabel i z,(clocks,disp)) =
            matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t * g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖) ∧
      ∀ (base : ((Fin q → ℝ) × ℝ)) (m : ℕ → ℕ), Tendsto m atTop atTop →
      ∀ (Q : ProbabilityMeasure ((Fin q → ℝ) × CavityLocalScene
          (((Fin q) → ℝ) × ℝ) (((Fin q) → ℝ) × ℝ))),
      Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw base μ ν
        (by simpa only [Fintype.card_fin] using hq)
        (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH (shifted (m n))
        ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (s (m n))).sub
          measurable_const)
        u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable))
        atTop (𝓝 Q) →
      ∀ (A : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet A →
        A ⊆ (fun w ↦ center+w) ⁻¹'
          (D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots) →
      ∀ B : ℝ, ∀ (U : Set (D.coreSpatialCoordinateSpace i)),
        IsOpen U → palmUnitCube (Fin q) ⊆ U →
      (∫⁻ w, ∫⁻ mark, ENNReal.ofReal (ψ mark.1) *
        min (ENNReal.ofReal B) (ENNReal.ofReal (energy (center+w,mark)))
        ∂cubePalm (Fin q) (physicalScenePairCampbell ((Q : Measure ((Fin q → ℝ) × CavityLocalScene
          ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).condKernel w))
        ∂(Q : Measure ((Fin q → ℝ) × CavityLocalScene
          ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).fst.restrict A) ≤
      liminf (fun n ↦ ∫⁻ ξ, ∫⁻ root,
        ENNReal.ofReal ((m n : ℝ)+1) * cavityRootWindowReadout (Γcell (m n) ξ)
          (fun p ↦ coord (m n) p.1)
          (fun p ↦ ENNReal.ofReal ((s (m n))^2 *
            ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)) U
          (root+s (m n) • center) +
        ENNReal.ofReal B * (ENNReal.ofReal ((m n : ℝ)+1) *
          (D.originalTaylorGuardMass i R (s (m n)) U
            (rootValue (center+tag (m n) root)) (root+s (m n) • center) (Γclock (m n) ξ) +
            Γ (m n) ξ ({p | coord (m n) p.1-(root+s (m n) • center) ∈ U} ∩ Sᶜ)))
        ∂cavityRootMeasure volume (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1)
        ∂law (m n)) atTop := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro q s rootDomain tag law Γ Γcell Γclock coord shifted rootValue
  obtain ⟨energy,he0,heq'⟩ := D.exists_original_macro_continuous_shifted_matrix_energy
    hF hcomplete hu ha hinj g t i
  have heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (D.coreMacroLabel i z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t * g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖ := by
    simpa using heq'
  refine ⟨energy,he0,heq,?_⟩
  intro base m hm Q hweak A hA hAsub B U hU hsub
  have hshifted (n : ℕ) : Measurable (shifted n) :=
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (s n)).sub
      measurable_const
  let Ftrunc : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal (ψ p.2.1) * min (ENNReal.ofReal B) (ENNReal.ofReal (energy (center+p.1,p.2)))
  have htranslate : Continuous (fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
      (center+p.1,p.2)) := (continuous_const.add continuous_fst).prodMk continuous_snd
  have hc : Continuous Ftrunc :=
    (ENNReal.continuous_ofReal.comp (ψ.continuous.comp continuous_snd.fst)).ennreal_mul
      (continuous_const.min (ENNReal.continuous_ofReal.comp (energy.continuous.comp htranslate)))
      (fun p ↦ Or.inr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)))
      (fun p ↦ Or.inr ENNReal.ofReal_ne_top)
  have hPalm := lintegral_originalIID_conditional_palm_le_liminf_sourceWindow
    base μ ν hq cost hcost k H hH shifted hshifted u hu.continuous.measurable
    m Q hweak A hA U hU hsub Ftrunc hc.lowerSemicontinuous
  refine hPalm.trans (liminf_le_liminf ?_)
  let Eread := fun p : (ℚ → M) × PhysicalPairPalmMark (Fin q) ↦
    energy (D.coreMacroLabel i p.1,p.2)
  have hψle : ∀ clocks, ENNReal.ofReal (ψ clocks) ≤ 1 :=
    fun clocks ↦ ENNReal.ofReal_le_one.mpr (hψrange clocks).2
  have hψzero : ∀ clocks, clocks ∉ (D.haar.continuous.coefficient i).window.region →
      ENNReal.ofReal (ψ clocks) = 0 := by
    intro clocks hclocks
    have hn : clocks ∉ tsupport ψ := fun h ↦ hclocks (hψsupport h)
    rw [image_eq_zero_of_notMem_tsupport hn,ENNReal.ofReal_zero]
  obtain ⟨threshold,hthreshold,hpoint⟩ :=
    D.exists_uniform_original_shifted_tilt_cell_restricted_local_readout_le
      hF hcomplete hu ha hinj horder g t i Eread heq (fun clocks ↦ ENNReal.ofReal (ψ clocks))
      hψle hψzero center R hR hε
  have hinverse (z : ℚ → M) (hz : z ∈ (D.haar.continuous.coefficient i).roots) :
      rootValue (D.coreMacroLabel i z) = z :=
    physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj _
      ((D.haar.continuous.coefficient i).roots_subset_piece hz)
  have hmacro (c : D.coreSpatialCoordinateSpace i)
      (hc : c ∈ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots) :
      D.coreMacroLabel i (rootValue c) = c := by
    obtain ⟨z,hz,rfl⟩ := hc
    rw [hinverse z hz]
  have hlarge : ∀ᶠ n in atTop, threshold ≤ s (m n) :=
    ((tendsto_physicalSceneCanonicalHaarScale q hq).comp hm).eventually
      (eventually_ge_atTop threshold)
  filter_upwards [hlarge] with n hn
  have hrootae : ∀ᵐ root ∂cavityRootMeasure volume
      (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1), tag (m n) root ∈ A :=
    Measure.ae_smul_measure
      ((ae_restrict_mem (measurableSet_Icc.inter
        (hA.preimage (continuous_physicalSceneMacroscopicRoot (s (m n))).measurable))).mono
          (fun root hr ↦ hr.2)) _
  apply lintegral_mono
  intro ξ
  apply lintegral_mono_ae
  filter_upwards [hrootae] with root hr
  have hcompare := hpoint (s (m n)) hn (Γ (m n) ξ) S hS B U hU.measurableSet
    (rootValue (center+tag (m n) root)) root
  have hscaled := mul_le_mul_of_nonneg_left hcompare
    (bot_le : 0 ≤ ENNReal.ofReal ((m n : ℝ)+1))
  simpa only [Ftrunc,Eread,hmacro _ (hAsub hr),mul_add,mul_left_comm] using hscaled


attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish

variable [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
  (i : Fin D.haar.continuous.count)
set_option quotPrecheck false
local notation "q" => finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker
local notation "V" => D.coreSpatialCoordinateSpace i
local notation "X" => V × ℝ
local notation "PairScene" => CavityLocalScene X X
local notation "Macro" => OriginalIIDMaskedMacroCarrier (0 : X)

/-- An actual frame weak law and its own full-scene first marginal give the
fixed whole-core raw matrix cutoff bound on a measured auxiliary-cell/owner
intersection. No conditional Palm or lower-energy bound is assumed. -/
theorem PopulationLocalPressureCore.fixed_candidate_owner_cell_restricted_tilt_liminf
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (hq : 0 < q) (H : Set M) (hH : MeasurableSet H)
    (S : Set (M × M)) (hS : MeasurableSet S)
    (ψ : C(ℝ × ℝ,ℝ)) (hψrange : ∀ clocks, ψ clocks ∈ Icc 0 1)
    (hψsupport : tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ)
    (K : Set V) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macro × Macro)) (j : ℕ)
    (hroot : (originalIIDFixedCandidateFullSceneJoint (Q j)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    let center := originalMacroFrameCenter q j
    let s := physicalSceneCanonicalHaarScale q
    let tag := fun n ↦ physicalSceneMacroscopicRoot (s n)
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (s n)
    let shifted := fun n x ↦ coord n x-s n • center
    let Qplan := (Q j).map (continuous_originalIIDMaskedMacroPlanProjection (0 : X)).measurable.aemeasurable
    Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : X) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH (shifted (m n))
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (s (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable))
      atTop (𝓝 Qplan) →
    ∀ (A : Set V), MeasurableSet A → A ⊆ originalMacroFrameOwner q K j →
      A ⊆ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots →
    ∀ B : ℝ, ∀ (U : Set V), IsOpen U → palmUnitCube (Fin q) ⊆ U →
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := fun n ξ ↦ (originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)
    let Γcell := fun n ξ ↦ (Γ n ξ).restrict S
    let Γclock := fun n ξ ↦ (Γ n ξ).restrict {p | (u p.1,u p.2) ∈
      (D.haar.continuous.coefficient i).window.region}
    let rootValue := physicalSceneOriginalMacroRootValue (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex
    (∫⁻ c in A, ∫⁻ mark, ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B)
      (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex g t (c,mark)))
      ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDWholeCoreSceneKernel K hK Q c).map Prod.fst)) ∂volume) ≤
      liminf (fun n ↦ ∫⁻ ξ, ∫⁻ root,
        ENNReal.ofReal ((m n : ℝ)+1) * cavityRootWindowReadout (Γcell (m n) ξ)
          (fun p ↦ coord (m n) p.1)
          (fun p ↦ ENNReal.ofReal ((s (m n))^2 *
            ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)) U
          (root+s (m n) • center) +
        ENNReal.ofReal B * (ENNReal.ofReal ((m n : ℝ)+1) *
          (D.originalTaylorGuardMass i R (s (m n)) U
            (rootValue (center+tag (m n) root)) (root+s (m n) • center) (Γclock (m n) ξ) +
            Γ (m n) ξ ({p | coord (m n) p.1-(root+s (m n) • center) ∈ U} ∩ Sᶜ)))
        ∂cavityRootMeasure volume
          (physicalSceneCanonicalHaarDomain q (m n) ∩ tag (m n) ⁻¹'
            ((fun w ↦ center+w) ⁻¹' A)) ((m n : ℝ)+1)
        ∂law (m n)) atTop := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro center s tag coord shifted Qplan hweak A hA howner hcore B U hU hsub law Γ Γcell Γclock rootValue
  obtain ⟨energy,he0,heq,hlim⟩ :=
    D.exists_translated_fixed_candidate_cell_restricted_tilt_liminf
      hF hcomplete hu ha hinj horder g t i hq H hH S hS ψ hψrange hψsupport center R hR hε cost hcost k
  let Alocal := (fun w : V ↦ center+w) ⁻¹' A
  have hAlocal : MeasurableSet Alocal := hA.preimage (measurable_const.add measurable_id)
  have hAlocalCore : Alocal ⊆ (fun w ↦ center+w) ⁻¹'
      (D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots) := fun w hw ↦ hcore hw
  have hpalm := hlim (0 : X) m hm Qplan hweak Alocal hAlocal hAlocalCore B U hU hsub
  have hfirst : (originalIIDFixedCandidatePairPlanJoint (Q j)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V) :=
    (ae_originalIIDFixedCandidate_condKernel_pair_readout (Q j)).1.trans hroot
  let Fraw := fun (c : V) (mark : PhysicalPairPalmMark (Fin q)) ↦
    ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B) (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex g t (c,mark)))
  have hreadout := lintegral_originalIIDFixedCandidate_cubePalm_eq_local_owner_subset
    K hK Q j hroot A hA howner Fraw
  change (∫⁻ c in A, ∫⁻ mark, Fraw c mark ∂cubePalm (Fin q) (physicalScenePairCampbell
    ((originalIIDWholeCoreSceneKernel K hK Q c).map Prod.fst)) ∂volume) ≤ _
  rw [hreadout]
  have hequality : (∫⁻ w, ∫⁻ mark, Fraw (center+w) mark
      ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel w))
      ∂(physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
        (physicalScene_centered_unitCube_mass (Fin q)) : Measure V).restrict Alocal) =
      ∫⁻ w, ∫⁻ mark, ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B)
        (ENNReal.ofReal (energy (center+w,mark)))
        ∂cubePalm (Fin q) (physicalScenePairCampbell
          ((originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel w))
        ∂(physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
          (physicalScene_centered_unitCube_mass (Fin q)) : Measure V).restrict Alocal := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem hAlocal] with w hw
    apply lintegral_congr
    intro mark
    exact (D.clock_cutoff_macro_shifted_tilt_energy_eq_fixed_raw hF hcomplete hu ha hinj g t i ψ
      hψsupport energy heq B (hAlocalCore hw) mark).symm
  rw [hequality]
  change (∫⁻ w, ∫⁻ mark, ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B)
      (ENNReal.ofReal (energy (center+w,mark)))
      ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel w))
      ∂(originalIIDFixedCandidatePairPlanJoint (Q j)).fst.restrict Alocal) ≤ _ at hpalm
  rw [hfirst] at hpalm
  exact hpalm


section FixedSeed
variable (j : ℕ)
set_option quotPrecheck false
local notation "qj" => finrank ℝ (P j).seed.covector.ker
local notation "Vj" => OriginalIIDSeedCoordinateSpace P j
local notation "Xj" => Vj × ℝ
local notation "Macroj" => OriginalIIDMaskedMacroCarrier (0 : Xj)
attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish


/-- Actual auxiliary geometry produces the clock/Taylor guard while keeping
the old source-cell restriction and its literal bounded escape in the lower readout. -/
theorem PopulationLocalPressureCore.exists_originalIID_cell_restricted_auxiliary_tilt_readout
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (i : Fin D.haar.continuous.count)
    (hseed : (D.haar.continuous.coefficient i).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (S : Set M) (hS : MeasurableSet S)
    (hSH : S ⊆ physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j)
    (ψ : C(ℝ × ℝ,ℝ)) (hψrange : ∀ clocks, ψ clocks ∈ Icc 0 1)
    (hψsupport : tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region)
    (K : Set Vj) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj)) (frame : ℕ)
    (hroot : (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) {ε : ℝ} (hε : 0 < ε)
    (η : ℝ≥0∞) (hη : 0 < η) :
    let center := originalMacroFrameCenter qj frame
    let scale := physicalSceneCanonicalHaarScale qj
    let tag := fun n ↦ physicalSceneMacroscopicRoot (scale n)
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let shifted := fun n x ↦ coord n x-scale n • center
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let auxCore := originalIIDSeedCoordinateCast (P := P) hseed ''
      (D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots)
    Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH (shifted (m n))
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable)) →
    ∃ guard : (n : ℕ) → ((Fin (n+1) → M) × (Fin (n+1) → M)) → Vj → ℝ≥0∞,
      (∀ᶠ n in atTop, ∀ A : Set Vj, MeasurableSet A → A ⊆ auxCore →
        (∫⁻ ξ, ∫⁻ root, guard n ξ root
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain qj n ∩ tag n ⁻¹'
            ((fun w ↦ center+w) ⁻¹' A)) ((n : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ η) ∧
      ∀ A : Set Vj, MeasurableSet A → A ⊆ originalMacroFrameOwner qj K frame → A ⊆ auxCore →
      ∀ B : ℝ,
      (∫⁻ c in A, ∫⁻ mark, ENNReal.ofReal (ψ mark.1)*min (ENNReal.ofReal B)
        (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) j g t (c,mark)))
        ∂cubePalm (Fin qj) (physicalScenePairCampbell
          ((originalIIDWholeCoreSceneKernel K hK Q c).map Prod.fst)) ∂volume) ≤
        liminf (fun r ↦ ∫⁻ ξ, ∫⁻ root,
          ENNReal.ofReal ((m r : ℝ)+1)*cavityRootWindowReadout
            ((originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ).restrict (S ×ˢ univ))
            (fun p ↦ coord (m r) p.1)
            (fun p ↦ ENNReal.ofReal ((scale (m r))^2 *
              ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖+ε)) U (root+scale (m r) • center) +
          ENNReal.ofReal B*(guard (m r) ξ root + ENNReal.ofReal ((m r : ℝ)+1)*
            ((originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ).restrict (H ×ˢ univ))
              ({p | coord (m r) p.1-(root+scale (m r) • center) ∈ U} ∩ (S ×ˢ univ)ᶜ))
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain qj (m r) ∩ tag (m r) ⁻¹'
            ((fun w ↦ center+w) ⁻¹' A)) ((m r : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro center scale tag coord shifted H hH auxCore hweak
  obtain ⟨R,hR,hRW,hsmall⟩ := D.exists_eventually_originalIID_translated_clock_guard_small
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist i cost hcost k hq center budget hbudget henergy
    hU.measurableSet W hW η hη
  let guard := fun (n : ℕ) (ξ : (Fin (n+1) → M) × (Fin (n+1) → M))
      (root : D.coreSpatialCoordinateSpace i) ↦ ENNReal.ofReal ((n : ℝ)+1)*
    D.originalTaylorGuardMass i R (scale n) U
      (physicalSceneOriginalMacroRootValue (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (center+tag n root)) (root+scale n • center)
      (((originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)).restrict
        {p | (u p.1,u p.2) ∈ (D.haar.continuous.coefficient i).window.region})
  refine ⟨guard,?_,?_⟩
  · filter_upwards [hsmall] with n hn
    intro A hAm hAsub
    have hnative : A ⊆ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots := by
      simpa only [auxCore,originalIIDSeedCoordinateCast_rfl,image_id'] using hAsub
    exact hn ((fun w ↦ center+w) ⁻¹' A)
      (hAm.preimage (measurable_const.add measurable_id)) (preimage_mono hnative)
  · intro A hAm howner hAsub B
    have hnative : A ⊆ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots := by
      simpa only [auxCore,originalIIDSeedCoordinateCast_rfl,image_id'] using hAsub
    have hbound := D.fixed_candidate_owner_cell_restricted_tilt_liminf i hF hcomplete hu ha hinj horder
      g t hq H hH (S ×ˢ univ) (hS.prod MeasurableSet.univ) ψ hψrange hψsupport R hR hε
      cost hcost k K hK Q frame hroot m hm hweak A hAm howner hnative B U hU hcube
    have hrestrict (n : ℕ) (ξ : (Fin (n+1) → M) × (Fin (n+1) → M)) :
        ((originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)).restrict
          (S ×ˢ univ) = (originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (S ×ˢ univ) :=
      Measure.restrict_restrict_of_subset (Set.prod_mono hSH Subset.rfl)
    dsimp only at hbound
    simp_rw [hrestrict] at hbound
    simpa only [mul_add] using hbound
/-- Finite auxiliary/frame cells share the exact old source-cell physical
tilt liminf. The original core-escape loss tends to zero at fixed height. -/
theorem PopulationLocalPressureCore.originalIID_finite_weighted_cell_tilt_liminf
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)

    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.continuous.count)
    (hseed₀ : (D₀.continuous.coefficient i₀).seedIndex = j)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    {I : Type*} [Fintype I]
    (index : I → Fin D.haar.continuous.count)
    (hseed : ∀ i, (D.haar.continuous.coefficient (index i)).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (ψ : I → C(ℝ × ℝ,ℝ)) (hψrange : ∀ i clocks, ψ i clocks ∈ Icc 0 1)
    (hψsupport : ∀ i, tsupport (ψ i) ⊆
      (D.haar.continuous.coefficient (index i)).window.region)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.continuous.coefficient i₀).seedIndex '' (D₀.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞))
    (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W)
    (cells : I → Set Vj) (hcells : ∀ i, MeasurableSet (cells i))
    (hsubK : ∀ i, cells i ⊆ K)
    (hsubaux : ∀ i, cells i ⊆ originalIIDSeedCoordinateCast (P := P) (hseed i) ''
      (D.coreMacroLabel (index i) '' (D.haar.continuous.coefficient (index i)).roots))
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (cells i) (cells k))) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →
    ∀ B : ℝ,
      (∑ i, ∫⁻ c in cells i, ∫⁻ mark, ENNReal.ofReal (ψ i mark.1)*min (ENNReal.ofReal B)
        (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) j g t (c,mark)))
        ∂originalIIDRawPairPalmKernel (originalIIDWholeCoreSceneKernel K hK.measurableSet Q) c ∂volume) ≤
      volume U*liminf (fun r ↦ ∫⁻ ξ, ∫⁻ p,
        ENNReal.ofReal ((scale (m r))^2*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
        ∂(originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ).restrict
          ((a ⁻¹' (D₀.continuous.coefficient i₀).roots) ×ˢ univ)
        ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro scale coord H hH hweak B
  let C₀ := D₀.continuous.coefficient i₀
  let q₀ := finrank ℝ (P C₀.seedIndex).seed.covector.ker
  let S := a ⁻¹' C₀.roots
  have hS : MeasurableSet S := C₀.roots_compact.measurableSet.preimage ha
  have hSH : S ⊆ H := fun x hx ↦ C₀.roots_subset_piece hx
  let maskedEnergy := fun n ↦ ∫⁻ ξ, ∫⁻ p,
    ENNReal.ofReal ((scale n)^2*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
    ∂(originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (S ×ˢ univ)
    ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))
  let actualL := liminf (fun r ↦ maskedEnergy (m r)) atTop
  simp only [originalIIDSeedCoordinateCast_rfl,image_id'] at hK₀
  have hKbasis : K = (Module.finBasis ℝ (P C₀.seedIndex).seed.covector.ker).equivFunL ''
      (populationSeedRootLabelValue (P C₀.seedIndex).seed a '' C₀.roots) := by
    rw [hK₀,image_image]
    rfl
  let raw := originalIIDRawPairPalmKernel (originalIIDWholeCoreSceneKernel K hK.measurableSet Q)
  let readout := fun i c ↦ ∫⁻ mark, ENNReal.ofReal (ψ i mark.1)*min (ENNReal.ofReal B)
    (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) C₀.seedIndex g t (c,mark))) ∂raw c
  obtain ⟨J,hJ,hpairmeas,hpairdisjoint,hpairsub,hpartition⟩ :=
    exists_finite_original_owner_cell_partition K hK cells hcells hsubK hdisjoint
  let paircell := fun p : I × Fin J ↦ cells p.1 ∩ originalMacroFrameOwner q₀ K p.2.val
  let center := fun p : I × Fin J ↦ originalMacroFrameCenter q₀ p.2.val
  have hperturb (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
      (∑ i, ∫⁻ c in cells i, readout i c ∂volume) ≤
        volume U*(actualL+ENNReal.ofReal ε*μ S)+
          ENNReal.ofReal B*∑ _p : I × Fin J, (η+η) := by
    have hex (p : I × Fin J) :=
      D.exists_originalIID_cell_restricted_auxiliary_tilt_readout (j := C₀.seedIndex)
        hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
        hA hB hμ hν hreg hμreg hface hgap hdist (index p.1) (hseed p.1)
        cost hcost k hq budget hbudget henergy g t S hS hSH (ψ p.1) (hψrange p.1) (hψsupport p.1)
        K hK.measurableSet Q p.2.val (hroot p.2.val) m hm U hU hcube W hW hε η hη
        (hweak p.2.val)
    choose baseGuard hguards hlocal using hex
    let escape := fun (p : I × Fin J) (n : ℕ) ξ root ↦ ENNReal.ofReal ((n : ℝ)+1)*
      ((originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ))
        ({e | coord n e.1-(root+scale n • center p) ∈ U} ∩ (S ×ˢ univ)ᶜ)
    let guard := fun p n ξ root ↦ baseGuard p n ξ root+escape p n ξ root
    have hescape (p : I × Fin J) := D₀.original_iid_translated_source_core_escape_tendsto
      hF hcomplete hu ha hinj i₀ U hU.measurableSet W hW scale
      (physicalSceneCanonicalHaarScale_pos q₀) (tendsto_physicalSceneCanonicalHaarScale q₀ hq)
      (fun n ↦ by simpa only [Nat.cast_add,Nat.cast_one] using physicalSceneCanonicalHaarScale_pow q₀ hq n)
      cost hcost k (fun _ ↦ center p) (fun n ↦ physicalSceneCanonicalHaarDomain q₀ n)
      (paircell p) (by rw [← hKbasis]; exact hpairsub p)
    have hescapeSmall : ∀ᶠ n in atTop, ∀ p : I × Fin J,
        (∫⁻ ξ, ∫⁻ root, escape p n ξ root
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain q₀ n ∩
            (fun root ↦ center p+physicalSceneMacroscopicRoot (scale n) root) ⁻¹' paircell p)
            ((n : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ η := by
      apply Filter.eventually_all.mpr
      intro p
      have hsets (n : ℕ) (root) : {e : M × M | coord n e.1-(root+scale n • center p) ∈ U} ∩
          (S ×ˢ univ)ᶜ = {e | coord n e.1-(root+scale n • center p) ∈ U ∧ a e.1 ∉ C₀.roots} := by
        ext e
        simp only [S,mem_inter_iff,mem_compl_iff,mem_prod,mem_preimage,mem_univ,and_true,mem_ofPred_eq]
      have hcoord_e (n : ℕ) (x : M) : coord n x = scale n •
          (Module.finBasis ℝ (P C₀.seedIndex).seed.covector.ker).equivFunL
            (populationSeedRootLabelValue (P C₀.seedIndex).seed a (a x)) := by
        ext k
        rfl
      have ht : Tendsto (fun n ↦ ∫⁻ ξ, ∫⁻ root, escape p n ξ root
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain q₀ n ∩
            (fun root ↦ center p+physicalSceneMacroscopicRoot (scale n) root) ⁻¹' paircell p)
            ((n : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (n+1) ↦ ν))) atTop (𝓝 0) := by
        dsimp only [escape]
        simp_rw [hsets]
        simp_rw [hcoord_e]
        simpa only [Nat.cast_add,Nat.cast_one,H,C₀] using hescape p
      exact (ht.eventually (eventually_lt_nhds hη)).mono (fun _ hn ↦ hn.le)
    have hsmall : ∀ᶠ n in atTop, ∀ p : I × Fin J,
        (∫⁻ ξ, ∫⁻ root, guard p n ξ root
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain q₀ n ∩
            (fun root ↦ center p+physicalSceneMacroscopicRoot (scale n) root) ⁻¹' paircell p)
            ((n : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ η+η := by
      have hall := Filter.eventually_all.mpr hguards
      filter_upwards [hall,hescapeSmall] with n hn he
      intro p
      rw [lintegral_originalIID_guard_add_source_escape μ ν (cost n) (hcost n) (k n) H hH
        (coord n) (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (scale n))
        S hS U hU.measurableSet (scale n • center p) ((n : ℝ)+1)
        (physicalSceneCanonicalHaarDomain q₀ n ∩
          (fun root ↦ center p+physicalSceneMacroscopicRoot (scale n) root) ⁻¹' paircell p) (baseGuard p n)]
      exact add_le_add (hn p (paircell p) (hpairmeas p)
        (inter_subset_left.trans (hsubaux p.1))) (he p)
    have hbound := originalIID_finite_cell_readouts_le_masked_liminf μ ν cost hcost k S hS
      coord (fun n ↦ measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj C₀.seedIndex (scale n))
      (fun n p ↦ (scale n)^2*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
      (fun n ↦ (((F.measurable_distance_slack hu).const_mul ((scale n)^2)).add
        (g.continuous.measurable.const_mul t)).add_const (|t| * ‖g‖))
      ε B scale (fun n ↦ (physicalSceneCanonicalHaarScale_pos q₀ n).ne') center
      (fun n _ ↦ physicalSceneCanonicalHaarDomain q₀ n) (fun _ _ ↦ measurableSet_Icc)
      paircell hpairmeas hpairdisjoint U hU.measurableSet hUf guard (fun _ ↦ η+η)
      m hm (fun p ↦ ∫⁻ c in paircell p, readout p.1 c ∂volume) hsmall
      (fun p ↦ by
        simpa only [readout,raw,originalIIDRawPairPalmKernel_apply,center,scale,coord,H,guard,escape,Set.preimage_preimage,Function.comp_def] using
          hlocal p (paircell p) (hpairmeas p) inter_subset_right
            (inter_subset_left.trans (hsubaux p.1)) B)
    rw [← hpartition readout] at hbound
    exact hbound
  let e := fun n : ℕ ↦ (1 / ((n : ℝ)+1))
  have hepos (n : ℕ) : 0 < e n := by positivity
  have he : Tendsto e atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hee : Tendsto (fun n ↦ ENNReal.ofReal (e n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp he
  have hsum : Tendsto (fun n ↦ ∑ _p : I × Fin J, (ENNReal.ofReal (e n)+ENNReal.ofReal (e n))) atTop (𝓝 0) := by
    simpa only [zero_add,Finset.sum_const_zero] using
      tendsto_finsetSum (s := (Finset.univ : Finset (I × Fin J))) (fun _ _ ↦ hee.add hee)
  have hright : Tendsto (fun n ↦ volume U*(actualL+ENNReal.ofReal (e n)*μ S)+
      ENNReal.ofReal B*∑ _p : I × Fin J, (ENNReal.ofReal (e n)+ENNReal.ofReal (e n))) atTop (𝓝 (volume U*actualL)) := by
    have hm := ENNReal.Tendsto.mul_const hee (b := μ S) (Or.inr (measure_ne_top μ S))
    have ha := (tendsto_const_nhds (x := actualL)).add hm
    have hfirst := ENNReal.Tendsto.const_mul ha (a := volume U) (Or.inr hUf)
    have hlast := ENNReal.Tendsto.const_mul hsum (a := ENNReal.ofReal B)
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [zero_mul,add_zero,mul_zero] using hfirst.add hlast
  exact ge_of_tendsto hright (Eventually.of_forall (fun n ↦
    hperturb (e n) (hepos n) (ENNReal.ofReal (e n)) (ENNReal.ofReal_pos.mpr (hepos n))))
/-- Actual finite auxiliary cells remove their genuine clock cutoff loss
against the old root mass, keeping its literal source-cell physical liminf. -/
theorem PopulationLocalPressureCore.originalIID_auxiliary_clipped_tilt_sum_le_masked_liminf
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)


    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.continuous.count)
    (hseed₀ : (D₀.continuous.coefficient i₀).seedIndex = j)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (ψ : Fin D.haar.continuous.count → C(ℝ × ℝ,ℝ))
    (hψrange : ∀ i clocks, ψ i clocks ∈ Icc 0 1)
    (hψsupport : ∀ i, tsupport (ψ i) ⊆ (D.haar.continuous.coefficient i).window.region)
    (clockLoss : ℝ≥0∞)
    (hclock : ∀ i, ∀ᵐ z ∂(μ.map a).restrict (D.haar.continuous.coefficient i).roots,
      ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) →
        (∀ᵐ p ∂π, p.1 ≤ p.2) → (∫⁻ p, ENNReal.ofReal (1-ψ i p) ∂π) ≤ clockLoss)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.continuous.coefficient i₀).seedIndex '' (D₀.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞)) (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let actualL := liminf (fun r ↦ ∫⁻ ξ, ∫⁻ p,
      ENNReal.ofReal ((scale (m r))^2*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
      ∂(originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ).restrict
        ((a ⁻¹' (D₀.continuous.coefficient i₀).roots) ×ˢ univ)
      ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop
    let Λ := originalIIDWholeCoreSceneKernel K hK.measurableSet Q
    let ref := fun c : Vj ↦ a ((P j).seed.curve
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) j
    ∀ (input : Vj → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint qj) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint qj))),
    (∀ᵐ c ∂(volume : Measure Vj).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →
    ∀ B : ℝ,
      (∑ i : Fin D.haar.continuous.count,
        ∫⁻ c in originalIIDSeedCoordinateCast (P := P) hseed₀ ''
          originalIIDAuxiliaryCell (D₀.continuous.coefficient i₀) (D.haar.continuous.coefficient i),
          ∫⁻ mark, min (ENNReal.ofReal B) (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) j g t (c,mark)))
            ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤
        volume U*actualL + ENNReal.ofReal B*clockLoss*(μ.map a) (D₀.continuous.coefficient i₀).roots := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro scale coord H hH actualL Λ ref root input hprofile hweak B
  let C₀ := D₀.continuous.coefficient i₀
  let S₀ := (P C₀.seedIndex).seed
  let e₀ := (Module.finBasis ℝ S₀.covector.ker).equivFunL
  let R₀ := populationSeedRootLabelValue S₀ a
  let I := OriginalIIDSameSeedAuxiliaryIndex C₀ D.haar
  let cells := fun i : I ↦ originalIIDAuxiliaryCell C₀ (D.haar.continuous.coefficient i.val)
  let energy := fun p : (OriginalIIDSeedCoordinateSpace P C₀.seedIndex) × PhysicalPairPalmMark (Fin (finrank ℝ S₀.covector.ker)) ↦
    ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) C₀.seedIndex g t p)
  simp only [originalIIDSeedCoordinateCast_rfl,image_id'] at hK₀ ⊢
  have hKbasis : K = e₀ '' (R₀ '' C₀.roots) := by
    rw [hK₀,image_image]
    rfl
  have hcells (i : I) : MeasurableSet (cells i) := by
    dsimp only [cells]
    rw [originalIIDAuxiliaryCell_eq_basis_image]
    exact e₀.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (D₀.measurable_cell_label_image hcomplete i₀
        (C₀.roots_compact.measurableSet.inter
          (D.haar.continuous.coefficient i.val).roots_compact.measurableSet) inter_subset_left)
  have hsubK (i : I) : cells i ⊆ K := by
    rw [hK₀]
    exact image_mono inter_subset_left
  have hsubaux (i : I) : cells i ⊆ originalIIDSeedCoordinateCast (P := P) i.property ''
      (D.coreMacroLabel i.val '' (D.haar.continuous.coefficient i.val).roots) :=
    originalIIDAuxiliaryCell_subset_cast_aux_core C₀ _ i.property
  have hdisjoint : Pairwise (fun i k : I ↦ Disjoint (cells i) (cells k)) := by
    intro i k hik
    dsimp only [cells]
    rw [originalIIDAuxiliaryCell_eq_basis_image,originalIIDAuxiliaryCell_eq_basis_image]
    simp only [image_image]
    exact ((D.haar.continuous.disjoint (fun h ↦ hik (Subtype.ext h))).mono
      inter_subset_right inter_subset_right).image (D₀.original_coordinate_injOn i₀)
        inter_subset_left inter_subset_left
  have hweighted := D.originalIID_finite_weighted_cell_tilt_liminf
    (j := C₀.seedIndex) hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist D₀ i₀ rfl g t (fun i : I ↦ i.val) (fun i ↦ i.property)
    cost hcost k hq budget hbudget henergy (fun i : I ↦ ψ i.val)
    (fun i ↦ hψrange i.val) (fun i ↦ hψsupport i.val)
    K hK (by simpa only [originalIIDSeedCoordinateCast_rfl,image_id'] using hK₀)
    Q hroot m hm U hU hcube hUf W hW cells hcells hsubK hsubaux hdisjoint hweak B
  have henergyMeas : Measurable energy :=
    (measurable_physicalSceneOriginalMacroShiftedTiltEnergy hF hcomplete hu ha hinj C₀.seedIndex g t).ennreal_ofReal
  have hprofile₀ : ∀ᵐ c ∂(volume : Measure (OriginalIIDSeedCoordinateSpace P C₀.seedIndex)).restrict
      (e₀ '' (R₀ '' C₀.roots)), OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) C₀.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c) := by
    rwa [← hKbasis]
  have hmiss (i : I) : ∀ᵐ c ∂(fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)).restrict (cells i),
      (∫⁻ mark, ENNReal.ofReal (1-ψ i.val mark.1) ∂originalIIDRawPairPalmKernel Λ c) ≤
        originalIIDRawPairPalmKernel Λ c univ*clockLoss := by
    have h := D₀.ae_fixed_candidate_raw_clock_cutoff_missed_le hF hcomplete hu ha hinj i₀
      Λ gap hgap input hprofile₀ (ψ i.val) (hψrange i.val) clockLoss
      (C₀.roots_compact.measurableSet.inter (D.haar.continuous.coefficient i.val).roots_compact.measurableSet)
      inter_subset_left (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hclock i.val))
    simpa only [cells,originalIIDAuxiliaryCell_eq_basis_image] using h
  have hmass : fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ) (⋃ i : I, cells i) ≤
      (μ.map a) C₀.roots := by
    have hfull := D₀.fixed_candidate_raw_palm_mass_eq_label hF hcomplete hu ha hinj i₀
      Λ gap (fun c ↦ condDistrib u a μ (root c)) (fun c ↦ condDistrib u a ν (root c))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) input hprofile₀
      C₀.roots_compact.measurableSet Subset.rfl
    calc
      _ ≤ fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ) K :=
        measure_mono (iUnion_subset hsubK)
      _ = _ := by rw [hKbasis]; exact hfull
  rw [sum_originalIIDAuxiliaryCell_eq_same_seed C₀ D.haar
    (fun A ↦ ∫⁻ c in A, ∫⁻ mark, min (ENNReal.ofReal B) (energy (c,mark))
      ∂originalIIDRawPairPalmKernel Λ c ∂volume) (by simp)]
  exact (sum_clipped_kernel_le_clock_cutoffs_add_union_root_mass volume
    (originalIIDRawPairPalmKernel Λ) Prod.fst measurable_fst (fun i : I ↦ ψ i.val)
    (fun i ↦ hψrange i.val) energy henergyMeas (ENNReal.ofReal B) ENNReal.ofReal_ne_top
    clockLoss cells hcells hdisjoint hmiss).trans
      (add_le_add hweighted (mul_le_mul_of_nonneg_left hmass bot_le))

/-- At each fixed height, original precision refinement removes clock and
auxiliary uncovered-root losses without changing Q, m, the full PN or raw tilt. -/
theorem originalIID_fixed_candidate_clipped_tilt_le_masked_liminf
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)


    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.continuous.count)
    (hseed₀ : (D₀.continuous.coefficient i₀).seedIndex = j)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (hGood : ∀ᵐ z ∂μ.map a, Good z)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.continuous.coefficient i₀).seedIndex '' (D₀.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞)) (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let actualL := liminf (fun r ↦ ∫⁻ ξ, ∫⁻ p,
      ENNReal.ofReal ((scale (m r))^2*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
      ∂(originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ).restrict
        ((a ⁻¹' (D₀.continuous.coefficient i₀).roots) ×ˢ univ)
      ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop
    let Λ := originalIIDWholeCoreSceneKernel K hK.measurableSet Q
    let ref := fun c : Vj ↦ a ((P j).seed.curve
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) j
    ∀ (input : Vj → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint qj) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint qj))),
    (∀ᵐ c ∂(volume : Measure Vj).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →

    ∀ B : ℝ,
      (∫⁻ c in K, ∫⁻ mark, min (ENNReal.ofReal B) (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) j g t (c,mark)))
        ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤ volume U*actualL := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro scale coord H hH actualL Λ ref root input hprofile hweak Bclip
  let C₀ := D₀.continuous.coefficient i₀
  let S₀ := (P C₀.seedIndex).seed
  let e₀ := (Module.finBasis ℝ S₀.covector.ker).equivFunL
  let R₀ := populationSeedRootLabelValue S₀ a
  let errorScale := fun n : ℕ ↦ (1/((n : ℝ)+1))
  have hpos (n : ℕ) : 0 < errorScale n := by positivity
  have ht : Tendsto errorScale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he : Tendsto (fun n ↦ ENNReal.ofReal (errorScale n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (not_le_of_gt hgap) (by simpa only [dist_self] using hdist x hxA x hxB)
  have hex (n : ℕ) := exists_original_population_core_uniform_clock_cutoffs
    (Good := Good) (δ := ENNReal.ofReal (errorScale n)) (loss := ENNReal.ofReal (errorScale n))
    hpopulation hrecovery hF hcomplete hu ha hinj hκ hbalance hGood
    hA hB hAB (hF.measurableSet_potentialRegularDomain hcomplete u) hμ hν hμreg hreg horder
    (ne_of_gt (ENNReal.ofReal_pos.mpr (hpos n))) (ne_of_gt (ENNReal.ofReal_pos.mpr (hpos n)))
  choose Daux hcutoffs using hex
  have hcuts (n : ℕ) (i : Fin (Daux n).haar.continuous.count) := hcutoffs n i (errorScale n) (hpos n)
  choose ψ hψcompact hψsupport hψrange hclock using hcuts
  let error := fun n ↦ ENNReal.ofReal Bclip*(ENNReal.ofReal (errorScale n)+ENNReal.ofReal (errorScale n))*
    (μ.map a) C₀.roots
  have herror : Tendsto error atTop (𝓝 0) := by
    have hadd := he.add he
    have hmul := ENNReal.Tendsto.const_mul hadd (a := ENNReal.ofReal Bclip) (Or.inr ENNReal.ofReal_ne_top)
    have hlast := ENNReal.Tendsto.mul_const hmul (b := (μ.map a) C₀.roots)
      (Or.inr (measure_ne_top (μ.map a) C₀.roots))
    simpa only [add_zero,mul_zero,zero_mul] using hlast
  have hfamily (n : ℕ) := (Daux n).originalIID_auxiliary_clipped_tilt_sum_le_masked_liminf
    (j := C₀.seedIndex) hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist D₀ i₀ rfl g t cost hcost k hq budget hbudget henergy
    (ψ n) (hψrange n) (hψsupport n) (ENNReal.ofReal (errorScale n)+ENNReal.ofReal (errorScale n))
    (hclock n) K hK hK₀ Q hroot m hm U hU hcube hUf W hW input hprofile hweak Bclip
  simp only [originalIIDSeedCoordinateCast_rfl,image_id'] at hK₀
  have hKbasis : K = e₀ '' (R₀ '' C₀.roots) := by
    rw [hK₀,image_image]
    rfl
  have hprofile₀ : ∀ᵐ c ∂(volume : Measure (OriginalIIDSeedCoordinateSpace P C₀.seedIndex)).restrict
      (e₀ '' (R₀ '' C₀.roots)), OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) C₀.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c) := by
    rwa [← hKbasis]
  have hwhole := D₀.fixed_candidate_clipped_le_of_auxiliary_cores hF hcomplete hu ha hinj i₀
    (fun _ ↦ Good) (fun _ ↦ r) (fun n ↦ ENNReal.ofReal (errorScale n))
    (fun n ↦ ENNReal.ofReal (errorScale n)) (fun n ↦ (Daux n).haar) he
    Λ gap (fun c ↦ condDistrib u a μ (root c)) (fun c ↦ condDistrib u a ν (root c))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) input hprofile₀
    (fun p ↦ ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) C₀.seedIndex g t p))
    (ENNReal.ofReal Bclip) ENNReal.ofReal_ne_top (volume U*actualL) error herror
    (fun n ↦ by
      simpa only [originalIIDSeedCoordinateCast_rfl,image_id',originalIIDAuxiliaryCell_eq_basis_image,error]
        using hfamily n)
  rwa [← hKbasis] at hwhole

/-- Actual original fixed-candidate full shifted energy has its sharp
unit-volume source-cell lower passage. Fixed-height precision limits precede
MCT and true open-window volume exhaustion; no boundary-null input is used. -/
theorem originalIID_fixed_candidate_shifted_tilt_le_masked_liminf
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)


    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.continuous.count)
    (hseed₀ : (D₀.continuous.coefficient i₀).seedIndex = j)
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (hGood : ∀ᵐ z ∂μ.map a, Good z)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.continuous.coefficient i₀).seedIndex '' (D₀.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let actualL := liminf (fun r ↦ ∫⁻ ξ, ∫⁻ p,
      ENNReal.ofReal ((scale (m r))^2*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
      ∂(originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ).restrict
        ((a ⁻¹' (D₀.continuous.coefficient i₀).roots) ×ˢ univ)
      ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop
    let Λ := originalIIDWholeCoreSceneKernel K hK.measurableSet Q
    let ref := fun c : Vj ↦ a ((P j).seed.curve
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) j
    ∀ (input : Vj → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint qj) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint qj))),
    (∀ᵐ c ∂(volume : Measure Vj).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →


    (∫⁻ c in K, ∫⁻ mark,
      ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) j g t (c,mark))
        ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤ actualL := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  intro scale coord H hH actualL Λ ref root input hprofile hweak
  let energy := fun p : Vj × PhysicalPairPalmMark (Fin qj) ↦
    ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) j g t p)
  have henergyMeas : Measurable energy :=
    (measurable_physicalSceneOriginalMacroShiftedTiltEnergy hF hcomplete hu ha hinj j g t).ennreal_ofReal
  apply le_of_open_palm_window_physical_bounds qj _ actualL
  intro U hU hUmeas hcube hUf W hWpos hW
  have hclip := originalIID_fixed_candidate_clipped_tilt_le_masked_liminf (j := j)
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist D₀ i₀ hseed₀ g t cost hcost k hq budget hbudget henergy
    hGood K hK hK₀ Q hroot m hm U hU hcube hUf W hW input hprofile hweak
  have hwhole := lintegral_le_of_uniform_natural_clipped_bounds
    ((volume.restrict K) ⊗ₘ originalIIDRawPairPalmKernel Λ) energy henergyMeas.aemeasurable
    (volume U*actualL) (fun n ↦ by
      rw [Measure.lintegral_compProd (measurable_const.min henergyMeas)]
      simpa only [ENNReal.ofReal_natCast] using hclip (n : ℝ))
  rw [Measure.lintegral_compProd henergyMeas] at hwhole
  exact hwhole


end FixedSeed

end OTSelector.Reconstruction
