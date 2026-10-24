import OTSelector.Reconstruction.OriginalIIDFinalPressureBudgetActualWeakMatching
import OTSelector.Reconstruction.OriginalIIDActualCandidateLabelReadout

/-! One genuine sample subsequence for every core in a countable family and all its original frames. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal BigOperators Topology CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 40000
set_option linter.unusedSectionVars false
open Metric Module Manifold OTSelector.Geometry
open OTSelector.Geometry.ContinuousFinslerNorm.IsSmoothStronglyConvex
open scoped ContDiff NNReal
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ}

variable
    (hcore : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y - u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ x ∂ν, x ∈ F.potentialRegularDomain u)
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

local instance iidFinalPressureCommonCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidFinalPressureCommonCoreConfigTopology (q : ℕ) :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance iidFinalPressureCommonCoreConfigBorel (q : ℕ) :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance iidFinalPressureCommonCoreConfigPolish (q : ℕ) :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance iidFinalPressureCommonCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidFinalPressureCommonCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidFinalPressureCommonCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance iidFinalPressureCommonCorePlanNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

local instance iidFinalPressureCommonCoreMacroPairPolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidFinalPressureCommonCoreSceneBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidFinalPressureCommonCoreMacroBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidFinalPressureCommonCoreMacroPairBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance

local instance iidFinalPressureCommonCoreScenePolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidFinalPressureCommonCoreSceneStandardBorel (q : ℕ) :
    StandardBorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidFinalPressureCommonCoreTaggedSceneBorel (q : ℕ) :
    BorelSpace ((Fin q → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist


/-- Countably many actual original coefficient cores retain one common iid
sample subsequence, their genuine weak laws, both original full inputs, the
original conditional Poisson law and its complete stationary matching profile.
The caller supplies the actual optimizer's energy, not a candidate or weak law. -/
theorem exists_original_actual_common_core_matching_laws_of_energy
    {J : Type*} [Countable J] {δ loss : J → ℝ≥0∞}
    (D : ∀ j, PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r (δ j) (loss j))
    (idx : ∀ j, Fin (D j).haar.continuous.count)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (hdim : 2 ≤ finrank ℝ E) :
    let C := fun j ↦ (D j).haar.continuous.coefficient (idx j)
    let seed := fun j ↦ (P (C j).seedIndex).seed
    let q := fun j ↦ finrank ℝ (seed j).covector.ker
    let V := fun j ↦ Fin (q j) → ℝ
    let X := fun j ↦ V j × ℝ
    let T := fun j ↦ LocalFiniteMeasure (X j) × LocalFiniteMeasure (X j)
    let Macro := fun j ↦ OriginalIIDMaskedMacroCarrier (0 : X j)
    let e := fun j ↦ (Module.finBasis ℝ (seed j).covector.ker).equivFunL
    let rootLabel := fun j ↦ populationSeedRootLabelValue (seed j) a
    let φ := fun j x ↦ e j (rootLabel j (a x))
    let K := fun j ↦ e j '' (rootLabel j '' (C j).roots)
    let hK : ∀ j, MeasurableSet (K j) := by
      let : MetricSpace M := F.metricSpace
      let : ProperSpace M := F.properSpace_of_complete hcomplete
      let : PolishSpace M := inferInstance
      let : BorelSpace (ℚ → M) := inferInstance
      intro j
      exact (e j).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
        ((D j).haar.measurable_cell_label_image hcomplete (idx j)
          (C j).roots_compact.measurableSet Subset.rfl)
    let scale := fun j ↦ physicalSceneCanonicalHaarScale (q j)
    let mask := fun j ↦ physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) (C j).seedIndex
    let hmask := fun j ↦ measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj (C j).seedIndex
    let hφ : ∀ j, Measurable (φ j) := by
      let : MetricSpace M := F.metricSpace
      let : ProperSpace M := F.properSpace_of_complete hcomplete
      let : PolishSpace M := inferInstance
      let : BorelSpace (ℚ → M) := inferInstance
      intro j
      exact (e j).continuous.measurable.comp
        ((measurable_populationSeedRootLabelValue (seed j) hF hcomplete hu ha hinj).comp ha)
    let huM : Measurable u := by let _inst : MetricSpace M := F.metricSpace; exact hu.continuous.measurable
    let ref := fun j (c : V j) ↦ a ((seed j).curve ((e j).symm c) 0)
    let θ := fun j c ↦ originalSeedCoordinateIntensity P a κ (μ.map a) (C j).seedIndex (ref j c)
    let α := fun j c ↦ condDistrib u a μ (ref j c)
    let β := fun j c ↦ condDistrib u a ν (ref j c)
    ∃ m : ℕ → ℕ, StrictMono m ∧
      ∃ Q : ∀ j, ℕ → ProbabilityMeasure (Macro j × Macro j),
        (∀ j frame, Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X j) μ ν
          (by simpa using original_seed_transverse_finrank_pos (seed j) hdim)
          (cost (m n)) (hcost (m n)) (k (m n)) (m n) (mask j) (hmask j)
          (fun x ↦ scale j (m n) • (φ j x-originalMacroFrameCenter (q j) frame))
          (((hφ j).sub measurable_const).const_smul (scale j (m n))) u huM) atTop (𝓝 (Q j frame))) ∧
        (∀ j frame, (originalIIDFixedCandidateFullSceneJoint (Q j frame)).fst =
          (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier (q j))
            (physicalScene_centered_unitCube_mass (Fin (q j))) : Measure (V j))) ∧
        ∃ Γ : ∀ j, Kernel (V j) (T j), (∀ j, IsMarkovKernel (Γ j)) ∧
          ∀ j, ∀ᵐ c ∂(volume : Measure (V j)).restrict (K j),
            OriginalIIDConditionalMatchingProfile gap (θ j c) (α j c) (β j c) (Γ j c)
              (originalIIDWholeCoreSceneKernel (K j) (hK j) (Q j) c) := by
  classical
  let : MetricSpace M := F.metricSpace
  let : ProperSpace M := F.properSpace_of_complete hcomplete
  let : PolishSpace M := inferInstance
  let : BorelSpace (ℚ → M) := inferInstance
  let : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro C seed q V X T Macro e rootLabel φ K hK scale mask hmask hφ huM ref θ α β
  let laws := fun (p : J × ℕ) n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X p.1) μ ν
    (by simpa using original_seed_transverse_finrank_pos (seed p.1) hdim)
    (cost n) (hcost n) (k n) n (mask p.1) (hmask p.1)
    (fun x ↦ scale p.1 n • (φ p.1 x-originalMacroFrameCenter (q p.1) p.2))
    (((hφ p.1).sub measurable_const).const_smul (scale p.1 n)) u huM
  have htight (p : J × ℕ) : IsTightMeasureSet
      (range (fun v : ℕ × ℕ ↦ (laws p v.2 : Measure (Macro p.1 × Macro p.1)))) := by
    have ht := isTightMeasureSet_originalIIDMaskedBipartiteMacroLaw_varying_cost
      (0 : X p.1) μ ν
      (by simpa using original_seed_transverse_finrank_pos (seed p.1) hdim)
      cost hcost k (mask p.1) (hmask p.1)
      (fun n x ↦ scale p.1 n • (φ p.1 x-originalMacroFrameCenter (q p.1) p.2))
      (fun n ↦ ((hφ p.1).sub measurable_const).const_smul (scale p.1 n)) u huM
    convert ht using 1
    ext ρ
    constructor
    · rintro ⟨⟨ℓ,n⟩,rfl⟩; exact ⟨n,rfl⟩
    · rintro ⟨n,rfl⟩; exact ⟨(0,n),rfl⟩
  obtain ⟨Q0,m0,hm0,hweak0,_⟩ := exists_common_iterated_probabilityMeasure_subseq_of_isTight
    (fun p (_ : ℕ) n ↦ laws p n) htight
  let m := m0 0
  let Q := fun j frame ↦ Q0 (j,frame) 0
  have hm : StrictMono m := hm0 0
  have hweak (j) (frame) : Tendsto (fun n ↦ laws (j,frame) (m n)) atTop (𝓝 (Q j frame)) := hweak0 (j,frame) 0
  have hprofiles (j) := (D j).original_actual_all_frames_conditional_matching_of_energy
    (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
    (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
    (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
    (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
    cost hcost k budget hbudget henergy hdim (idx j)
  choose Γ hΓ hΓprofile using hprofiles
  have hframes (j) (frame) := hΓprofile j (originalMacroFrameCenter (q j) frame) m hm (Q j frame) (hweak j frame)
  refine ⟨m,hm,Q,(fun j frame ↦ hweak j frame),(fun j frame ↦ (hframes j frame).1),Γ,hΓ,?_⟩
  intro j
  apply ae_originalIIDWholeCoreSceneKernel_of_ae_owner (K j) (hK j) (Q j)
    (fun c L ↦ OriginalIIDConditionalMatchingProfile gap (θ j c) (α j c) (β j c) (Γ j c) L)
  apply ae_originalMacroFrameOwner_glue (q j) (K j) volume
  intro frame
  apply (ae_originalMacroFrameOwner_iff (q j) (hK j) frame _).mpr
  have hsub : (fun y ↦ originalMacroFrameCenter (q j) frame+y) ⁻¹' originalMacroFrameOwner (q j) (K j) frame ⊆
      (fun y ↦ originalMacroFrameCenter (q j) frame+y) ⁻¹' K j :=
    preimage_mono (fun c hc ↦ (originalMacroFrameOwner_subset (q j) (K j) frame hc).1)
  have hprofile := ae_restrict_of_ae_restrict_of_subset hsub (hframes j frame).2
  have howner : MeasurableSet ((fun y ↦ originalMacroFrameCenter (q j) frame+y) ⁻¹'
      originalMacroFrameOwner (q j) (K j) frame) :=
    (measurableSet_originalMacroFrameOwner (q j) (hK j) frame).preimage (measurable_const.add measurable_id)
  filter_upwards [hprofile,ae_restrict_mem howner] with y hy hmem
  refine ⟨frame,hmem,?_⟩
  simpa only [originalIIDFrameSceneKernel,Kernel.comap_apply,q,add_sub_cancel_left] using hy

end OTSelector.Reconstruction
