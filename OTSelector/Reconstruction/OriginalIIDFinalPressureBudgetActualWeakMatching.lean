import OTSelector.Reconstruction.OriginalIIDWholeCoreSceneKernel

/-! Actual original iid weak matching laws from a physical energy budget, without pressure-data inputs. -/
open Set Function Filter MeasureTheory ProbabilityTheory Topology TopologicalSpace
open scoped ENNReal BigOperators Topology CompactlySupported BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 30000
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
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

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

local instance iidFinalPressureMatchingCorePointStandardBorel (q : ℕ) : StandardBorelSpace ((Fin q → ℝ) × ℝ) := inferInstance
local instance iidFinalPressureMatchingCoreConfigTopology (q : ℕ) :
    TopologicalSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueTopology _
local instance iidFinalPressureMatchingCoreConfigBorel (q : ℕ) :
    BorelSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vagueBorelSpace
local instance iidFinalPressureMatchingCoreConfigPolish (q : ℕ) :
    PolishSpace (LocalConfiguration (0 : (Fin q → ℝ) × ℝ)) := LocalConfiguration.vaguePolishSpace
local instance iidFinalPressureMatchingCoreInputPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := LocalFiniteMeasure.instPolishSpace
local instance iidFinalPressureMatchingCorePlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance iidFinalPressureMatchingCoreInputNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure ((Fin q → ℝ) × ℝ)) := ⟨⟨0,inferInstance⟩⟩
local instance iidFinalPressureMatchingCorePlanNonempty (q : ℕ) :
    Nonempty (LocalFiniteMeasure (((Fin q → ℝ) × ℝ) × ((Fin q → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

local instance iidFinalPressureMatchingCoreMacroPairPolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidFinalPressureMatchingCoreSceneBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidFinalPressureMatchingCoreMacroBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance
local instance iidFinalPressureMatchingCoreMacroPairBorel (q : ℕ) :
    BorelSpace (OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ) ×
      OriginalIIDMaskedMacroCarrier (0 : (Fin q → ℝ) × ℝ)) := inferInstance

local instance iidFinalPressureMatchingCoreScenePolish (q : ℕ) :
    PolishSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidFinalPressureMatchingCoreSceneStandardBorel (q : ℕ) :
    StandardBorelSpace (OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance
local instance iidFinalPressureMatchingCoreTaggedSceneBorel (q : ℕ) :
    BorelSpace ((Fin q → ℝ) × OriginalIIDMaskedMacroInputScene (Fin q)) := inferInstance

include hcore hrecovery hκ horder hbalance hA hB hμ hν hreg hμreg hface hgap hdist


/-- Every actual measurable original optimizer cost and scale, with its genuine
physical kinetic budget, produces its own full stationary conditional matching
laws over the entire original core. No weak law, Poisson profile, pressureData,
probability lower field or pressure value is supplied. -/
theorem PopulationLocalPressureCore.original_actual_all_frames_conditional_matching_of_energy
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (budget : ℝ≥0∞) (hbudgetfinite : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale (finrank ℝ E-1) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (hdim : 2 ≤ finrank ℝ E) (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let V := Fin q → ℝ
    let X := V × ℝ
    let T := LocalFiniteMeasure X × LocalFiniteMeasure X
    let Scene := OriginalIIDMaskedMacroInputScene (Fin q)
    let Macro := OriginalIIDMaskedMacroCarrier (0 : X)
    let R := populationSeedRootLabelValue S a
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let φ := fun x ↦ e (R (a x))
    let K := e '' (R '' C.roots)
    let scale := physicalSceneCanonicalHaarScale q
    let mask := physicalSceneOriginalSeedSource
      (P := P) (a := a) (κ := κ) (lambda := μ.map a) C.seedIndex
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    let θ := fun c ↦ originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex (ref c)
    let α := fun c ↦ condDistrib u a μ (ref c)
    let β := fun c ↦ condDistrib u a ν (ref c)
    let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
      (physicalScene_centered_unitCube_mass (Fin q))
    let hm : MeasurableSet mask := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj C.seedIndex
    let hφ : Measurable φ := by
      have hp := measurable_physicalSceneOriginalSeedScaledPosition
        (P := P) (a := a) hF hcomplete hu ha hinj C.seedIndex (1 : ℝ)
      change Measurable (fun x ↦ (1 : ℝ) • φ x) at hp
      simpa only [one_smul] using hp
    let huM : Measurable u := by
      let _iidWholeCoreMatchingMetric : MetricSpace M := F.metricSpace
      exact hu.continuous.measurable
    ∃ Γ : Kernel V T, IsMarkovKernel Γ ∧
      ∀ (c0 : V) (m : ℕ → ℕ), StrictMono m →
      ∀ Q : ProbabilityMeasure (Macro × Macro),
      Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν
        (by simpa using original_seed_transverse_finrank_pos S hdim)
        (cost (m n)) (hcost (m n)) (k (m n)) (m n) mask hm
        (fun x ↦ scale (m n) • (φ x-c0))
        ((hφ.sub measurable_const).const_smul (scale (m n))) u huM) atTop (𝓝 Q) →
      let ρ := Q.map
        (continuous_originalIIDMaskedMacroInputSceneProjection (0 : X)).measurable.aemeasurable
      (ρ : Measure (V × Scene)).fst = (η : Measure V) ∧
      ∀ᵐ y ∂(η : Measure V).restrict ((fun y ↦ c0+y) ⁻¹' K),
        OriginalIIDConditionalMatchingProfile gap (θ (c0+y)) (α (c0+y)) (β (c0+y))
          (Γ (c0+y)) ((ρ : Measure (V × Scene)).condKernel y) := by
  intro C S q V X T Scene Macro R e φ K scale mask ref θ α β η hmask hφ huM
  let _iidWholeCoreMatchingMetric : MetricSpace M := F.metricSpace
  let _iidWholeCoreMatchingProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _iidWholeCoreMatchingPolish : PolishSpace M := inferInstance
  let _iidWholeCoreMatchingRootBorel : BorelSpace (ℚ → M) := inferInstance
  have hq : 0 < q := original_seed_transverse_finrank_pos S hdim
  have hqdim : 0 < Fintype.card (Fin q) := by simpa using hq
  have hdimker : q = finrank ℝ E - 1 := by
    have hh : q + 1 = finrank ℝ E := by
      simpa only [Module.finrank_prod, Module.finrank_self, add_comm] using
        S.normalization.toLinearEquiv.finrank_eq
    omega
  have henergyCore : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (scale n ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget := by
    simpa only [scale,hdimker] using henergy
  have hscale2 : Tendsto (fun n ↦ scale n ^ 2) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) (by decide : (2 : ℕ) ≠ 0)).comp
      (tendsto_physicalSceneCanonicalHaarScale q hq)
  obtain ⟨Γ,hΓ,hinput⟩ := D.original_translated_macro_conditional_input
    hF hcomplete hu ha hinj hdim i cost hcost k
  refine ⟨Γ,hΓ,?_⟩
  intro c0 m hm Q hweak
  have hQ := hinput c0 m hm Q hweak
  let coord := fun n x ↦ scale n • φ x-scale n • c0
  have hcoord (n : ℕ) : Measurable (coord n) :=
    (hφ.const_smul (scale n)).sub measurable_const
  have hw : Tendsto (fun n ↦ originalIIDMaskedBipartiteMacroLaw (0 : X) μ ν hqdim
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) mask hmask
      (coord (m n)) (hcoord (m n)) u huM) atTop (𝓝 Q) := by
    simpa only [coord,smul_sub] using hweak
  have hFull := ae_originalIID_fixed_seed_translated_masked_macro_input_marginals
    (hcore := hcore) (hrecovery := hrecovery) (hF := hF) (hcomplete := hcomplete)
    (hu := hu) (ha := ha) (hinj := hinj) (hκ := hκ) (horder := horder)
    (hbalance := hbalance) (hA := hA) (hB := hB) (hμ := hμ) (hν := hν)
    (hreg := hreg) (hμreg := hμreg) (hface := hface) (hgap := hgap) (hdist := hdist)
    (cost := cost) (hcost := hcost) (selectionScale := k)
    (spatialScale := scale) (hsp := physicalSceneCanonicalHaarScale_pos q) (hscale := hscale2)
    (j := C.seedIndex) (C := budget) (hC := hbudgetfinite) (henergy := henergyCore) (base := (0 : X))
    (fun n ↦ scale n • c0) hq m hm Q (by convert hw using 1; rfl)
  have hClock := ae_originalIIDMaskedMacro_weak_limit_clock_gap (0 : X) μ ν hqdim
    hgap hdist hμ hν cost hcost k (fun _ ↦ mask) (fun _ ↦ hmask)
    coord hcoord hu (fun n ↦ scale n ^ 2) (fun n ↦ sq_pos_of_pos (physicalSceneCanonicalHaarScale_pos q n))
    hscale2 budget hbudgetfinite henergyCore m hm Q hw
  exact ae_originalIIDMaskedMacro_conditional_matching_of_actual_data μ ν hq cost hcost
    k mask hmask coord hcoord u huM m hm Q hw hFull gap hClock η
    ((fun y ↦ c0+y) ⁻¹' K) c0 Γ θ
    (fun c ↦ mul_nonneg (NNReal.coe_nonneg _)
      (populationAtlasTheta_nonneg P a κ (μ.map a) C.seedIndex (ref c)))
    α β hQ.1 hQ.2.2

end OTSelector.Reconstruction
