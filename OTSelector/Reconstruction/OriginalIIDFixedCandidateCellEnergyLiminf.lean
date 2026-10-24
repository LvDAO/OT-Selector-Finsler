import OTSelector.Reconstruction.OriginalIIDActualKineticFinite
import OTSelector.Reconstruction.OriginalIIDOwnerPalmIntegralTransfer
import OTSelector.Reconstruction.OriginalIIDTranslatedClockGuard

/-! One actual auxiliary-cell/owner lower readout of the SAME fixed scene
candidate. The true original frame weak law supplies its own pair conditional
Palm; this module identifies its local LSC readout with the fixed raw matrix
on the original measured core, before any energy budget is paid. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M}
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}


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
theorem PopulationLocalPressureCore.fixed_candidate_owner_clock_cutoff_energy_liminf
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (hq : 0 < q) (H : Set M) (hH : MeasurableSet H)
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
    let Γclock := fun n ξ ↦ (Γ n ξ).restrict {p | (u p.1,u p.2) ∈
      (D.haar.continuous.coefficient i).window.region}
    let rootValue := physicalSceneOriginalMacroRootValue (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex
    (∫⁻ c in A, ∫⁻ mark, ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B)
      (ENNReal.ofReal (matrixQuadratic
        (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
          (D.haar.continuous.coefficient i).seedIndex (c,mark.1)) mark.2))
      ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDWholeCoreSceneKernel K hK Q c).map Prod.fst)) ∂volume) ≤
      liminf (fun n ↦ ∫⁻ ξ, ∫⁻ root,
        ENNReal.ofReal ((m n : ℝ)+1) * cavityRootWindowReadout (Γ (m n) ξ)
          (fun p ↦ coord (m n) p.1)
          (fun p ↦ ENNReal.ofReal ((s (m n))^2 *
            ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+ε)) U
          (root+s (m n) • center) +
        ENNReal.ofReal B * (ENNReal.ofReal ((m n : ℝ)+1) *
          D.originalTaylorGuardMass i R (s (m n)) U
            (rootValue (center+tag (m n) root)) (root+s (m n) • center) (Γclock (m n) ξ))
        ∂cavityRootMeasure volume
          (physicalSceneCanonicalHaarDomain q (m n) ∩ tag (m n) ⁻¹'
            ((fun w ↦ center+w) ⁻¹' A)) ((m n : ℝ)+1)
        ∂law (m n)) atTop := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro center s tag coord shifted Qplan hweak A hA howner hcore B U hU hsub law Γ Γclock rootValue
  obtain ⟨energy,he0,heq,hlim⟩ :=
    D.exists_translated_fixed_candidate_clock_cutoff_local_energy_liminf
      hF hcomplete hu ha hinj horder i hq H hH ψ hψrange hψsupport center R hR hε cost hcost k
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
    ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B) (ENNReal.ofReal (matrixQuadratic
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (c,mark.1)) mark.2))
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
    exact (D.clock_cutoff_macro_energy_eq_fixed_raw hF hcomplete hu ha hinj i ψ
      hψsupport energy heq B (hAlocalCore hw) mark).symm
  rw [hequality]
  change (∫⁻ w, ∫⁻ mark, ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B)
      (ENNReal.ofReal (energy (center+w,mark)))
      ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDFixedCandidatePairPlanJoint (Q j)).condKernel w))
      ∂(originalIIDFixedCandidatePairPlanJoint (Q j)).fst.restrict Alocal) ≤ _ at hpalm
  rw [hfirst] at hpalm
  exact hpalm

end OTSelector.Reconstruction
