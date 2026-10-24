import OTSelector.Reconstruction.OriginalIIDClockRestrictedGuardVanish
import OTSelector.Reconstruction.OriginalIIDTranslatedWindowBudget

/-! The actual original Taylor guard in translated frame coordinates is
exactly the original guard on the translated root set. No input, optimizer,
mask, clock restriction or root normalization is changed. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 20000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
namespace PopulationLocalPressureCore

/-- Exact original guard readout after translating only the original frame
root. The raw reference and clock-restricted physical plan stay literal. -/
theorem originalIIDClockGuardExpectation_translated
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (n : ℕ) (cost : M → M → ℝ)
    (selectionScale R s : ℝ) (hs : s ≠ 0)
    (center : D.coreSpatialCoordinateSpace i) (roots U : Set (D.coreSpatialCoordinateSpace i))
    (hroots : MeasurableSet roots)
    (hcore : roots ⊆ (fun root ↦ center+physicalSceneMacroscopicRoot s root) ⁻¹'
      (D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots)) :
    let C := D.haar.continuous.coefficient i
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := lambda) C.seedIndex
    let Γclock := fun ξ ↦
      ((originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale ξ).restrict (H ×ˢ univ)).restrict
        {p | (u p.1,u p.2) ∈ C.window.region}
    D.originalIIDClockGuardExpectation i n cost selectionScale R s
      ((fun root ↦ s • center+root) '' roots) U =
      ∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n+1 : ℕ) : ℝ) *
        D.originalTaylorGuardMass i R s U
          (physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
            (center+physicalSceneMacroscopicRoot s root)) (s • center+root) (Γclock ξ)
        ∂cavityRootMeasure volume roots ((n+1 : ℕ) : ℝ)
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν)) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro C H Γclock
  have htag (root : D.coreSpatialCoordinateSpace i) :
      s⁻¹ • root = physicalSceneMacroscopicRoot s root := by
    ext k
    simp [physicalSceneMacroscopicRoot,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  unfold originalIIDClockGuardExpectation
  apply lintegral_congr
  intro ξ
  rw [← lintegral_cavityRootMeasure_add_const roots ((n+1 : ℕ) : ℝ) (s • center)]
  apply lintegral_congr_ae
  have hrootae : ∀ᵐ root ∂cavityRootMeasure volume roots ((n+1 : ℕ) : ℝ), root ∈ roots :=
    Measure.ae_smul_measure (ae_restrict_mem hroots) _
  filter_upwards [hrootae] with root hr
  obtain ⟨z,hz,hcoord⟩ := hcore hr
  change D.coreMacroLabel i z = center+physicalSceneMacroscopicRoot s root at hcoord
  have hvalue : physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
      (D.coreMacroLabel i z) = z := by
    exact physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj _
      ((D.haar.continuous.coefficient i).roots_subset_piece hz)
  rw [htag,physicalSceneMacroscopicRoot_add_scale_center hs,← hcoord,
    D.originalRootedTaylorReference_coreMacroLabel hF hcomplete hu ha hinj i hz,hvalue]

/-- The genuine original guard producer applies in each translated original
frame, uniformly over every measured subcore. All root domains retain mass
n+1, and no guard/tail or conditional energy bound is postulated. -/
theorem exists_eventually_originalIID_translated_clock_guard_small
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
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (selectionScale : ℕ → ℝ)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (center : D.coreSpatialCoordinateSpace i)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale
        (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (selectionScale n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    {U : Set (D.coreSpatialCoordinateSpace i)} (hU : MeasurableSet U)
    (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    let C := D.haar.continuous.coefficient i
    let q := finrank ℝ (P C.seedIndex).seed.covector.ker
    let s := physicalSceneCanonicalHaarScale q
    let tag := fun n ↦ physicalSceneMacroscopicRoot (s n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ)
      (lambda := μ.map a) C.seedIndex
    let Γclock := fun n ξ ↦
      ((originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (selectionScale n) ξ).restrict
        (H ×ˢ univ)).restrict {p | (u p.1,u p.2) ∈ C.window.region}
    ∀ η : ℝ≥0∞, 0 < η → ∃ R : ℝ, 0 ≤ R ∧ W ≤ R ∧
      ∀ᶠ n in atTop, ∀ A : Set (D.coreSpatialCoordinateSpace i), MeasurableSet A →
        A ⊆ (fun w ↦ center+w) ⁻¹' (D.coreMacroLabel i '' C.roots) →
        (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
          D.originalTaylorGuardMass i R (s n) U
            (physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
              (center+tag n root)) (root+s n • center) (Γclock n ξ)
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain q n ∩ tag n ⁻¹' A)
            ((n : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ η := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  intro C q s tag H Γclock η hη
  let fullRoots := fun n ↦ (fun root ↦ s n • center+root) '' physicalSceneCanonicalHaarDomain q n
  have hfull (n : ℕ) : volume (fullRoots n) = ENNReal.ofReal ((n+1 : ℕ) : ℝ) := by
    have hm : MeasurableSet (fullRoots n) :=
      (measurableEmbedding_addLeft (s n • center)).measurableSet_image.mpr measurableSet_Icc
    have hp := (measurePreserving_add_left (volume : Measure (Fin q → ℝ))
      (s n • center)).measure_preimage hm.nullMeasurableSet
    rw [Set.preimage_image_eq _ (measurableEmbedding_addLeft (s n • center)).injective] at hp
    simpa only [Nat.cast_add,Nat.cast_one] using hp.symm.trans
      (volume_physicalSceneCanonicalHaarDomain q hq n)
  have hsp : ∀ n, 0 < s n := physicalSceneCanonicalHaarScale_pos q
  have hnorm : ∀ n, s n ^ q = ((n+1 : ℕ) : ℝ) := by
    intro n
    simpa only [Nat.cast_add,Nat.cast_one] using physicalSceneCanonicalHaarScale_pow q hq n
  obtain ⟨R,hR,hRW,hevent⟩ := exists_eventually_originalIID_clock_guard_small
    hpopulation hrecovery D hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist i cost hcost selectionScale s hsp
    (tendsto_physicalSceneCanonicalHaarScale q hq) hnorm fullRoots hfull budget hbudget henergy
    hU W hW η hη
  refine ⟨R,hR,hRW,?_⟩
  filter_upwards [hevent] with n hn
  intro A hAmeas hAsub
  let roots := physicalSceneCanonicalHaarDomain q n ∩ tag n ⁻¹' A
  have hroots : MeasurableSet roots := measurableSet_Icc.inter
    (hAmeas.preimage (continuous_physicalSceneMacroscopicRoot (s n)).measurable)
  let shiftedRoots := (fun root ↦ s n • center+root) '' roots
  have hshifted : MeasurableSet shiftedRoots :=
    (measurableEmbedding_addLeft (s n • center)).measurableSet_image.mpr hroots
  have hrootscore : roots ⊆ (fun root ↦ center+physicalSceneMacroscopicRoot (s n) root) ⁻¹'
      (D.coreMacroLabel i '' C.roots) := fun root hr ↦ hAsub hr.2
  have hinv (root : D.coreSpatialCoordinateSpace i) :
      (s n)⁻¹ • root = physicalSceneMacroscopicRoot (s n) root := by
    ext k
    simp [physicalSceneMacroscopicRoot,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  have hcore : shiftedRoots ⊆ (fun root ↦ (s n)⁻¹ • root) ⁻¹'
      (D.coreMacroLabel i '' C.roots) := by
    rintro root ⟨r,hr,rfl⟩
    change (s n)⁻¹ • (s n • center+r) ∈ (D.coreMacroLabel i '' C.roots)
    rw [hinv,physicalSceneMacroscopicRoot_add_scale_center (hsp n).ne']
    exact hrootscore hr
  have hsub : shiftedRoots ⊆ fullRoots n := image_mono inter_subset_left
  have hbound := hn shiftedRoots hshifted hsub hcore
  rw [originalIIDClockGuardExpectation_translated D hF hcomplete hu ha hinj i n
    (cost n) (selectionScale n) R (s n) (hsp n).ne' center roots U hroots hrootscore] at hbound
  simp only [Nat.cast_add,Nat.cast_one] at hbound
  have hpoint (root : D.coreSpatialCoordinateSpace i) :
      s n • center+root = root+s n • center := add_comm _ _
  simp_rw [hpoint] at hbound
  exact hbound

end PopulationLocalPressureCore
end OTSelector.Reconstruction
