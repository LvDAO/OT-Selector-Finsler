import OTSelector.Reconstruction.OriginalIIDActualTaggedEnergyLiminf
import OTSelector.Reconstruction.OriginalIIDColoredConditionalCandidate
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedDisplacement

/-! Actual kinetic-energy steps for the unchanged original candidate. Dilation
retains the complete matrix kernel. A supported clock cutoff removes the clock
complement from finite full-plan comparisons without declaring full PN clock
support. Remaining endpoint and spatial losses stay literal same-plan masses. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

local instance actualKineticPlanPolish (q : ℕ) :
    PolishSpace (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) :=
  LocalFiniteMeasure.instPolishSpace

/-- The complete matrix kinetic mean of the same actual colored candidate
transforms by the exact Palm Jacobian times the square of physical dilation. -/
theorem lintegral_originalUnitColoredLaw_matrix_energy (q : ℕ)
    (Q : ProbabilityMeasure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))
    (hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) < (⊤ : ℝ≥0∞))
    (d : ℝ) (hd : d ≠ 0)
    (A : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A) :
    (∫⁻ m, ENNReal.ofReal (matrixQuadratic (A m.1) m.2)
      ∂legalMarkedJointPalm q (originalUnitColoredLaw q Q d hd)) =
      ENNReal.ofReal |(d^q)⁻¹| * ENNReal.ofReal (d^2) *
        (∫⁻ m, ENNReal.ofReal (matrixQuadratic (A m.1) m.2)
          ∂cubePalm (Fin q) (physicalScenePairCampbell
            ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))) := by
  have hm : Measurable (fun m : PhysicalPairPalmMark (Fin q) ↦
      ENNReal.ofReal (matrixQuadratic (A m.1) m.2)) :=
    (continuous_matrixQuadratic.measurable.comp
      ((hA.comp measurable_fst).prodMk measurable_snd)).ennreal_ofReal
  rw [originalUnitColoredLaw_palm_dilation q Q hstat hunit d hd,
    lintegral_smul_measure,lintegral_map hm (measurable_legalPairMarkDilation q d)]
  simp only [legalPairMarkDilation,matrixQuadratic_smul,
    ENNReal.ofReal_mul (sq_nonneg d)]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,mul_assoc]
  rfl

/-- Finiteness of the same full matrix kinetic is equivalent before and after
normalizing the actual colored candidate. No new candidate is chosen. -/
theorem integrable_originalUnitColoredLaw_matrix_iff (q : ℕ)
    (Q : ProbabilityMeasure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (hstat : ∀ v, MeasurePreserving (physicalSceneReroot v)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)
      ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))
    (hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)}
      ∂((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst)) < (⊤ : ℝ≥0∞))
    (d : ℝ) (hd : d ≠ 0)
    (A : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A) :
    Integrable (fun m ↦ matrixQuadratic (A m.1) m.2)
      (legalMarkedJointPalm q (originalUnitColoredLaw q Q d hd)) ↔
    Integrable (fun m ↦ matrixQuadratic (A m.1) m.2)
      (cubePalm (Fin q) (physicalScenePairCampbell
        ((Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q))).map Prod.fst))) := by
  have hm : Measurable (fun m : PhysicalPairPalmMark (Fin q) ↦
      matrixQuadratic (A m.1) m.2) := continuous_matrixQuadratic.measurable.comp
    ((hA.comp measurable_fst).prodMk measurable_snd)
  have hpos : 0 < |(d^q)⁻¹| := abs_pos.mpr (inv_ne_zero (pow_ne_zero _ hd))
  rw [originalUnitColoredLaw_palm_dilation q Q hstat hunit d hd,
    integrable_smul_measure (ENNReal.ofReal_ne_zero_iff.mpr hpos) ENNReal.ofReal_ne_top,
    integrable_map_measure hm.aestronglyMeasurable
      (measurable_legalPairMarkDilation q d).aemeasurable]
  simpa only [Function.comp_def,legalPairMarkDilation,matrixQuadratic_smul] using
    integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hd))
      (fun m : PhysicalPairPalmMark (Fin q) ↦ matrixQuadratic (A m.1) m.2)

section DisjointDomains
variable {I X ι : Type*} [Fintype I] [Fintype ι] [MeasurableSpace X]

/-- Disjoint actual macro cells pay the original physical energy once. This
keeps auxiliary refinement from multiplying the budget by its number of cells. -/
theorem lintegral_cavityRoot_disjoint_domains_window_sum_le
    (Γ : Measure X) [IsFiniteMeasure Γ]
    (coord : X → (ι → ℝ)) (hcoord : Measurable coord)
    (upper : X → ℝ≥0∞) (hupper : Measurable upper)
    (rootDomain U : Set (ι → ℝ)) (hU : MeasurableSet U) (N : ℝ) (hN : 0 < N)
    (cells : I → Set (ι → ℝ)) (hmeas : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j))) :
    (∑ i, ∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout Γ coord upper U root
      ∂cavityRootMeasure volume (rootDomain ∩ cells i) N) ≤
      volume U * ∫⁻ x, upper x ∂Γ := by
  classical
  let f := fun root ↦ ENNReal.ofReal N * cavityRootWindowReadout Γ coord upper U root
  have heq (i : I) : cavityRootMeasure volume (rootDomain ∩ cells i) N =
      (cavityRootMeasure volume rootDomain N).restrict (cells i) :=
    (cavityRootMeasure_restrict_tag_core volume rootDomain N id measurable_id
      (cells i) (hmeas i)).symm
  change (∑ i, ∫⁻ root, f root ∂cavityRootMeasure volume (rootDomain ∩ cells i) N) ≤ _
  simp_rw [heq]
  calc
    _ = ∫⁻ root in ⋃ i, cells i, f root ∂cavityRootMeasure volume rootDomain N := by
      simpa only [tsum_fintype] using (lintegral_iUnion hmeas hdisjoint f).symm
    _ ≤ ∫⁻ root, f root ∂cavityRootMeasure volume rootDomain N :=
      setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_cavityRoot_scaled_window_le volume Γ coord hcoord upper hupper U hU
      rootDomain N hN
end DisjointDomains

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

/-- A supported clock cutoff estimates the SAME full plan, while the clock
restriction is used only inside the finite comparison. Its remainder contains
no mass from the complement of the original legal clock window. -/
theorem exists_uniform_original_clock_cutoff_kinetic_energy_le
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (i : Fin D.haar.continuous.count)
    (energy : (ℚ → M) × PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) → ℝ)
    (heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp)
    (ψ : (ℝ × ℝ) → ℝ≥0∞) (hψ : ∀ clocks, ψ clocks ≤ 1)
    (hψzero : ∀ clocks, clocks ∉ (D.haar.continuous.coefficient i).window.region → ψ clocks = 0)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ], ∀ B : ℝ,
      ∀ (rootDomain U : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet U →
      ∀ N : ℝ, 0 < N → ∀ ref : D.coreSpatialCoordinateSpace i → (ℚ → M),
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex scale
      let Γclock := Γ.restrict {p | (u p.1,u p.2) ∈
        (D.haar.continuous.coefficient i).window.region}
      (∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1))))) U root
        ∂cavityRootMeasure volume rootDomain N) ≤
      volume U * ((∫⁻ p, ENNReal.ofReal (scale^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)) ∂Γ) +
          ENNReal.ofReal ε * Γ univ) + ENNReal.ofReal B *
      (∫⁻ root, ENNReal.ofReal N *
        D.originalTaylorGuardMass i R scale U (ref root) root Γclock
        ∂cavityRootMeasure volume rootDomain N) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  have heq0 : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            0 * (0 : (M × M) →ᵇ ℝ)
              (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) +
                |(0 : ℝ)| * ‖(0 : (M × M) →ᵇ ℝ)‖ := by
    simpa using heq
  obtain ⟨threshold,hthreshold,hbound⟩ :=
    D.exists_uniform_original_full_plan_truncated_energy_le hF hcomplete hu ha hinj horder
      i 0 0 energy heq0 R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ B rootDomain U hU N hN ref coord Γclock
  let clockCarrier : Set (M × M) := {p | (u p.1,u p.2) ∈
    (D.haar.continuous.coefficient i).window.region}
  have hclock : MeasurableSet clockCarrier :=
    (D.haar.continuous.coefficient i).window.isCompact_region.measurableSet.preimage
      ((hu.continuous.measurable.comp measurable_fst).prodMk
        (hu.continuous.measurable.comp measurable_snd))
  have hwindow (root : D.coreSpatialCoordinateSpace i) :
      cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1))))) U root ≤
      cavityRootWindowReadout Γclock (fun p ↦ coord p.1)
        (fun p ↦ min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1))))) U root := by
    unfold cavityRootWindowReadout
    change (∫⁻ p, U.indicator (fun _ ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B)
      (ENNReal.ofReal (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1)))))
        (coord p.1-root) ∂Γ) ≤ ∫⁻ p in clockCarrier,
      U.indicator (fun _ ↦ min (ENNReal.ofReal B)
        (ENNReal.ofReal (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1)))))
          (coord p.1-root) ∂Γ
    rw [← lintegral_indicator hclock]
    apply lintegral_mono
    intro p
    dsimp only
    by_cases hc : (u p.1,u p.2) ∈ (D.haar.continuous.coefficient i).window.region
    · rw [indicator_of_mem (show p ∈ clockCarrier from hc)]
      by_cases hw : coord p.1-root ∈ U
      · simp only [indicator_of_mem hw]
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hψ (u p.1,u p.2))
          (bot_le : 0 ≤ min (ENNReal.ofReal B)
            (ENNReal.ofReal (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1)))))
      · simp only [indicator_of_notMem hw]
        exact le_rfl
    · rw [indicator_of_notMem (show p ∉ clockCarrier from hc)]
      by_cases hw : coord p.1-root ∈ U
      · simp only [indicator_of_mem hw,hψzero _ hc,zero_mul]
        exact le_rfl
      · simp only [indicator_of_notMem hw]
        exact le_rfl
  calc
    _ ≤ ∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout Γclock (fun p ↦ coord p.1)
        (fun p ↦ min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1))))) U root
        ∂cavityRootMeasure volume rootDomain N := by
      apply lintegral_mono
      intro root
      exact mul_le_mul_of_nonneg_left (hwindow root) bot_le
    _ ≤ volume U * ((∫⁻ p, ENNReal.ofReal (scale^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)) ∂Γclock) +
          ENNReal.ofReal ε * Γclock univ) + ENNReal.ofReal B *
      (∫⁻ root, ENNReal.ofReal N *
        D.originalTaylorGuardMass i R scale U (ref root) root Γclock
        ∂cavityRootMeasure volume rootDomain N) := by
      simpa only [zero_mul,zero_add,add_zero,abs_zero] using
        hbound scale hs Γclock B rootDomain U hU N hN ref
    _ ≤ _ := by
      apply add_le_add_left
      apply mul_le_mul_of_nonneg_left _ bot_le
      exact add_le_add (lintegral_mono' Measure.restrict_le_self le_rfl)
        (mul_le_mul_of_nonneg_left (Measure.restrict_le_self univ) bot_le)

/-- A genuine second-moment bound for the literal retained near part of each
original iid optimizer. The right side is its actual physical slack energy,
not a supplied moment or limit-energy hypothesis. This restriction is explicit. -/
theorem exists_originalIID_retained_near_second_moment_bound
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    : ∃ coeff > 0, ∃ radius > 0,
      ∀ (i : Fin D.haar.continuous.count) (n : ℕ) (cost : M → M → ℝ)
        (selectionScale spatialScale : ℝ) (H : Set M), MeasurableSet H →
      let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
        (Measure.pi (fun _ : Fin (n+1) ↦ ν))
      let Γ := originalIIDOptimalPhysicalPlan (n := n+1) cost selectionScale
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex spatialScale
      ENNReal.ofReal coeff *
        (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (‖coord p.2-coord p.1‖^2)
          ∂(Γ ξ).restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)) ∂law) ≤
        ∫⁻ ξ, ∫⁻ p, ENNReal.ofReal (spatialScale^2 *
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)) ∂Γ ξ ∂law := by
  obtain ⟨coeff,hcoeff,radius,hradius,hbound⟩ :=
    D.exists_uniform_rooted_nearDisplacement_energy_tail hF hcomplete hu ha hinj
  refine ⟨coeff,hcoeff,radius,hradius,?_⟩
  intro i n cost selectionScale spatialScale H hH law Γ coord
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro ξ
  exact (hbound i (Γ ξ) H hH spatialScale 1 (by norm_num) univ univ MeasurableSet.univ
    1 one_ne_zero (by finiteness)).1

/-- In the clock-localized estimate the clock-complement term is exactly zero;
only actual endpoint-core/regularity and rooted spatial losses remain. The full
observed plan in the comparison theorem itself stays unchanged. -/
theorem original_clock_restricted_guard_le_endpoint_spatial
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (i : Fin D.haar.continuous.count) (R scale : ℝ)
    (U : Set (D.coreSpatialCoordinateSpace i)) (z : ℚ → M)
    (root : D.coreSpatialCoordinateSpace i) (Γ : Measure (M × M))
    (hz : z ∈ (D.haar.continuous.coefficient i).roots)
    (hroot : root = scale • D.coreMacroLabel i z) :
    let C := D.haar.continuous.coefficient i
    let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
    let Γclock := Γ.restrict {p | (u p.1,u p.2) ∈ C.window.region}
    D.originalTaylorGuardMass i R scale U z root Γclock ≤
      Γclock ({p | coord p.1-root ∈ U} ∩ {p | ¬(a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧
        p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u)}) +
      Γclock ({p | coord p.1-root ∈ U} ∩ {p | ¬(‖coord p.1-root‖ ≤ R ∧ ‖coord p.2-root‖ ≤ R)}) := by
  letI : MetricSpace M := F.metricSpace
  intro C coord Γclock
  let I : Set (M × M) := {p | (u p.1,u p.2) ∈ C.window.region}
  have hI : MeasurableSet I := C.window.isCompact_region.measurableSet.preimage
    ((hu.continuous.measurable.comp measurable_fst).prodMk
      (hu.continuous.measurable.comp measurable_snd))
  have hzero : Γclock Iᶜ = 0 := by
    rw [Measure.restrict_apply hI.compl]
    change Γ (Iᶜ ∩ I) = 0
    simp only [compl_inter_self,measure_empty]
  have hzero' : Γclock ({p | coord p.1-root ∈ U} ∩ Iᶜ) = 0 :=
    le_antisymm ((measure_mono inter_subset_right).trans_eq hzero) bot_le
  dsimp only [C,coord,I] at hzero'
  simp only [compl_ofPred] at hzero'
  have hb := D.originalTaylorGuardMass_le_endpoint_clock_spatial i R scale U z root Γclock hz hroot
  simpa only [hzero',add_zero] using hb

/-- Canonical original iid averaging of the clock-localized full-plan kinetic
comparison preserves the exact source error ε·μ(H). The clock restriction is
confined to the remainder; the observed optimizer and root law are unchanged. -/
theorem eventually_originalIID_clock_cutoff_kinetic_energy_le
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (i : Fin D.haar.continuous.count)
    (energy : (ℚ → M) × PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) → ℝ)
    (heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp)
    (ψ : (ℝ × ℝ) → ℝ≥0∞) (hψ : ∀ clocks, ψ clocks ≤ 1)
    (hψzero : ∀ clocks, clocks ∉ (D.haar.continuous.coefficient i).window.region → ψ clocks = 0)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (H : Set M) (hH : MeasurableSet H)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) :
    let q := finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker
    let s := physicalSceneCanonicalHaarScale q
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := fun n ξ ↦
      (originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)
    let Γclock := fun n ξ ↦ (Γ n ξ).restrict {p | (u p.1,u p.2) ∈
      (D.haar.continuous.coefficient i).window.region}
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (s n)
    ∀ᶠ n in atTop, ∀ B : ℝ,
      ∀ (rootDomain U : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet U →
      ∀ ref : D.coreSpatialCoordinateSpace i → (ℚ → M),
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
        cavityRootWindowReadout (Γ n ξ) (fun p ↦ coord n p.1)
          (fun p ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B) (ENNReal.ofReal
            (energy (ref root,((u p.1,u p.2),coord n p.2-coord n p.1))))) U root
        ∂cavityRootMeasure volume rootDomain ((n : ℝ)+1) ∂law n) ≤
      volume U * ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((s n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)) ∂Γ n ξ ∂law n) +
          ENNReal.ofReal ε * μ H) + ENNReal.ofReal B *
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
        D.originalTaylorGuardMass i R (s n) U (ref root) root (Γclock n ξ)
        ∂cavityRootMeasure volume rootDomain ((n : ℝ)+1) ∂law n) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro q s law Γ Γclock coord
  obtain ⟨threshold,hthreshold,hbound⟩ :=
    D.exists_uniform_original_clock_cutoff_kinetic_energy_le hF hcomplete hu ha hinj horder
      i energy heq ψ hψ hψzero R hR hε
  have hslarge : Tendsto s atTop atTop := tendsto_physicalSceneCanonicalHaarScale q hq
  filter_upwards [hslarge.eventually (eventually_ge_atTop threshold)] with n hn
  intro B rootDomain U hU ref
  let Ephys : ((Fin (n+1) → M) × (Fin (n+1) → M)) → ℝ≥0∞ := fun ξ ↦
    ∫⁻ p, ENNReal.ofReal ((s n)^2 *
      ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)) ∂Γ n ξ
  have hΓ : Measurable (Γ n) := measurable_physicalPlan_sourceRestriction _
    (measurable_originalIIDOptimalPhysicalPlan (cost n) (hcost n) (k n)) H hH
  have hE : Measurable Ephys := (Measure.measurable_lintegral
    (((F.measurable_distance_slack hu).const_mul ((s n)^2)).ennreal_ofReal)).comp hΓ
  have hm : Measurable (fun ξ ↦ Γ n ξ univ) := (Measure.measurable_coe MeasurableSet.univ).comp hΓ
  have hmean : (∫⁻ ξ, Γ n ξ univ ∂law n) = μ H := by
    have hprod : H ×ˢ (univ : Set M) = Prod.fst ⁻¹' H := by ext p; simp
    simpa only [Γ,Measure.restrict_apply_univ,hprod] using
      lintegral_originalIIDOptimalPhysicalPlan_source_event μ ν (cost n) (k n) hH
  calc
    _ ≤ ∫⁻ ξ, volume U * (Ephys ξ + ENNReal.ofReal ε * Γ n ξ univ) +
        ENNReal.ofReal B * (∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
          D.originalTaylorGuardMass i R (s n) U (ref root) root (Γclock n ξ)
          ∂cavityRootMeasure volume rootDomain ((n : ℝ)+1)) ∂law n := by
      apply lintegral_mono
      intro ξ
      exact hbound (s n) hn (Γ n ξ) B rootDomain U hU ((n : ℝ)+1) (by positivity) ref
    _ = _ := by
      have hsum : Measurable (fun ξ ↦ Ephys ξ+ENNReal.ofReal ε*Γ n ξ univ) :=
        hE.add (hm.const_mul _)
      have htotal : Measurable (fun ξ ↦ volume U*(Ephys ξ+ENNReal.ofReal ε*Γ n ξ univ)) :=
        hsum.const_mul _
      rw [lintegral_add_left htotal]
      congr 1
      · rw [lintegral_const_mul _ hsum,lintegral_add_left hE]
        congr 2
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hmean]
      · exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Every auxiliary original core reads the SAME fixed-seed macro matrix,
including at clocks outside its retained interval. Thus a true accuracy
refinement need not change the candidate's raw kinetic kernel. -/
theorem original_matrix_eq_fixed_macro_coefficient
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {z : ℚ → M}
    (hz : z ∈ (D.haar.continuous.coefficient i).roots) (clocks : ℝ × ℝ) :
    (D.haar.continuous.coefficient i).matrix z clocks =
      physicalSceneOriginalMacroCoefficient (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (D.coreMacroLabel i z,clocks) := by
  have hr : physicalSceneOriginalMacroRootValue (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (D.coreMacroLabel i z) = z :=
    physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj
      (D.haar.continuous.coefficient i).seedIndex
        ((D.haar.continuous.coefficient i).roots_subset_piece hz)
  unfold physicalSceneOriginalMacroCoefficient
  dsimp only
  rw [hr]
  rfl

end PopulationLocalPressureCore
end OTSelector.Reconstruction
