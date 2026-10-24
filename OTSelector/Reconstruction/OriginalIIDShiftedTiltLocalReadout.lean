import OTSelector.MeasureTheory.Integral.GuardedClippedWindow
import OTSelector.Reconstruction.OriginalIIDActualKineticFinite
import OTSelector.Reconstruction.OriginalIIDFixedCandidateRootRecovery
import OTSelector.Reconstruction.OriginalIIDOwnerPalmIntegralTransfer

/-! The signed tilted original energy uses one nonnegative shifted observable
on the same weak candidate. Every finite RHS keeps its original local source
window so disjoint owner/root cells share one actual physical budget. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [local instance] kineticFinitePlanPolish kineticFinitePlanNonempty

section ShiftCancellation
variable {C Y : Type*} [MeasurableSpace C] [MeasurableSpace Y]
/-- The original joint root/Palm law has its actual unnormalized root mass. -/
theorem fixedCandidate_joint_mass_eq (η : Measure C) [SFinite η]
    (κ : Kernel C Y) [IsSFiniteKernel κ] (A : Set C) (hA : MeasurableSet A) :
    ((η.restrict A) ⊗ₘ κ) univ = fixedCandidateRootMass η κ A := by
  rw [Measure.compProd_apply MeasurableSet.univ]
  simp only [preimage_univ]
  exact (withDensity_apply _ hA).symm
/-- Adding a constant to a nonnegative fixed readout pays exactly the original
root/Palm mass. The variable energy may have infinite moment. -/
theorem lintegral_fixedCandidate_add_constant (η : Measure C) [SFinite η]
    (κ : Kernel C Y) [IsSFiniteKernel κ] (A : Set C) (hA : MeasurableSet A)
    (energy : C × Y → ℝ≥0∞) (henergy : Measurable energy) (shift : ℝ≥0∞) :
    (∫⁻ c in A, ∫⁻ y, energy (c,y)+shift ∂κ c ∂η) =
      (∫⁻ c in A, ∫⁻ y, energy (c,y) ∂κ c ∂η) + shift * fixedCandidateRootMass η κ A := by
  have hadd : Measurable (fun p : C × Y ↦ energy p+shift) := henergy.add measurable_const
  calc
    _ = ∫⁻ p, energy p+shift ∂((η.restrict A) ⊗ₘ κ) :=
      (Measure.lintegral_compProd hadd).symm
    _ = _ := by
      rw [lintegral_add_left henergy,lintegral_const,
        Measure.lintegral_compProd henergy,fixedCandidate_joint_mass_eq η κ A hA]
/-- Once a real readout is integrable, the same signed constant cancels with
its true mass; no Palm probability normalization occurs. -/
theorem integral_fixedCandidate_add_constant_sub_mass (η : Measure C) [SFinite η]
    (κ : Kernel C Y) [IsSFiniteKernel κ] (A : Set C) (hA : MeasurableSet A)
    (hfinite : fixedCandidateRootMass η κ A ≠ (∞ : ℝ≥0∞))
    (value : C × Y → ℝ) (hvalue : Integrable value ((η.restrict A) ⊗ₘ κ)) (shift : ℝ) :
    (∫ p, value p+shift ∂((η.restrict A) ⊗ₘ κ)) -
      shift * (fixedCandidateRootMass η κ A).toReal =
        ∫ p, value p ∂((η.restrict A) ⊗ₘ κ) := by
  letI : IsFiniteMeasure ((η.restrict A) ⊗ₘ κ) :=
    ⟨by rw [fixedCandidate_joint_mass_eq η κ A hA];exact lt_top_iff_ne_top.mpr hfinite⟩
  rw [integral_add hvalue (integrable_const shift),integral_const,
    smul_eq_mul,Measure.real, fixedCandidate_joint_mass_eq η κ A hA]
  ring
end ShiftCancellation

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

/-- The complete fixed-seed tilted raw observable is independent of all
auxiliary retained cores. Physical endpoints use the original seed map and
unchanged clock pair; the bounded shift is exactly the probe norm. -/
def physicalSceneOriginalMacroShiftedTiltEnergy (j : ℕ) (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (p : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ (P j).seed.covector.ker))) : ℝ :=
  let S := (P j).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (p.1,p.2.1)) p.2.2 +
    t * g (populationSeedPhysicalMap S (e.symm p.1,p.2.1.1),
      populationSeedPhysicalMap S (e.symm p.1,p.2.1.2)) + |t| * ‖g‖

/-- The fixed original tilted observable is jointly measurable, including
outside the retained compact core where the original physical map completes it. -/
theorem measurable_physicalSceneOriginalMacroShiftedTiltEnergy
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (j : ℕ) (g : (M × M) →ᵇ ℝ) (t : ℝ) :
    Measurable (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a) j g t) := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  let S := (P j).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  have hkin : Measurable (fun p : (Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)) ↦
      matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j
        (p.1,p.2.1)) p.2.2) := continuous_matrixQuadratic.measurable.comp
    (((measurable_physicalSceneOriginalMacroCoefficient (P := P) hF hcomplete hu ha hinj j).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  have hp (clock : ((Fin (finrank ℝ S.covector.ker) → ℝ) ×
      PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker))) → ℝ) (hc : Measurable clock) :
      Measurable (fun p ↦ populationSeedPhysicalMap S (e.symm p.1,clock p)) :=
    (measurable_populationSeedPhysicalMap S).comp
      ((e.symm.continuous.measurable.comp measurable_fst).prodMk hc)
  exact ((hkin.add ((g.continuous.measurable.comp
    ((hp (fun p ↦ p.2.1.1) measurable_snd.fst.fst).prodMk
      (hp (fun p ↦ p.2.1.2) measurable_snd.fst.snd))).const_mul t)).add_const (|t| * ‖g‖))

/-- Any auxiliary core reads the same complete original tilted observable
at every clock pair, so refining the core never changes its raw probe. -/
theorem PopulationLocalPressureCore.shifted_tilt_energy_eq_fixed_raw
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (g : (M × M) →ᵇ ℝ) (t : ℝ) (i : Fin D.haar.continuous.count)
    {z : ℚ → M} (hz : z ∈ (D.haar.continuous.coefficient i).roots)
    (mark : PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker))) :
    matrixQuadratic ((D.haar.continuous.coefficient i).matrix z mark.1) mark.2 +
      t * g (D.corePoint i (z,mark.1.1),D.corePoint i (z,mark.1.2)) + |t| * ‖g‖ =
    physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex g t (D.coreMacroLabel i z,mark) := by
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  let e := (Module.finBasis ℝ S.covector.ker).equivFunL
  let R := populationSeedRootLabelValue S a
  obtain ⟨hw,_⟩ := fixed_seed_rootLabel_recovery hF hcomplete hu ha hinj
    (D.haar.continuous.coefficient i).seedIndex
      ((D.haar.continuous.coefficient i).roots_subset_piece hz)
  have hpoint (s : ℝ) : populationSeedPhysicalMap S (e.symm (D.coreMacroLabel i z),s) =
      D.corePoint i (z,s) := by
    change populationSeedPhysicalMap S (e.symm (e (R z)),s) = D.corePoint i (z,s)
    rw [e.symm_apply_apply]
    exact populationSeedPhysicalMap_at_label S (⟨R z,hw⟩ : S.labels) s
  rw [D.original_matrix_eq_fixed_macro_coefficient hF hcomplete hu ha hinj i hz mark.1]
  dsimp only [physicalSceneOriginalMacroShiftedTiltEnergy]
  rw [hpoint,hpoint]

/-- The true finite Taylor comparison retains its physical source-window
readout before any Haar averaging. Disjoint auxiliary root cells may therefore
share one global physical-energy budget instead of paying it once per cell. -/
theorem PopulationLocalPressureCore.exists_uniform_original_shifted_tilt_clock_cutoff_local_readout_le
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
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ], ∀ B : ℝ,
      ∀ U : Set (D.coreSpatialCoordinateSpace i), MeasurableSet U →
      ∀ (z : ℚ → M) (root : D.coreSpatialCoordinateSpace i),
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex scale
      let Γclock := Γ.restrict {p | (u p.1,u p.2) ∈
        (D.haar.continuous.coefficient i).window.region}
      cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (z,((u p.1,u p.2),coord p.2-coord p.1))))) U root ≤
      cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ ENNReal.ofReal (scale^2 *
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)) U root +
      ENNReal.ofReal B * D.originalTaylorGuardMass i R scale U z root Γclock := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨threshold,hthreshold,herror⟩ :=
    D.exists_uniform_original_rooted_tilted_error hF hcomplete hu ha hinj horder i g t R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ B U hU z root coord Γclock
  let upper : M × M → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (scale^2 *
    ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)
  have hupper : Measurable upper :=
    (((((F.measurable_distance_slack hu).const_mul (scale^2)).add
      (g.continuous.measurable.const_mul t)).add_const (|t| * ‖g‖)).add_const ε).ennreal_ofReal
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ scale
  let W : Set (M × M) := {p | coord p.1-root ∈ U}
  let A := D.originalRootedTaylorWindow i R scale U z root
  let C : Set (M × M) := {p | (u p.1,u p.2) ∈
    (D.haar.continuous.coefficient i).window.region}
  have hW : MeasurableSet W :=
    hU.preimage ((hcoord.comp measurable_fst).sub measurable_const)
  have hA : MeasurableSet A :=
    D.measurableSet_originalRootedTaylorWindow hF hcomplete hu ha hinj i R scale hU _ _
  have hC : MeasurableSet C :=
    (D.haar.continuous.coefficient i).window.isCompact_region.measurableSet.preimage
      ((hu.continuous.measurable.comp measurable_fst).prodMk
        (hu.continuous.measurable.comp measurable_snd))
  have hpoint (p : M × M) (hp : p ∈ W ∩ A) :
      ENNReal.ofReal (energy (z,((u p.1,u p.2),coord p.2-coord p.1))) ≤ upper p := by
    have he := herror scale hs U z root p hp.2
    have heq' := heq z hp.2.1 (u p.1,u p.2) hp.2.2.2.2.2.2.2.1 (coord p.2-coord p.1)
    apply ENNReal.ofReal_le_ofReal
    rw [heq']
    change D.originalRootedTaylorKinetic i scale z p +
      t * D.originalRootedFrozenProbe i g z p + |t| * ‖g‖ ≤ _
    linarith [(abs_le.mp he).2]
  have hbound := lintegral_guarded_window_clipped_le Γ W A C hW hA hC
    (fun p ↦ ψ (u p.1,u p.2))
    (fun p ↦ ENNReal.ofReal (energy (z,((u p.1,u p.2),coord p.2-coord p.1))))
    upper hupper (fun p ↦ hψ (u p.1,u p.2)) (fun p hp ↦ hψzero _ hp) hpoint
    (ENNReal.ofReal B)
  have hmass : Γ ((W \ A) ∩ C) = D.originalTaylorGuardMass i R scale U z root Γclock := by
    change Γ ((W \ A) ∩ C) = (Γ.restrict C) (W \ A)
    rw [Measure.restrict_apply (hW.diff hA)]
  change (∫⁻ p, W.indicator
    (fun p ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B)
      (ENNReal.ofReal (energy (z,((u p.1,u p.2),coord p.2-coord p.1))))) p ∂Γ) ≤
    (∫⁻ p, W.indicator upper p ∂Γ) + _
  simpa only [hmass] using hbound

theorem PopulationLocalPressureCore.exists_uniform_original_shifted_tilt_clock_cutoff_translated_local_readout_le
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
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ], ∀ B : ℝ,
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
      cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ ENNReal.ofReal (scale^2 *
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)) U (root+scale • center) +
      ENNReal.ofReal B * D.originalTaylorGuardMass i R scale U z (root+scale • center) Γclock := by
  obtain ⟨threshold,hthreshold,hbound⟩ :=
    D.exists_uniform_original_shifted_tilt_clock_cutoff_local_readout_le hF hcomplete hu ha hinj horder
      g t i energy heq ψ hψ hψzero R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ B U hU z root coord shifted Γclock
  have hread := cavityRootWindowReadout_translate_clock_energy Γ
    (fun p ↦ coord p.1) (fun p ↦ coord p.2) (fun p ↦ (u p.1,u p.2))
    (fun m ↦ ψ m.1 * min (ENNReal.ofReal B) (ENNReal.ofReal (energy (z,m))))
    (scale • center) root U
  change cavityRootWindowReadout Γ (fun p ↦ coord p.1-scale • center)
      (fun p ↦ ψ (u p.1,u p.2) * min (ENNReal.ofReal B) (ENNReal.ofReal
        (energy (z,((u p.1,u p.2),(coord p.2-scale • center)-(coord p.1-scale • center))))))
      U root ≤ _
  rw [hread]
  exact hbound scale hs Γ B U hU z (root+scale • center)

/-- The SAME translated actual weak law has a measured-core Palm lower bound
whose finite RHS remains in the original physical coordinate and local root
window. This supplies one disjoint-cell budget across every original owner. -/
theorem PopulationLocalPressureCore.exists_translated_fixed_candidate_shifted_tilt_clock_cutoff_local_energy_liminf
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
        ENNReal.ofReal ((m n : ℝ)+1) * cavityRootWindowReadout (Γ (m n) ξ)
          (fun p ↦ coord (m n) p.1)
          (fun p ↦ ENNReal.ofReal ((s (m n))^2 *
            ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)) U
          (root+s (m n) • center) +
        ENNReal.ofReal B * (ENNReal.ofReal ((m n : ℝ)+1) *
          D.originalTaylorGuardMass i R (s (m n)) U
            (rootValue (center+tag (m n) root)) (root+s (m n) • center) (Γclock (m n) ξ))
        ∂cavityRootMeasure volume (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1)
        ∂law (m n)) atTop := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro q s rootDomain tag law Γ Γclock coord shifted rootValue
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
    D.exists_uniform_original_shifted_tilt_clock_cutoff_translated_local_readout_le
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
  have hcompare := hpoint (s (m n)) hn (Γ (m n) ξ) B U hU.measurableSet
    (rootValue (center+tag (m n) root)) root
  have hscaled := mul_le_mul_of_nonneg_left hcompare
    (bot_le : 0 ≤ ENNReal.ofReal ((m n : ℝ)+1))
  simpa only [Ftrunc,Eread,hmacro _ (hAsub hr),mul_add,mul_left_comm] using hscaled

/-- Every auxiliary continuous extension gives the SAME raw fixed-seed
clipped observable after multiplication by the produced clock cutoff.
This equality is pointwise on the full measured core, including its boundary. -/
theorem PopulationLocalPressureCore.clock_cutoff_macro_shifted_tilt_energy_eq_fixed_raw
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (i : Fin D.haar.continuous.count)
    (ψ : C(ℝ × ℝ,ℝ))
    (hψsupport : tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region)
    (energy : D.coreSpatialCoordinateSpace i × PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) → ℝ)
    (heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (D.coreMacroLabel i z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t * g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖)
    (B : ℝ) {w : D.coreSpatialCoordinateSpace i}
    (hw : w ∈ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots)
    (mark : PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker))) :
    ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B) (ENNReal.ofReal (energy (w,mark))) =
      ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B) (ENNReal.ofReal
        (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a)
          (D.haar.continuous.coefficient i).seedIndex g t (w,mark))) := by
  obtain ⟨z,hz,rfl⟩ := hw
  by_cases hc : mark.1 ∈ (D.haar.continuous.coefficient i).window.region
  · rw [heq z hz mark.1 hc mark.2,
      D.shifted_tilt_energy_eq_fixed_raw hF hcomplete hu ha hinj g t i hz mark]
  · have hn : mark.1 ∉ tsupport ψ := fun h ↦ hc (hψsupport h)
    rw [image_eq_zero_of_notMem_tsupport hn,ENNReal.ofReal_zero,zero_mul,zero_mul]

/-- The bounded tilt shift is paid against the exact ORIGINAL lambda mass
of the same raw candidate. Thus removing the shift after the finite-height
lower passage subtracts |t|‖g‖ lambda(L), with no unit-Palm convention. -/
theorem PopulationHaarPressureCore.fixed_candidate_original_tilt_shift_mass_eq_label
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)] [∀ j, (κ j).IsAddHaarMeasure]
    (D : PopulationHaarPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (i : Fin D.continuous.count) :
    let C := D.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := Module.finrank ℝ S.covector.ker
    let e := (Module.finBasis ℝ S.covector.ker).equivFunL
    let R := populationSeedRootLabelValue S a
    let K := e '' (R '' C.roots)
    let ref := fun c ↦ a (S.curve (e.symm c) 0)
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ) (α β : (Fin q → ℝ) → Measure ℝ)
      (_ : ∀ c, IsProbabilityMeasure (α c)) (_ : ∀ c, IsProbabilityMeasure (β c))
      (input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
        LocalFiniteMeasure (LegalMarkedPhysicalPoint q))),
      (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
        OriginalIIDConditionalMatchingProfile gap
          (originalSeedCoordinateIntensity P a κ lambda C.seedIndex (ref c))
          (α c) (β c) (input c) (Λ c)) →
      ∀ {L : Set (ℚ → M)}, MeasurableSet L → L ⊆ C.roots →
        (∫⁻ c in e '' (R '' L), ∫⁻ _mark, ENNReal.ofReal (|t| * ‖g‖)
          ∂originalIIDRawPairPalmKernel Λ c ∂(volume : Measure (Fin q → ℝ))) =
            ENNReal.ofReal (|t| * ‖g‖) * lambda L := by
  intro C S q e R K ref Λ gap α β hα hβ input hprofile L hL hsub
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  have hA : MeasurableSet (e '' (R '' L)) :=
    e.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (D.measurable_cell_label_image hcomplete i hL hsub)
  have hmass := D.fixed_candidate_raw_palm_mass_eq_label hF hcomplete hu ha hinj i
    Λ gap α β hα hβ input hprofile hL hsub
  simp_rw [lintegral_const]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  change ENNReal.ofReal (|t| * ‖g‖) *
    (∫⁻ c in e '' (R '' L), originalIIDRawPairPalmKernel Λ c univ ∂volume) = _
  rw [←withDensity_apply _ hA]
  exact congrArg (ENNReal.ofReal (|t| * ‖g‖) * ·) hmass

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
theorem PopulationLocalPressureCore.fixed_candidate_owner_shifted_tilt_clock_cutoff_energy_liminf
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
      (ENNReal.ofReal (physicalSceneOriginalMacroShiftedTiltEnergy (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex g t (c,mark)))
      ∂cubePalm (Fin q) (physicalScenePairCampbell
        ((originalIIDWholeCoreSceneKernel K hK Q c).map Prod.fst)) ∂volume) ≤
      liminf (fun n ↦ ∫⁻ ξ, ∫⁻ root,
        ENNReal.ofReal ((m n : ℝ)+1) * cavityRootWindowReadout (Γ (m n) ξ)
          (fun p ↦ coord (m n) p.1)
          (fun p ↦ ENNReal.ofReal ((s (m n))^2 *
            ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t * g p+|t| * ‖g‖+ε)) U
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
    D.exists_translated_fixed_candidate_shifted_tilt_clock_cutoff_local_energy_liminf
      hF hcomplete hu ha hinj horder g t i hq H hH ψ hψrange hψsupport center R hR hε cost hcost k
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

end OTSelector.Reconstruction
