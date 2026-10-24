import OTSelector.MeasureTheory.Integral.GuardedClippedWindow
import OTSelector.Reconstruction.OriginalIIDActualKineticIntegrability
import OTSelector.Reconstruction.OriginalIIDUniformClockCutoff
import OTSelector.Reconstruction.OriginalIIDWholeCoreSceneKernel

/-! Same original weak candidate under auxiliary-core and clock refinements.
Every weak-limit parameter is universal and fixed before the retained measurable
root core is chosen. The original sample law, mask and full displacement persist. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

section ClockRemoval
variable {Ω V : Type*} [MeasurableSpace Ω] [MeasurableSpace V]

/-- A finite clipping loses at most its height times the actual missed clock
mass. This is a pointwise decomposition inside the unchanged measure. -/
theorem lintegral_min_le_clock_cutoff_add_missed
    (μ : Measure Ω) (clock : Ω → ℝ × ℝ) (hclock : Measurable clock)
    (ψ : C(ℝ × ℝ,ℝ)) (hrange : ∀ c, ψ c ∈ Icc 0 1)
    (energy : Ω → ℝ≥0∞) (henergy : Measurable energy) (B : ℝ≥0∞) (hB : B ≠ ⊤) :
    (∫⁻ x, min B (energy x) ∂μ) ≤
      (∫⁻ x, ENNReal.ofReal (ψ (clock x)) * min B (energy x) ∂μ) +
        B * (∫⁻ x, ENNReal.ofReal (1-ψ (clock x)) ∂μ) := by
  have hsplit (x : Ω) : ENNReal.ofReal (ψ (clock x)) +
      ENNReal.ofReal (1-ψ (clock x)) = 1 := by
    rw [← ENNReal.ofReal_add (hrange _).1 (sub_nonneg.mpr (hrange _).2)]
    simp
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (ψ (clock x)) * min B (energy x) +
        ENNReal.ofReal (1-ψ (clock x)) * B ∂μ := by
      apply lintegral_mono
      intro x
      calc
        min B (energy x) =
            (ENNReal.ofReal (ψ (clock x)) + ENNReal.ofReal (1-ψ (clock x))) *
              min B (energy x) := by rw [hsplit,one_mul]
        _ ≤ _ := by
          rw [add_mul]
          exact add_le_add_right (mul_le_mul_of_nonneg_left (min_le_left _ _) bot_le) _
    _ = _ := by
      have hweighted : Measurable (fun x ↦ ENNReal.ofReal (ψ (clock x)) *
          min B (energy x)) :=
        ((ψ.continuous.measurable.comp hclock).ennreal_ofReal).mul
          (measurable_const.min henergy)
      rw [lintegral_add_left hweighted,lintegral_mul_const' _ _ hB,mul_comm]

/-- The unnormalized raw Palm is estimated using its genuine theta-scaled
clock marginals. Only the auxiliary clock coupling is normalized internally;
the original mark measure and the conclusion keep their full raw mass. -/
theorem lintegral_raw_clock_cutoff_missed_le
    (ρ : Measure ((ℝ × ℝ) × V)) (α β : Measure ℝ) (θ : ℝ) (hθ : 0 < θ)
    (hsource : ρ.map (fun m ↦ m.1.1) = ENNReal.ofReal θ • α)
    (htarget : ρ.map (fun m ↦ m.1.2) = ENNReal.ofReal θ • β)
    (horder : ∀ᵐ m ∂ρ, m.1.1 ≤ m.1.2)
    (ψ : C(ℝ × ℝ,ℝ)) (loss : ℝ≥0∞)
    (hcutoff : ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π α β →
      (∀ᵐ c ∂π, c.1 ≤ c.2) → (∫⁻ c, ENNReal.ofReal (1-ψ c) ∂π) ≤ loss) :
    (∫⁻ m, ENNReal.ofReal (1-ψ m.1) ∂ρ) ≤ ENNReal.ofReal θ * loss := by
  let mass := ENNReal.ofReal θ
  have hmass0 : mass ≠ 0 := (ENNReal.ofReal_pos.mpr hθ).ne'
  have hmassTop : mass ≠ ⊤ := ENNReal.ofReal_ne_top
  let π : Measure (ℝ × ℝ) := mass⁻¹ • ρ.map Prod.fst
  have hπ : Vlasov.IsCoupling π α β := by
    constructor
    · dsimp [π]
      rw [Measure.map_smul,Measure.map_map measurable_fst measurable_fst]
      change mass⁻¹ • ρ.map (fun m ↦ m.1.1) = α
      rw [hsource,smul_smul,ENNReal.inv_mul_cancel hmass0 hmassTop,one_smul]
    · dsimp [π]
      rw [Measure.map_smul,Measure.map_map measurable_snd measurable_fst]
      change mass⁻¹ • ρ.map (fun m ↦ m.1.2) = β
      rw [htarget,smul_smul,ENNReal.inv_mul_cancel hmass0 hmassTop,one_smul]
  have horderπ : ∀ᵐ c ∂π, c.1 ≤ c.2 :=
    Measure.ae_smul_measure ((ae_map_iff measurable_fst.aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).mpr horder) _
  have hraw : mass • π = ρ.map Prod.fst := by
    dsimp [π]
    rw [smul_smul,ENNReal.mul_inv_cancel hmass0 hmassTop,one_smul]
  calc
    _ = ∫⁻ c, ENNReal.ofReal (1-ψ c) ∂ρ.map Prod.fst := by
      rw [lintegral_map (by fun_prop) measurable_fst]
    _ = mass * ∫⁻ c, ENNReal.ofReal (1-ψ c) ∂π := by
      rw [← hraw,lintegral_smul_measure]
      rfl
    _ ≤ _ := mul_le_mul_of_nonneg_left (hcutoff π hπ horderπ) bot_le

end ClockRemoval

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

/-- Overlapping auxiliary root cores necessarily use the same original seed.
Thus auxiliary accuracy refinement does not alter the literal finite masked
experiment on that overlap. -/
theorem original_seedIndex_eq_of_common_root
    (C : OriginalPopulationCoefficientCore P a κ lambda μ ν δ)
    {δ' : ℝ≥0∞} (C' : OriginalPopulationCoefficientCore P a κ lambda μ ν δ')
    {z : ℚ → M} (hz : z ∈ C.roots) (hz' : z ∈ C'.roots) :
    C.seedIndex = C'.seedIndex := by
  by_contra h
  exact Set.disjoint_left.mp (pairwiseDisjoint_populationSeedRootPiece P a κ lambda h)
    (C.roots_subset_piece hz) (C'.roots_subset_piece hz')

namespace PopulationLocalPressureCore

/-- The actual compact-root clock producer controls the SAME unnormalized raw
mark measure and removes its clock cutoff at each fixed clipping height.
Its theta-scaled marginals are the genuine original Palm clock identities. -/
theorem exists_uniform_raw_clock_cutoff_clipped_energy_bound
    {V : Type*} [MeasurableSpace V]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) {gap η : ℝ} (hgap : 0 < gap)
    (hwindow : ((D.haar.continuous.coefficient i).window.val.2.2 : ℝ) ≤ gap/2)
    (hη : 0 < η) :
    ∃ ψ : C(ℝ × ℝ,ℝ), IsCompact (tsupport ψ) ∧
      tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region ∧
      (∀ p, ψ p ∈ Icc 0 1) ∧
      ∀ z ∈ (D.haar.continuous.coefficient i).roots, ∀ diam : ℝ,
        ConditionalClockSupportBounds (condDistrib u a μ z) (condDistrib u a ν z)
          gap diam →
        ∀ θ : ℝ, 0 < θ → ∀ ρ : Measure ((ℝ × ℝ) × V),
          ρ.map (fun m ↦ m.1.1) = ENNReal.ofReal θ • condDistrib u a μ z →
          ρ.map (fun m ↦ m.1.2) = ENNReal.ofReal θ • condDistrib u a ν z →
          (∀ᵐ m ∂ρ, m.1.1 ≤ m.1.2) →
          (∫⁻ m, ENNReal.ofReal (1-ψ m.1) ∂ρ) ≤
              ENNReal.ofReal θ * (δ+ENNReal.ofReal η) ∧
          ∀ energy : ((ℝ × ℝ) × V) → ℝ≥0∞, Measurable energy → ∀ B : ℝ,
            (∫⁻ m, min (ENNReal.ofReal B) (energy m) ∂ρ) ≤
              (∫⁻ m, ENNReal.ofReal (ψ m.1) *
                min (ENNReal.ofReal B) (energy m) ∂ρ) +
              ENNReal.ofReal B * (ENNReal.ofReal θ * (δ+ENNReal.ofReal η)) := by
  obtain ⟨ψ,hcompact,hsub,hrange,hcutoff⟩ :=
    D.exists_uniform_original_clock_cutoff i hgap hwindow hη
  refine ⟨ψ,hcompact,hsub,hrange,?_⟩
  intro z hz diam hsep θ hθ ρ hsource htarget horder
  have hmiss := lintegral_raw_clock_cutoff_missed_le ρ
    (condDistrib u a μ z) (condDistrib u a ν z) θ hθ hsource htarget horder ψ
    (δ+ENNReal.ofReal η) (hcutoff z hz diam hsep)
  refine ⟨hmiss,?_⟩
  intro energy henergy B
  apply (lintegral_min_le_clock_cutoff_add_missed ρ Prod.fst measurable_fst ψ hrange
    energy henergy (ENNReal.ofReal B) ENNReal.ofReal_ne_top).trans
  exact add_le_add_right (mul_le_mul_of_nonneg_left hmiss bot_le) _

/-- The true finite Taylor comparison retains its physical source-window
readout before any Haar averaging. Disjoint auxiliary root cells may therefore
share one global physical-energy budget instead of paying it once per cell. -/
theorem exists_uniform_original_clock_cutoff_local_readout_le
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
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+ε)) U root +
      ENNReal.ofReal B * D.originalTaylorGuardMass i R scale U z root Γclock := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨threshold,hthreshold,herror⟩ :=
    D.exists_uniform_original_rooted_tilted_error hF hcomplete hu ha hinj horder i 0 0 R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ B U hU z root coord Γclock
  let upper : M × M → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (scale^2 *
    ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+ε)
  have hupper : Measurable upper :=
    (((F.measurable_distance_slack hu).const_mul (scale^2)).add_const ε).ennreal_ofReal
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
    change D.originalRootedTaylorKinetic i scale z p ≤ _
    simp only [zero_mul,add_zero] at he
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

/-- Every auxiliary continuous extension gives the SAME raw fixed-seed
clipped observable after multiplication by the produced clock cutoff.
This equality is pointwise on the full measured core, including its boundary. -/
theorem clock_cutoff_macro_energy_eq_fixed_raw
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count)
    (ψ : C(ℝ × ℝ,ℝ))
    (hψsupport : tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region)
    (energy : D.coreSpatialCoordinateSpace i × PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) → ℝ)
    (heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (D.coreMacroLabel i z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp)
    (B : ℝ) {w : D.coreSpatialCoordinateSpace i}
    (hw : w ∈ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots)
    (mark : PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker))) :
    ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B) (ENNReal.ofReal (energy (w,mark))) =
      ENNReal.ofReal (ψ mark.1) * min (ENNReal.ofReal B) (ENNReal.ofReal (matrixQuadratic
        (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
          (D.haar.continuous.coefficient i).seedIndex (w,mark.1)) mark.2)) := by
  obtain ⟨z,hz,rfl⟩ := hw
  by_cases hc : mark.1 ∈ (D.haar.continuous.coefficient i).window.region
  · rw [heq z hz mark.1 hc mark.2,
      D.original_matrix_eq_fixed_macro_coefficient hF hcomplete hu ha hinj i hz mark.1]
  · have hn : mark.1 ∉ tsupport ψ := fun h ↦ hc (hψsupport h)
    rw [image_eq_zero_of_notMem_tsupport hn,ENNReal.ofReal_zero,zero_mul,zero_mul]

local instance kineticClosurePlanPolish (ι : Type*) [Fintype ι] : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance kineticClosurePlanNonempty (ι : Type*) [Fintype ι] : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

/-- The produced original clock cutoff passes to the SAME actual conditional
Palm under any supplied original weak subsequence. Its literal remainder has
only endpoint and spatial guards inside the original clock window. -/
theorem exists_fixed_candidate_clock_cutoff_matrix_energy_liminf
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
    (i : Fin D.haar.continuous.count)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (H : Set M) (hH : MeasurableSet H)
    (ψ : C(ℝ × ℝ,ℝ)) (hψrange : ∀ clocks, ψ clocks ∈ Icc 0 1)
    (hψsupport : tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε)
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
    let rootValue := physicalSceneOriginalMacroRootValue (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex
    ∃ energy : C(D.coreSpatialCoordinateSpace i × PhysicalPairPalmMark (Fin q),ℝ),
      (∀ p, 0 ≤ energy p) ∧
      (∀ z ∈ (D.haar.continuous.coefficient i).roots,
        ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
          energy (D.coreMacroLabel i z,(clocks,disp)) =
            matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp) ∧
      ∀ (base : ((Fin q → ℝ) × ℝ)) (m : ℕ → ℕ), Tendsto m atTop atTop →
      ∀ (Q : ProbabilityMeasure ((Fin q → ℝ) × CavityLocalScene
          (((Fin q) → ℝ) × ℝ) (((Fin q) → ℝ) × ℝ))),
      Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw base μ ν
        (by simpa only [Fintype.card_fin] using hq)
        (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH (coord (m n))
        (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (s (m n)))
        u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable))
        atTop (𝓝 Q) →
      ∀ (A : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet A →
        A ⊆ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots →
      ∀ B : ℝ, ∀ (U : Set (D.coreSpatialCoordinateSpace i)),
        IsOpen U → palmUnitCube (Fin q) ⊆ U →
      (∫⁻ w, ∫⁻ mark, ENNReal.ofReal (ψ mark.1) *
        min (ENNReal.ofReal B) (ENNReal.ofReal (energy (w,mark)))
        ∂cubePalm (Fin q) (physicalScenePairCampbell ((Q : Measure ((Fin q → ℝ) × CavityLocalScene
          ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).condKernel w))
        ∂(Q : Measure ((Fin q → ℝ) × CavityLocalScene
          ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).fst.restrict A) ≤
      liminf (fun n ↦ volume U *
        ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((s (m n))^2 *
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
          ∂Γ (m n) ξ ∂law (m n)) + ENNReal.ofReal ε * μ H) + ENNReal.ofReal B *
        (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((m n : ℝ)+1) *
          D.originalTaylorGuardMass i R (s (m n)) U (rootValue (tag (m n) root)) root (Γclock (m n) ξ)
          ∂cavityRootMeasure volume (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1)
          ∂law (m n))) atTop := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro q s rootDomain tag law Γ Γclock coord rootValue
  obtain ⟨energy,he0,heq'⟩ := D.exists_original_macro_continuous_shifted_matrix_energy
    hF hcomplete hu ha hinj 0 0 i
  have heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (D.coreMacroLabel i z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp := by
    simpa using heq'
  refine ⟨energy,he0,heq,?_⟩
  intro base m hm Q hweak A hA hAsub B U hU hsub
  let Pn := fun n ↦ originalIIDMaskedMacroPlanLaw base μ ν
    (show 0 < Fintype.card (Fin q) by simpa only [Fintype.card_fin] using hq)
    (cost n) (hcost n) (k n) n H hH (coord n)
    (measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (s n))
    u hu.continuous.measurable
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  have hΓ (n : ℕ) : Measurable (Γ n) := measurable_physicalPlan_sourceRestriction _
    (measurable_originalIIDOptimalPhysicalPlan (cost n) (hcost n) (k n)) H hH
  have hcoord (n : ℕ) : Measurable (coord n) :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ (s n)
  have htag (n : ℕ) : Measurable (tag n) :=
    (continuous_physicalSceneMacroscopicRoot (s n)).measurable
  have hobs (n : ℕ) : Measurable (fun p ↦
      (tag n p.2,physicalSceneRootedLocalScene (Γ n) (Γ n) (coord n) u ((n : ℝ)+1) p)) :=
    ((htag n).comp measurable_snd).prodMk (measurable_physicalSceneRootedLocalScene
      (Γ n) (Γ n) (hΓ n) (hΓ n) (coord n) (hcoord n) u hu.continuous.measurable _)
  have hlaw (n : ℕ) : (Pn n : Measure ((Fin q → ℝ) × CavityLocalScene
        ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))) =
      ((law n).prod (cavityRootMeasure volume (rootDomain n) ((n : ℝ)+1))).map
        (fun p ↦ (tag n p.2,physicalSceneRootedLocalScene (Γ n) (Γ n) (coord n) u ((n : ℝ)+1) p)) :=
          by
    rw [originalIIDMaskedMacroPlanLaw_eq_haarCubeAverageLaw]
    simp only [Fintype.card_fin,haarCubeAverageLaw,haarCubeRootLaw]
    rw [haarRootRadius_mass q hq (by positivity)]
    rfl
  have hmarg (n : ℕ) : (Pn n).map measurable_fst.aemeasurable = η := by
    letI : SFinite (cavityRootMeasure volume (rootDomain n) ((n : ℝ)+1)) := by
      dsimp [cavityRootMeasure]
      infer_instance
    apply ProbabilityMeasure.toMeasure_injective
    change (Pn n : Measure ((Fin q → ℝ) × CavityLocalScene
        ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).map Prod.fst = (η : Measure (Fin q → ℝ))
    rw [hlaw n,Measure.map_map measurable_fst (hobs n)]
    have hcomp : (Prod.fst ∘ (fun p ↦
        (tag n p.2,physicalSceneRootedLocalScene (Γ n) (Γ n) (coord n) u ((n : ℝ)+1) p))) =
        tag n ∘ Prod.snd := rfl
    rw [hcomp,← Measure.map_map (htag n) measurable_snd,Measure.map_snd_prod,
      measure_univ,one_smul]
    exact congrArg (fun p : ProbabilityMeasure (Fin q → ℝ) ↦ (p : Measure (Fin q → ℝ)))
      (physicalSceneMacroscopicRootLaw_canonicalHaarScale q hq n)
  let Ftrunc : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞ := fun p ↦
    ENNReal.ofReal (ψ p.2.1) * min (ENNReal.ofReal B) (ENNReal.ofReal (energy p))
  have hc : Continuous Ftrunc :=
    (ENNReal.continuous_ofReal.comp (ψ.continuous.comp continuous_snd.fst)).ennreal_mul
      (continuous_const.min (ENNReal.continuous_ofReal.comp energy.continuous))
      (fun p ↦ Or.inr (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_left _ _)))
      (fun p ↦ Or.inr ENNReal.ofReal_ne_top)
  have hPalm :=
    lintegral_conditional_cubePalm_restrict_tag_core_le_liminf_original_tagged_sourceWindow
    (fun n ↦ law (m n)) (fun n ↦ Γ (m n)) (fun n ↦ Γ (m n))
    (fun n ↦ hΓ (m n)) (fun n ↦ hΓ (m n)) (fun n ↦ coord (m n)) (fun n ↦ hcoord (m n))
    u hu.continuous.measurable (fun n ↦ (m n : ℝ)+1) (fun n ↦ rootDomain (m n))
    (fun n ↦ tag (m n)) (fun n ↦ htag (m n)) η (fun n ↦ Pn (m n)) Q
    (fun n ↦ hlaw (m n)) hweak (fun n ↦ hmarg (m n)) A hA hU hsub Ftrunc hc.lowerSemicontinuous
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
  have hfinite := D.eventually_originalIID_clock_cutoff_kinetic_energy_le
    hF hcomplete hu ha hinj horder i Eread heq (fun clocks ↦ ENNReal.ofReal (ψ clocks))
      hψle hψzero hq H hH R hR hε cost hcost k
  have hinverse (z : ℚ → M) (hz : z ∈ (D.haar.continuous.coefficient i).roots) :
      rootValue (D.coreMacroLabel i z) = z :=
    physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj _
      ((D.haar.continuous.coefficient i).roots_subset_piece hz)
  have hmacro (c : D.coreSpatialCoordinateSpace i)
      (hc : c ∈ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots) :
      D.coreMacroLabel i (rootValue c) = c := by
    obtain ⟨z,hz,rfl⟩ := hc
    rw [hinverse z hz]
  filter_upwards [hm.eventually hfinite] with n hn
  have hrootae : ∀ᵐ root ∂cavityRootMeasure volume
      (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1), tag (m n) root ∈ A := by
    have hd : MeasurableSet (rootDomain (m n)) := measurableSet_Icc
    exact Measure.ae_smul_measure
      ((ae_restrict_mem (hd.inter (hA.preimage (htag (m n))))).mono (fun root hr ↦ hr.2)) _
  have hequal :
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((m n : ℝ)+1) *
        cavityRootWindowReadout (Γ (m n) ξ) (fun p ↦ coord (m n) p.1)
          (fun p ↦ Ftrunc (tag (m n) root,((u p.1,u p.2),coord (m n) p.2-coord (m n) p.1))) U root
        ∂cavityRootMeasure volume (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1) ∂law (m n)) =
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((m n : ℝ)+1) *
        cavityRootWindowReadout (Γ (m n) ξ) (fun p ↦ coord (m n) p.1)
          (fun p ↦ ENNReal.ofReal (ψ (u p.1,u p.2)) *
            min (ENNReal.ofReal B) (ENNReal.ofReal
            (Eread (rootValue (tag (m n) root),
              ((u p.1,u p.2),coord (m n) p.2-coord (m n) p.1))))) U root
        ∂cavityRootMeasure volume (rootDomain (m n) ∩ tag (m n) ⁻¹' A)
          ((m n : ℝ)+1) ∂law (m n)) := by
    apply lintegral_congr
    intro ξ
    apply lintegral_congr_ae
    filter_upwards [hrootae] with root hr
    simp only [Ftrunc,Eread,hmacro _ (hAsub hr)]
  rw [hequal]
  exact hn B (rootDomain (m n) ∩ tag (m n) ⁻¹' A) U hU.measurableSet
    (fun root ↦ rootValue (tag (m n) root))
end PopulationLocalPressureCore
end OTSelector.Reconstruction
