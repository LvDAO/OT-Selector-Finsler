import OTSelector.Reconstruction.OriginalIIDTaggedProbeFreezing
import OTSelector.Reconstruction.OriginalTaggedPalmEnergyLiminf
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedMacroscopicOriginalCoefficient
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalCanonicalSceneScale
import OTSelector.Reconstruction.OriginalIIDMaskedMacroStationarity
import OTSelector.Reconstruction.OriginalIIDRootCoreEscape
import OTSelector.Reconstruction.OriginalIIDEndpointGuards
import OTSelector.Reconstruction.OriginalIIDOptimalPhysicalMarginalMeans
import OTSelector.MeasureTheory.FixedMarginalRestrictedWeak
import OTSelector.Reconstruction.ActualTaggedMeasuredCoreLsc
import OTSelector.Reconstruction.ActualTaggedMeasuredCorePhysicalReadout

/-! Actual full-plan bounded matrix-energy comparison, retaining explicit
physical cutoff losses before passing through the same joint conditional Palm.
The original fixed clock window is not assumed to carry the full PN clocks. -/
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

/-- Actual original geometry supplies a continuous nonnegative shifted energy
agreeing with the complete root-dependent matrix and physical curve probe on
its genuine retained root/clock carrier. No energy/readout bound is an input. -/
theorem exists_original_continuous_shifted_matrix_energy
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (g : (M × M) →ᵇ ℝ) (t : ℝ) (i : Fin D.haar.continuous.count) :
    ∃ energy : C((ℚ → M) × PhysicalPairPalmMark (Fin (finrank ℝ
        (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)),ℝ),
      (∀ p, 0 ≤ energy p) ∧
      ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t * g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖ := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let K := C.roots ×ˢ C.window.region
  let probe : (ℚ → M) × (ℝ × ℝ) → ℝ := fun p ↦
    g (D.corePoint i (p.1,p.2.1),D.corePoint i (p.1,p.2.2))
  have hp : ContinuousOn probe K := by
    apply g.continuous.comp_continuousOn
    apply ContinuousOn.prodMk
    · exact (D.continuousOn_corePoint i).comp
        (continuous_fst.prodMk continuous_snd.fst).continuousOn
        (fun p hp ↦ ⟨hp.1,(C.window.region_subset hp.2).1⟩)
    · exact (D.continuousOn_corePoint i).comp
        (continuous_fst.prodMk continuous_snd.snd).continuousOn
        (fun p hp ↦ ⟨hp.1,(C.window.region_subset hp.2).2.1⟩)
  have hk : IsClosed K := C.roots_compact.isClosed.prod C.window.isCompact_region.isClosed
  have hn : ∀ p ∈ K, ∀ disp, 0 ≤ matrixQuadratic (C.matrix p.1 p.2) disp := by
    intro p hp disp
    by_cases hd : disp = 0
    · simp [hd]
    · exact (matrixQuadratic_pos (C.coefficient_posDef p.1 hp.1 p.2 hp.2) hd).le
  obtain ⟨energy,henergy0,heq⟩ := exists_continuous_nonnegative_tagged_matrix_shifted_energy
    hk (fun p ↦ C.matrix p.1 p.2) C.coefficient_continuous hn probe hp
    (fun p hp ↦ (Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm _) t
  exact ⟨energy,henergy0,fun z hz clocks hc disp ↦ heq (z,(clocks,disp)) ⟨hz,hc⟩⟩

/-- The original measured macro core admits a continuous nonnegative complete
matrix energy extension. The original inverse is used only on its compact
image, so no ambient continuity of the measurable population labels is added. -/
theorem exists_original_macro_continuous_shifted_matrix_energy
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (g : (M × M) →ᵇ ℝ) (t : ℝ) (i : Fin D.haar.continuous.count) :
    ∃ energy : C(D.coreSpatialCoordinateSpace i × PhysicalPairPalmMark (Fin (finrank ℝ
        (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)),ℝ),
      (∀ p, 0 ≤ energy p) ∧
      ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (D.coreMacroLabel i z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t*g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖ := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let K := D.coreMacroLabel i '' C.roots
  let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
  have hlabel : ContinuousOn (populationSeedRootLabelValue (P C.seedIndex).seed a) C.roots := by
    simpa only [D.haar.intensity_roots i] using (D.haar.intensity i).continuous_label
  have hK : IsCompact K := C.roots_compact.image_of_continuousOn
    ((Module.finBasis ℝ (P C.seedIndex).seed.covector.ker).equivFunL.continuous.comp_continuousOn
      hlabel)
  have hroot : ContinuousOn root K :=
    C.continuousOn_originalMacroRootValue_image hF hcomplete hu ha hinj hlabel
  have hinverse (z : ℚ → M) (hz : z ∈ C.roots) : root (D.coreMacroLabel i z) = z :=
    physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj C.seedIndex
      (C.roots_subset_piece hz)
  obtain ⟨Eroot,hEroot0,hEroot⟩ :=
    D.exists_original_continuous_shifted_matrix_energy hcomplete g t i
  let T :=
    K ×ˢ (univ : Set (PhysicalPairPalmMark (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker))))
  let Henergy : D.coreSpatialCoordinateSpace i ×
      PhysicalPairPalmMark (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)) → ℝ :=
    fun p ↦ Eroot (root p.1,p.2)
  have hT : IsClosed T := hK.isClosed.prod isClosed_univ
  have hH : ContinuousOn Henergy T := Eroot.continuous.comp_continuousOn
    ((hroot.comp continuous_fst.continuousOn (fun p hp ↦ hp.1)).prodMk
      continuous_snd.continuousOn)
  let Hmap : C(T,ℝ) := ⟨fun p ↦ Henergy p,continuousOn_iff_continuous_domRestrict.mp hH⟩
  obtain ⟨E,hE⟩ := Hmap.exists_restrict_eq hT
  let energy : C(D.coreSpatialCoordinateSpace i ×
      PhysicalPairPalmMark (Fin (finrank ℝ (P C.seedIndex).seed.covector.ker)),ℝ) :=
    ⟨fun p ↦ max (E p) 0,E.continuous.max continuous_const⟩
  refine ⟨energy,fun p ↦ le_max_right _ _,?_⟩
  intro z hz clocks hc disp
  have hp : (D.coreMacroLabel i z,(clocks,disp)) ∈ T := ⟨⟨z,hz,rfl⟩,mem_univ _⟩
  have he : E (D.coreMacroLabel i z,(clocks,disp)) =
      Henergy (D.coreMacroLabel i z,(clocks,disp)) :=
    congrArg (fun f : C(T,ℝ) ↦ f ⟨_,hp⟩) hE
  change max (E (D.coreMacroLabel i z,(clocks,disp))) 0 = _
  rw [he]
  change max (Eroot (root (D.coreMacroLabel i z),(clocks,disp))) 0 = _
  rw [hinverse z hz,max_eq_left (hEroot0 _)]
  exact hEroot z hz clocks hc disp

/-- The literal finite Taylor event is measurable in its physical endpoints.
Its root/reference may be fixed arbitrarily; no continuity of a core indicator
or boundary-null property is used. -/
theorem measurableSet_originalRootedTaylorWindow
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) (R scale : ℝ)
    {U : Set (D.coreSpatialCoordinateSpace i)} (hU : MeasurableSet U)
    (z : ℚ → M) (root : D.coreSpatialCoordinateSpace i) :
    MeasurableSet (D.originalRootedTaylorWindow i R scale U z root) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ scale
  have hum : Measurable u := hu.continuous.measurable
  have hreg := hF.measurableSet_potentialRegularDomain hcomplete u
  have hconst (p : Prop) : MeasurableSet {x : M × M | p} := by by_cases hp : p <;> simp [hp]
  change MeasurableSet {p : M × M | z ∈ C.roots ∧
    root = scale • D.coreMacroLabel i z ∧ a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧
    p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u ∧
    (u p.1,u p.2) ∈ C.window.region ∧ ‖coord p.1-root‖ ≤ R ∧
    ‖coord p.2-root‖ ≤ R ∧ coord p.1-root ∈ U}
  have hax : MeasurableSet {p : M × M | a p.1 ∈ C.roots} :=
    C.roots_compact.isClosed.measurableSet.preimage (ha.comp measurable_fst)
  have hay : MeasurableSet {p : M × M | a p.2 ∈ C.roots} :=
    C.roots_compact.isClosed.measurableSet.preimage (ha.comp measurable_snd)
  have hrx := hreg.preimage (measurable_fst : Measurable (Prod.fst : M × M → M))
  have hry := hreg.preimage (measurable_snd : Measurable (Prod.snd : M × M → M))
  have hcl : MeasurableSet {p : M × M | (u p.1,u p.2) ∈ C.window.region} :=
    C.window.isCompact_region.measurableSet.preimage
    ((hum.comp measurable_fst).prodMk (hum.comp measurable_snd))
  have hnx : MeasurableSet {p : M × M | ‖coord p.1-root‖ ≤ R} :=
    measurableSet_Iic.preimage ((hcoord.comp measurable_fst).sub measurable_const).norm
  have hny : MeasurableSet {p : M × M | ‖coord p.2-root‖ ≤ R} :=
    measurableSet_Iic.preimage ((hcoord.comp measurable_snd).sub measurable_const).norm
  have hsrc : MeasurableSet {p : M × M | coord p.1-root ∈ U} :=
    hU.preimage ((hcoord.comp measurable_fst).sub measurable_const)
  exact (hconst _).inter ((hconst _).inter
    (hax.inter (hay.inter (hrx.inter (hry.inter (hcl.inter (hnx.inter (hny.inter hsrc))))))))

/-- Exact full-plan guard remainder in one actual translated source window.
It is a physical readout of the same Γ, not a replacement retained scene. -/
def originalTaylorGuardMass
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (R scale : ℝ)
    (U : Set (D.coreSpatialCoordinateSpace i)) (z : ℚ → M)
    (root : D.coreSpatialCoordinateSpace i) (Γ : Measure (M × M)) : ℝ≥0∞ :=
  Γ ({p | physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
    (D.haar.continuous.coefficient i).seedIndex scale p.1-root ∈ U} \
      D.originalRootedTaylorWindow i R scale U z root)

/-- On its genuine root/core relation, the full-plan loss splits into endpoint
core/regularity loss, the actual clock-window complement, and the two spatial
cutoffs. In particular the fixed-D clock complement is retained explicitly. -/
theorem originalTaylorGuardMass_le_endpoint_clock_spatial
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (i : Fin D.haar.continuous.count) (R scale : ℝ)
    (U : Set (D.coreSpatialCoordinateSpace i)) (z : ℚ → M)
    (root : D.coreSpatialCoordinateSpace i) (Γ : Measure (M × M))
    (hz : z ∈ (D.haar.continuous.coefficient i).roots)
    (hroot : root = scale • D.coreMacroLabel i z) :
    let C := D.haar.continuous.coefficient i
    let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a) C.seedIndex scale
    D.originalTaylorGuardMass i R scale U z root Γ ≤
      Γ ({p | coord p.1-root ∈ U} ∩ {p | ¬(a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧
        p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u)}) +
      Γ ({p | coord p.1-root ∈ U} ∩ {p | (u p.1,u p.2) ∉ C.window.region}) +
      Γ ({p | coord p.1-root ∈ U} ∩ {p | ¬(‖coord p.1-root‖ ≤ R ∧ ‖coord p.2-root‖ ≤ R)}) := by
  classical
  intro C coord
  let W : Set (M × M) := {p | coord p.1-root ∈ U}
  let badEndpoint : Set (M × M) := {p | ¬(a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧
    p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u)}
  let badClock : Set (M × M) := {p | (u p.1,u p.2) ∉ C.window.region}
  let badSpatial : Set (M × M) := {p | ¬(‖coord p.1-root‖ ≤ R ∧ ‖coord p.2-root‖ ≤ R)}
  have hsub : W \ D.originalRootedTaylorWindow i R scale U z root ⊆
      (W ∩ badEndpoint) ∪ (W ∩ badClock) ∪ (W ∩ badSpatial) := by
    intro p hp
    by_cases he : a p.1 ∈ C.roots ∧ a p.2 ∈ C.roots ∧
        p.1 ∈ F.potentialRegularDomain u ∧ p.2 ∈ F.potentialRegularDomain u
    · by_cases hc : (u p.1,u p.2) ∈ C.window.region
      · apply Or.inr
        refine ⟨hp.1,?_⟩
        intro hsp
        exact hp.2 ⟨hz,hroot,he.1,he.2.1,he.2.2.1,he.2.2.2,hc,hsp.1,hsp.2,hp.1⟩
      · exact Or.inl (Or.inr ⟨hp.1,hc⟩)
    · exact Or.inl (Or.inl ⟨hp.1,he⟩)
  exact (measure_mono hsub).trans ((measure_union_le _ _).trans
    (add_le_add_left (measure_union_le _ _) _))

/-- A bounded truncation of the SAME full matrix energy is compared with the
actual physical signed tilt on the full original plan. Every missing Taylor
guard is charged explicitly by B times its genuine mass. -/
theorem exists_uniform_original_full_plan_truncated_energy_le
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x=a y ∧ u x≤u y) ↔ u y-u x=dist x y)
    (i : Fin D.haar.continuous.count) (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (energy : (ℚ → M) × PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) → ℝ)
    (heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t * g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε) :
    ∃ threshold > 0, ∀ scale : ℝ, threshold ≤ scale →
      ∀ (Γ : Measure (M × M)) [IsFiniteMeasure Γ], ∀ (B : ℝ),
      ∀ (rootDomain U : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet U →
      ∀ N : ℝ, 0 < N → ∀ ref : D.coreSpatialCoordinateSpace i → (ℚ → M),
      let coord := physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex scale
      (∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1))))) U root
        ∂cavityRootMeasure volume rootDomain N) ≤
      volume U * ((∫⁻ p, ENNReal.ofReal (scale ^ 2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1) + t*g p + |t| * ‖g‖) ∂Γ) +
          ENNReal.ofReal ε * Γ univ) + ENNReal.ofReal B *
      (∫⁻ root, ENNReal.ofReal N * D.originalTaylorGuardMass i R scale U (ref root) root Γ
        ∂cavityRootMeasure volume rootDomain N) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  obtain ⟨threshold,hthreshold,herror⟩ :=
    D.exists_uniform_original_rooted_tilted_error hF hcomplete hu ha hinj horder i g t R hR hε
  refine ⟨threshold,hthreshold,?_⟩
  intro scale hs Γ _ B rootDomain U hU N hN ref coord
  let base : M × M → ℝ := fun p ↦ scale ^ 2 *
    ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖
  have hb : Measurable base := (((F.measurable_distance_slack hu).const_mul (scale^2)).add
    (g.continuous.measurable.const_mul t)).add_const _
  have hb0 (p : M × M) : 0 ≤ base p := by
    have hl := hu.le_add_mul p.2 p.1
    simp only [NNReal.coe_one,one_mul,dist_comm p.2 p.1] at hl
    have hslack : 0 ≤ (F.lengthEDist p.1 p.2).toReal-u p.2+u p.1 := by
      change 0 ≤ dist p.1 p.2-u p.2+u p.1; linarith
    have hg : |t*g p| ≤ |t| * ‖g‖ := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((Real.norm_eq_abs _).symm ▸ g.norm_coe_le_norm p) (abs_nonneg t)
    dsimp only [base]
    nlinarith [mul_nonneg (sq_nonneg scale) hslack,(abs_le.mp hg).1]
  let upper : M × M → ℝ≥0∞ := fun p ↦ ENNReal.ofReal (base p+ε)
  have hupper : Measurable upper := (hb.add_const ε).ennreal_ofReal
  have hcoord : Measurable coord :=
    measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj _ scale
  have hread : Measurable (fun root ↦ cavityRootWindowReadout Γ (fun p ↦ coord p.1) upper U root) :=
    by
    have hm : Measurable (fun p : D.coreSpatialCoordinateSpace i × (M × M) ↦
        U.indicator (fun _ ↦ upper p.2) (coord p.2.1-p.1)) := by
      change Measurable (fun p : D.coreSpatialCoordinateSpace i × (M × M) ↦
        if coord p.2.1-p.1 ∈ U then upper p.2 else 0)
      exact Measurable.ite (hU.preimage ((hcoord.comp measurable_snd.fst).sub measurable_fst))
        (hupper.comp measurable_snd) measurable_const
    exact hm.lintegral_prod_right'
  have hpoint (root : D.coreSpatialCoordinateSpace i) :
      cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ min (ENNReal.ofReal B) (ENNReal.ofReal
          (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1))))) U root ≤
      cavityRootWindowReadout Γ (fun p ↦ coord p.1) upper U root +
        ENNReal.ofReal B * D.originalTaylorGuardMass i R scale U (ref root) root Γ := by
    let bad := {p : M × M | coord p.1-root ∈ U} \
      D.originalRootedTaylorWindow i R scale U (ref root) root
    have hbad : MeasurableSet bad :=
      (hU.preimage ((hcoord.comp measurable_fst).sub measurable_const)).diff
        (D.measurableSet_originalRootedTaylorWindow hF hcomplete hu ha hinj i R scale hU _ _)
    have hm : Measurable (fun p : M × M ↦ U.indicator (fun _ ↦ upper p) (coord p.1-root)) := by
      change Measurable (fun p : M × M ↦ if coord p.1-root ∈ U then upper p else 0)
      exact Measurable.ite (hU.preimage ((hcoord.comp measurable_fst).sub measurable_const))
        hupper measurable_const
    change (∫⁻ p, U.indicator (fun _ ↦ min (ENNReal.ofReal B) (ENNReal.ofReal
        (energy (ref root,((u p.1,u p.2),coord p.2-coord p.1))))) (coord p.1-root) ∂Γ) ≤ _
    calc
      _ ≤ ∫⁻ p, U.indicator (fun _ ↦ upper p) (coord p.1-root) +
          bad.indicator (fun _ ↦ ENNReal.ofReal B) p ∂Γ := by
        apply lintegral_mono
        intro p
        by_cases hsource : coord p.1-root ∈ U
        · simp only [indicator_of_mem hsource]
          by_cases hp : p ∈ D.originalRootedTaylorWindow i R scale U (ref root) root
          · have he := herror scale hs U (ref root) root p hp
            have heq' := heq (ref root) hp.1 (u p.1,u p.2) hp.2.2.2.2.2.2.1 (coord p.2-coord p.1)
            have hE : energy (ref root,((u p.1,u p.2),coord p.2-coord p.1)) ≤ base p+ε := by
              rw [heq']
              change D.originalRootedTaylorKinetic i scale (ref root) p +
                t * D.originalRootedFrozenProbe i g (ref root) p + |t| * ‖g‖ ≤ base p+ε
              dsimp only [base]
              linarith [(abs_le.mp he).2]
            exact (min_le_right _ _).trans
              ((ENNReal.ofReal_le_ofReal hE).trans (le_add_right le_rfl))
          · have hpbad : p ∈ bad := ⟨hsource,hp⟩
            rw [indicator_of_mem hpbad]
            exact (min_le_left _ _).trans (le_add_left le_rfl)
        · simp only [indicator_of_notMem hsource]
          exact bot_le
      _ = _ := by rw [lintegral_add_left hm,lintegral_indicator_const hbad]; rfl
  calc
    _ ≤ ∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1) upper U root +
        ENNReal.ofReal B *
          (ENNReal.ofReal N * D.originalTaylorGuardMass i R scale U (ref root) root Γ)
        ∂cavityRootMeasure volume rootDomain N := by
      apply lintegral_mono
      intro root
      simpa only [mul_add,mul_left_comm] using
        mul_le_mul_of_nonneg_left (hpoint root) (bot_le : 0 ≤ ENNReal.ofReal N)
    _ = (∫⁻ root, ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1) upper U root
        ∂cavityRootMeasure volume rootDomain N) + ENNReal.ofReal B *
      (∫⁻ root, ENNReal.ofReal N * D.originalTaylorGuardMass i R scale U (ref root) root Γ
        ∂cavityRootMeasure volume rootDomain N) := by
      rw [lintegral_add_left (hread.const_mul _)]
      congr 1
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
      apply add_le_add_left
      have havg := lintegral_cavityRoot_scaled_window_le volume Γ _ (hcoord.comp measurable_fst)
        upper hupper U hU rootDomain N hN
      refine havg.trans_eq ?_
      congr 1
      have hup (p : M × M) : upper p = ENNReal.ofReal (base p)+ENNReal.ofReal ε :=
        ENNReal.ofReal_add (hb0 p) hε.le
      simp_rw [hup]
      rw [lintegral_add_left hb.ennreal_ofReal,lintegral_const]

/-- The full original two-product iid optimizer, restricted by the original
physical source seed H, satisfies the bounded comparison at the canonical
N=n+1 rooting scale. The sharp Taylor loss is ε·μ(H), before any atlas sum. -/
theorem eventually_originalIID_canonical_full_truncated_energy_le
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
    (i : Fin D.haar.continuous.count) (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (energy : (ℚ → M) × PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)) → ℝ)
    (heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
            t * g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (H : Set M) (hH : MeasurableSet H)
    (R : ℝ) (hR : 0 ≤ R) {ε : ℝ} (hε : 0 < ε)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) :
    let q := finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker
    let s := fun n : ℕ ↦ 2 * haarRootRadius q ((n : ℝ)+1)
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ :=
      fun n ξ ↦ (originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (s n)
    ∀ᶠ n in atTop, ∀ B : ℝ,
      ∀ (rootDomain U : Set (D.coreSpatialCoordinateSpace i)), MeasurableSet U →
      ∀ ref : D.coreSpatialCoordinateSpace i → (ℚ → M),
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
        cavityRootWindowReadout (Γ n ξ) (fun p ↦ coord n p.1)
          (fun p ↦ min (ENNReal.ofReal B) (ENNReal.ofReal
            (energy (ref root,((u p.1,u p.2),coord n p.2-coord n p.1))))) U root
        ∂cavityRootMeasure volume rootDomain ((n : ℝ)+1) ∂law n) ≤
      volume U * ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((s n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖) ∂Γ n ξ ∂law n) +
          ENNReal.ofReal ε * μ H) + ENNReal.ofReal B *
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
        D.originalTaylorGuardMass i R (s n) U (ref root) root (Γ n ξ)
        ∂cavityRootMeasure volume rootDomain ((n : ℝ)+1) ∂law n) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro q s law Γ coord
  obtain ⟨threshold,hthreshold,hbound⟩ :=
    D.exists_uniform_original_full_plan_truncated_energy_le hF hcomplete hu ha hinj horder
      i g t energy heq R hR hε
  have hNlarge : Tendsto (fun n : ℕ ↦ (n : ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hslarge : Tendsto s atTop atTop :=
    (tendsto_haarRootRadius q hq hNlarge).const_mul_atTop (by norm_num)
  filter_upwards [hslarge.eventually (eventually_ge_atTop threshold)] with n hn
  intro B rootDomain U hU ref
  let Ephys : ((Fin (n+1) → M) × (Fin (n+1) → M)) → ℝ≥0∞ := fun ξ ↦
    ∫⁻ p, ENNReal.ofReal ((s n)^2 *
      ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖) ∂Γ n ξ
  have hΓ : Measurable (Γ n) := measurable_physicalPlan_sourceRestriction _
    (measurable_originalIIDOptimalPhysicalPlan (cost n) (hcost n) (k n)) H hH
  have hE : Measurable Ephys := (Measure.measurable_lintegral
    (((((F.measurable_distance_slack hu).const_mul ((s n)^2)).add
      (g.continuous.measurable.const_mul t)).add_const _).ennreal_ofReal)).comp hΓ
  have hm : Measurable (fun ξ ↦ Γ n ξ univ) := (Measure.measurable_coe MeasurableSet.univ).comp hΓ
  have hmean : (∫⁻ ξ, Γ n ξ univ ∂law n) = μ H := by
    have hprod : H ×ˢ (univ : Set M) = Prod.fst ⁻¹' H := by ext p; simp
    simpa only [Γ,Measure.restrict_apply_univ,hprod] using
      lintegral_originalIIDOptimalPhysicalPlan_source_event μ ν (cost n) (k n) hH
  calc
    _ ≤ ∫⁻ ξ, volume U * (Ephys ξ + ENNReal.ofReal ε * Γ n ξ univ) +
        ENNReal.ofReal B * (∫⁻ root, ENNReal.ofReal ((n : ℝ)+1) *
          D.originalTaylorGuardMass i R (s n) U (ref root) root (Γ n ξ)
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

section CanonicalMacro
local instance actualFullTaggedPlanPolish (ι : Type*) [Fintype ι] : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance actualFullTaggedPlanNonempty (ι : Type*) [Fintype ι] : Nonempty
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) := ⟨⟨0,inferInstance⟩⟩

/-- The same canonical masked macro law supplies its own bounded matrix Palm
lower passage. The actual measured core may have positive boundary mass.
No root-reference map, desired Palm energy bound, or clock-support property
is an extra input. The sharp Taylor loss is ε·μ(H); every unremoved guard is
charged by its literal mass in the unchanged physical optimizer. -/
theorem exists_originalIID_masked_macro_matrix_energy_liminf
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
    (i : Fin D.haar.continuous.count) (g : (M × M) →ᵇ ℝ) (t : ℝ)
    (hq : 0 < finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)
    (H : Set M) (hH : MeasurableSet H)
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
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex (s n)
    let rootValue := physicalSceneOriginalMacroRootValue (P := P) (a := a)
      (D.haar.continuous.coefficient i).seedIndex
    ∃ energy : C(D.coreSpatialCoordinateSpace i × PhysicalPairPalmMark (Fin q),ℝ),
      (∀ p, 0 ≤ energy p) ∧
      (∀ z ∈ (D.haar.continuous.coefficient i).roots,
        ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
          energy (D.coreMacroLabel i z,(clocks,disp)) =
            matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp +
              t*g (D.corePoint i (z,clocks.1),D.corePoint i (z,clocks.2)) + |t| * ‖g‖) ∧
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
      (∫⁻ w, ∫⁻ mark, min (ENNReal.ofReal B) (ENNReal.ofReal (energy (w,mark)))
        ∂cubePalm (Fin q) (physicalScenePairCampbell ((Q : Measure ((Fin q → ℝ) × CavityLocalScene
          ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).condKernel w))
        ∂(Q : Measure ((Fin q → ℝ) × CavityLocalScene
          ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).fst.restrict A) ≤
      liminf (fun n ↦ volume U *
        ((∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((s (m n))^2 *
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+t*g p+|t| * ‖g‖)
          ∂Γ (m n) ξ ∂law (m n)) + ENNReal.ofReal ε * μ H) + ENNReal.ofReal B *
        (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((m n : ℝ)+1) *
          D.originalTaylorGuardMass i R (s (m n)) U (rootValue (tag (m n) root)) root (Γ (m n) ξ)
          ∂cavityRootMeasure volume (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1)
          ∂law (m n))) atTop := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro q s rootDomain tag law Γ coord rootValue
  obtain ⟨energy,he0,heq⟩ := D.exists_original_macro_continuous_shifted_matrix_energy
    hF hcomplete hu ha hinj g t i
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
    min (ENNReal.ofReal B) (ENNReal.ofReal (energy p))
  have hc : Continuous Ftrunc :=
    continuous_const.min (ENNReal.continuous_ofReal.comp energy.continuous)
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
  have hfinite := D.eventually_originalIID_canonical_full_truncated_energy_le
    hF hcomplete hu ha hinj horder i g t Eread heq hq H hH R hR hε cost hcost k
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
          (fun p ↦ min (ENNReal.ofReal B) (ENNReal.ofReal
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
end CanonicalMacro

end PopulationLocalPressureCore
end OTSelector.Reconstruction
