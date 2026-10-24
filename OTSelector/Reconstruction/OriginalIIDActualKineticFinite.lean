import OTSelector.Reconstruction.OriginalIIDActualKineticClosure
import OTSelector.Reconstruction.OriginalIIDUnitDensityValueReadout

/-! Full-clock sign control of the same original raw kinetic observable.
Actual original conditional moment witnesses, full raw Palm clock marginals
and actual forward clocks give positivity without a retained-window support
assumption. The subsequent finite-energy passage keeps clipping height fixed
until original accuracy losses have been removed. -/
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

/-- Natural clipping heights exhaust one fixed nonnegative observable. The
budget here is already uniform in the clipping height; an error B*delta does
not satisfy this hypothesis before the original precision limit is taken. -/
theorem lintegral_le_of_uniform_natural_clipped_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → ℝ≥0∞) (hf : AEMeasurable f μ) (C : ℝ≥0∞)
    (hbound : ∀ n : ℕ, (∫⁻ x, min (n : ℝ≥0∞) (f x) ∂μ) ≤ C) :
    (∫⁻ x, f x ∂μ) ≤ C := by
  have hsup (x : Ω) : (⨆ n : ℕ, min (n : ℝ≥0∞) (f x)) = f x := by
    rw [← iSup_inf_eq,ENNReal.iSup_natCast,top_inf_eq]
  calc
    _ = ∫⁻ x, ⨆ n : ℕ, min (n : ℝ≥0∞) (f x) ∂μ :=
      lintegral_congr (fun x ↦ (hsup x).symm)
    _ = ⨆ n : ℕ, ∫⁻ x, min (n : ℝ≥0∞) (f x) ∂μ := by
      apply lintegral_iSup' (fun _ ↦ aemeasurable_const.min hf)
      exact Eventually.of_forall (fun x i j hij ↦ min_le_min (by exact_mod_cast hij) le_rfl)
    _ ≤ _ := iSup_le hbound

/-- Once actual fixed-height precision refinement has produced ONE finite
budget for every natural height on the SAME kernel, monotone convergence and
the actual sign give almost-everywhere real kinetic integrability. -/
theorem ae_integrable_of_uniform_clipped_kernel_bounds
    {W X : Type*} [MeasurableSpace W] [MeasurableSpace X]
    (μ : Measure W) [SFinite μ] (κ : Kernel W X) [IsSFiniteKernel κ]
    (energy : W × X → ℝ) (henergy : Measurable energy)
    (hnonneg : ∀ᵐ w ∂μ, ∀ᵐ x ∂κ w, 0 ≤ energy (w,x))
    (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hbound : ∀ n : ℕ, (∫⁻ w, ∫⁻ x, min (n : ℝ≥0∞)
      (ENNReal.ofReal (energy (w,x))) ∂κ w ∂μ) ≤ C) :
    ∀ᵐ w ∂μ, Integrable (fun x ↦ energy (w,x)) (κ w) := by
  have hjoint : (∫⁻ p, ENNReal.ofReal (energy p) ∂μ ⊗ₘ κ) ≤ C := by
    apply lintegral_le_of_uniform_natural_clipped_bounds (μ ⊗ₘ κ)
      (fun p ↦ ENNReal.ofReal (energy p)) henergy.ennreal_ofReal.aemeasurable C
    intro n
    rw [Measure.lintegral_compProd (measurable_const.min henergy.ennreal_ofReal)]
    exact hbound n
  have hglobal : (∫⁻ w, ∫⁻ x, ENNReal.ofReal (energy (w,x)) ∂κ w ∂μ) ≠ ⊤ := by
    rw [← Measure.lintegral_compProd henergy.ennreal_ofReal]
    exact ne_top_of_le_ne_top hC hjoint
  have hfinite := ae_lt_top henergy.ennreal_ofReal.lintegral_kernel_prod_right' hglobal
  filter_upwards [hfinite,hnonneg] with w hw hn
  exact (lintegral_ofReal_ne_top_iff_integrable
    (henergy.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable hn).mp hw.ne

/-- Translating a genuine rooted frame changes the root by the same vector;
clocks and the whole target-minus-source displacement remain literal. -/
theorem cavityRootWindowReadout_translate_clock_energy
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (ρ : Measure Ω) (source target : Ω → (ι → ℝ)) (clock : Ω → ℝ × ℝ)
    (F : (ℝ × ℝ) × (ι → ℝ) → ℝ≥0∞)
    (offset root : ι → ℝ) (U : Set (ι → ℝ)) :
    cavityRootWindowReadout ρ (fun x ↦ source x-offset)
      (fun x ↦ F (clock x,(target x-offset)-(source x-offset))) U root =
      cavityRootWindowReadout ρ source (fun x ↦ F (clock x,target x-source x)) U
        (root+offset) := by
  unfold cavityRootWindowReadout
  apply lintegral_congr
  intro x
  have hsource : (source x-offset)-root = source x-(root+offset) := by abel
  have hdisp : (target x-offset)-(source x-offset) = target x-source x := by abel
  simp only [hsource,hdisp]

local instance kineticFinitePlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure ((((Fin q) → ℝ) × ℝ) × (((Fin q) → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace
local instance kineticFinitePlanNonempty (q : ℕ) : Nonempty
    (LocalFiniteMeasure ((((Fin q) → ℝ) × ℝ) × (((Fin q) → ℝ) × ℝ))) :=
  ⟨⟨0,inferInstance⟩⟩

/-- Any actual fixed masked iid macro weak law supplies its own local tagged
Palm lower passage. Coordinates may be an original translated frame; all
sample/root laws and the integer normalization are derived internally. -/
theorem lintegral_originalIID_conditional_palm_le_liminf_sourceWindow
    {M : Type*} [MeasurableSpace M] {q : ℕ}
    (base : (Fin q → ℝ) × ℝ) (μ ν : Measure M)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hq : 0 < q)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (Fin q → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u) (m : ℕ → ℕ)
    (Q : ProbabilityMeasure ((Fin q → ℝ) × CavityLocalScene
      ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ)))
    (hweak : Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw base μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (coord (m n)) (hcoord (m n)) u hu) atTop (𝓝 Q))
    (A : Set (Fin q → ℝ)) (hA : MeasurableSet A)
    (U : Set (Fin q → ℝ)) (hU : IsOpen U) (hsub : palmUnitCube (Fin q) ⊆ U)
    (F : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) → ℝ≥0∞)
    (hF : LowerSemicontinuous F) :
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := fun n ξ ↦
      (originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)
    let rootDomain := physicalSceneCanonicalHaarDomain q
    let tag := fun n ↦ physicalSceneMacroscopicRoot (physicalSceneCanonicalHaarScale q n)
    (∫⁻ w, ∫⁻ mark, F (w,mark)
      ∂cubePalm (Fin q) (physicalScenePairCampbell ((Q : Measure ((Fin q → ℝ) ×
        CavityLocalScene ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).condKernel w))
      ∂(Q : Measure ((Fin q → ℝ) × CavityLocalScene
        ((Fin q → ℝ) × ℝ) ((Fin q → ℝ) × ℝ))).fst.restrict A) ≤
      liminf (fun n ↦ ∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((m n : ℝ)+1) *
        cavityRootWindowReadout (Γ (m n) ξ) (fun p ↦ coord (m n) p.1)
          (fun p ↦ F (tag (m n) root,((u p.1,u p.2),coord (m n) p.2-coord (m n) p.1))) U root
        ∂cavityRootMeasure volume (rootDomain (m n) ∩ tag (m n) ⁻¹' A) ((m n : ℝ)+1)
        ∂law (m n)) atTop := by
  intro law Γ rootDomain tag
  let s := physicalSceneCanonicalHaarScale q
  let Pn := fun n ↦ originalIIDMaskedMacroPlanLaw base μ ν
    (show 0 < Fintype.card (Fin q) by simpa only [Fintype.card_fin] using hq)
    (cost n) (hcost n) (k n) n H hH (coord n)
    (hcoord n) u hu
  let η := physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier q)
    (physicalScene_centered_unitCube_mass (Fin q))
  have hΓ (n : ℕ) : Measurable (Γ n) := measurable_physicalPlan_sourceRestriction _
    (measurable_originalIIDOptimalPhysicalPlan (cost n) (hcost n) (k n)) H hH
  have htag (n : ℕ) : Measurable (tag n) :=
    (continuous_physicalSceneMacroscopicRoot (s n)).measurable
  have hobs (n : ℕ) : Measurable (fun p ↦
      (tag n p.2,physicalSceneRootedLocalScene (Γ n) (Γ n) (coord n) u ((n : ℝ)+1) p)) :=
    ((htag n).comp measurable_snd).prodMk (measurable_physicalSceneRootedLocalScene
      (Γ n) (Γ n) (hΓ n) (hΓ n) (coord n) (hcoord n) u hu _)
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
  exact lintegral_conditional_cubePalm_restrict_tag_core_le_liminf_original_tagged_sourceWindow
    (fun n ↦ law (m n)) (fun n ↦ Γ (m n)) (fun n ↦ Γ (m n))
    (fun n ↦ hΓ (m n)) (fun n ↦ hΓ (m n)) (fun n ↦ coord (m n)) (fun n ↦ hcoord (m n))
    u hu (fun n ↦ (m n : ℝ)+1) (fun n ↦ rootDomain (m n))
    (fun n ↦ tag (m n)) (fun n ↦ htag (m n)) η (fun n ↦ Pn (m n)) Q
    (fun n ↦ hlaw (m n)) hweak (fun n ↦ hmarg (m n)) A hA hU hsub F hF

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}

/-- Complete original clock support and genuine strict forward clocks make
the original full inverse-compliance quadratic nonnegative on the SAME raw
mark measure. No retained scalar interval or cutoff is imposed on that measure. -/
theorem OriginalSeedConditionalMoments.ae_raw_kinetic_nonneg_of_clock_marginals
    {S : F.CalibratedLevelSeedPatch u} {w : S.covector.ker}
    {α β : Measure ℝ} (D : OriginalSeedConditionalMoments S w α β)
    (hF : F.IsSmoothStronglyConvex) (hw : w ∈ S.labels)
    (ρ : Measure (PhysicalPairPalmMark (Fin (finrank ℝ S.covector.ker)))) (θ : ℝ)
    (hsource : ρ.map (fun m ↦ m.1.1) = ENNReal.ofReal θ • α)
    (htarget : ρ.map (fun m ↦ m.1.2) = ENNReal.ofReal θ • β)
    (hforward : ∀ᵐ m ∂ρ, m.1.1 < m.1.2) :
    ∀ᵐ m ∂ρ, 0 ≤ matrixQuadratic (originalSeedPairCoefficient S w m.1) m.2 := by
  have hs : ∀ᵐ m ∂ρ, m.1.1-(S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ae_of_ae_map measurable_fst.fst.aemeasurable (by
      rw [hsource]
      exact Measure.ae_smul_measure D.support.source.ae_open _)
  have ht : ∀ᵐ m ∂ρ, m.1.2-(S.level : ℝ) ∈ Ioo D.lo D.hi :=
    ae_of_ae_map measurable_fst.snd.aemeasurable (by
      rw [htarget]
      exact Measure.ae_smul_measure D.support.target.ae_open _)
  filter_upwards [hs,ht,hforward] with m hms hmt hmf
  have hp := (D.pair_compliance_posDef hF hw hms hmt hmf).2
  by_cases hd : m.2 = 0
  · simp [hd]
  · exact (matrixQuadratic_pos hp hd).le

variable [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The actual population core supplies the full original moment witness
internally, and hence nonnegativity of its SAME fixed raw macro kernel under
the true raw Palm clock marginals. The full mark measure is unchanged. -/
theorem PopulationLocalPressureCore.ae_fixed_raw_macro_kinetic_nonneg
    [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {z : ℚ → M}
    (hz : z ∈ (D.haar.continuous.coefficient i).roots)
    (ρ : Measure (PhysicalPairPalmMark (Fin (finrank ℝ
      (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker)))) (θ : ℝ)
    (hsource : ρ.map (fun m ↦ m.1.1) = ENNReal.ofReal θ • condDistrib u a μ z)
    (htarget : ρ.map (fun m ↦ m.1.2) = ENNReal.ofReal θ • condDistrib u a ν z)
    (hforward : ∀ᵐ m ∂ρ, m.1.1 < m.1.2) :
    ∀ᵐ m ∂ρ, 0 ≤ matrixQuadratic
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (D.coreMacroLabel i z,m.1)) m.2 := by
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : BorelSpace (ℚ → M) := inferInstance
  let C := D.haar.continuous.coefficient i
  have hroot : z ∈ D.haar.continuous.population.roots := by
    rw [← D.haar.continuous.union_eq]
    exact mem_iUnion.mpr ⟨i,hz⟩
  have hpiece := C.roots_subset_piece hz
  obtain ⟨mom⟩ := ((D.haar.continuous.population.good z hroot).2 C.seedIndex hpiece).1
  have hnonneg := mom.ae_raw_kinetic_nonneg_of_clock_marginals hF
    (populationSeedPieceLabel P a κ lambda C.seedIndex ⟨z,hpiece⟩).property
    ρ θ hsource htarget hforward
  filter_upwards [hnonneg] with m hm
  rw [← D.original_matrix_eq_fixed_macro_coefficient hF hcomplete hu ha hinj i hz m.1]
  change 0 ≤ matrixQuadratic (populationSeedRootCoefficient (P C.seedIndex).seed a
    (Module.finBasis ℝ (P C.seedIndex).seed.covector.ker) (z,m.1)) m.2
  rw [populationSeedRootCoefficient_eq_pieceCoefficient P a κ lambda
    hF hcomplete hu ha hinj C.seedIndex hpiece m.1]
  exact hm

/-- The true finite Taylor comparison in any original translated macro frame
uses the same physical optimizer and raw kernel. Only the literal root is
translated; no new weak candidate, mask, clock or displacement is selected. -/
theorem PopulationLocalPressureCore.exists_uniform_original_clock_cutoff_translated_local_readout_le
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
          ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+ε)) U (root+scale • center) +
      ENNReal.ofReal B * D.originalTaylorGuardMass i R scale U z (root+scale • center) Γclock := by
  obtain ⟨threshold,hthreshold,hbound⟩ :=
    D.exists_uniform_original_clock_cutoff_local_readout_le hF hcomplete hu ha hinj horder
      i energy heq ψ hψ hψzero R hR hε
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
theorem PopulationLocalPressureCore.exists_translated_fixed_candidate_clock_cutoff_local_energy_liminf
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
            matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp) ∧
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
            ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+ε)) U
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
    hF hcomplete hu ha hinj 0 0 i
  have heq : ∀ z ∈ (D.haar.continuous.coefficient i).roots,
      ∀ clocks ∈ (D.haar.continuous.coefficient i).window.region, ∀ disp,
        energy (D.coreMacroLabel i z,(clocks,disp)) =
          matrixQuadratic ((D.haar.continuous.coefficient i).matrix z clocks) disp := by
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
    D.exists_uniform_original_clock_cutoff_translated_local_readout_le
      hF hcomplete hu ha hinj horder i Eread heq (fun clocks ↦ ENNReal.ofReal (ψ clocks))
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

end OTSelector.Reconstruction
