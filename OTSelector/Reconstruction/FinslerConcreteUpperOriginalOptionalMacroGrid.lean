import OTSelector.Reconstruction.FinslerConcreteUpperActualMacrobox
import OTSelector.Reconstruction.FinslerConcreteUpperClassGridExpectation
import OTSelector.Reconstruction.FinslerPopulationTypedIIDFacts
import LeanPool.QuasiBorelSpaces.MeasureTheory.Option

/-! Actual unclamped original macrobox values obey the legal parent-grid repair bound. -/
open Set Function MeasureTheory ProbabilityTheory Filter Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal NNReal Matrix.Norms.Operator BigOperators Classical BoundedContinuousFunction
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
local instance optionalMacroGridUnitSpace : MeasurableSpace (Option Unit) := ⊤
local instance optionalMacroGridUnitSingleton : MeasurableSingletonClass (Option Unit) := ⟨fun _ ↦ trivial⟩

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

/-- The compact original coefficient roots produce a fixed integer macrobox.
The literal N-point nullable paired-class experiment then pays its actual
parent-scale repair. The true physical kernel is used without any clamp. -/
theorem PopulationLocalPressureCore.exists_original_optional_clockClass_grid_expectation
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (i : Fin D.haar.continuous.count) {I : Set ℝ} {gap : ℝ}
    (Q : FiniteScalarBins I gap) (ref : (D.haar.continuous.coefficient i).roots)
    (f : M × M →ᵇ ℝ) (P₀ : Fin Q.count → Fin Q.count → ℝ)
    (hP₀ : ∀ j k, 0 ≤ P₀ j k) (hmassP : 0 < ∑ j, ∑ k, P₀ j k)
    (hzero : ∀ j k, ¬(D.haar.continuous.coefficient i).clockClassAllowed Q j k → P₀ j k = 0) :
    let C := D.haar.continuous.coefficient i
    let Seed := (P C.seedIndex).seed
    let root := populationSeedRootLabelValue Seed a
    let basis := Module.finBasis ℝ Seed.covector.ker
    let q := Module.finrank ℝ Seed.covector.ker
    ∃ (R : ℕ) (K : ℝ), 0 < R ∧ 0 ≤ K ∧
    ∀ (spatial : Measure (Option Seed.covector.ker)) [IsProbabilityMeasure spatial],
      (∀ᵐ w ∂spatial, ∀ x, w = some x → x ∈ root '' C.roots) →
    ∀ (m depth N : ℕ), 4 < q → 0 < N →
      ∀ (hm : 0 < m) (hdepth : m ≤ 2 ^ depth), 2 ^ depth ≤ 2 * m → ∀ tilt : ℝ,
    let point := fun w : Option Seed.covector.ker ↦ w.elim 0 id
    let z := fun w ↦ labelCubeCoordinates basis (R : ℝ) (point w)
    let θ := fun w : Option Seed.covector.ker ↦ w.map (fun _ ↦ ())
    let πclass := clockClassJointProbability P₀ hP₀ hmassP
    let ρ := spatial.prod (πclass : Measure (Fin Q.count × Fin Q.count))
    let law := (Measure.pi (fun _ : Fin N ↦ ρ)).prod (Measure.pi (fun _ : Fin N ↦ ρ))
    let graph := fun sample ↦ pairedClassActiveGraph θ (C.clockClassAllowed Q) sample.1 sample.2
    let cost := fun sample j k ↦ (N : ℝ) ^ (2 / (q : ℝ)) *
      C.clockClassKinetic Q ref.val (sample.1 j).2.1 (sample.2 k).2.2
        (basis.equivFun (point (sample.2 k).1 - point (sample.1 j).1)) +
      tilt * C.clockClassProbe Q ref.val ref.property f (sample.1 j).2.1 (sample.2 k).2.2
    (∫ sample, PartialMatching.legalMaximumValue (graph sample) (cost sample) ∂law) / N ≤
      (∫ sample, ∑ leaf : Fin q → Fin (2 ^ depth + 1), PartialMatching.legalMaximumValue
        (PartialMatching.spatialLegalBlock (graph sample)
          (fun j ↦ gridCellLabel q m depth depth hm hdepth (z (sample.1 j).1))
          (fun k ↦ gridCellLabel q m depth depth hm hdepth (z (sample.2 k).1)) leaf)
        (cost sample) ∂law) / N +
      activeGridRepairError q (legalGridRepairConstant q (Q.count + 1) (Q.count * Q.count))
        K ‖f‖ tilt 1 ((N : ℝ) / (m : ℝ) ^ q) := by
  classical
  obtain ⟨R,hR,_,hroot,hchange,K,hK,hbound⟩ :=
    D.exists_original_clockClass_macrobox_model hF hcomplete hu ha hinj i Q ref.val ref.property
  dsimp only
  refine ⟨R,K,hR,hK,?_⟩
  intro spatial _ hspatial m depth N hq hN hm hdepth hdepth2 tilt
  let C := D.haar.continuous.coefficient i
  let Seed := (P C.seedIndex).seed
  let basis := Module.finBasis ℝ Seed.covector.ker
  let q := Module.finrank ℝ Seed.covector.ker
  let point := fun w : Option Seed.covector.ker ↦ w.elim 0 id
  let z := fun w ↦ labelCubeCoordinates basis (R : ℝ) (point w)
  let θ := fun w : Option Seed.covector.ker ↦ w.map (fun _ ↦ ())
  let πclass := clockClassJointProbability P₀ hP₀ hmassP
  let ρ := spatial.prod (πclass : Measure (Fin Q.count × Fin Q.count))
  let law := (Measure.pi (fun _ : Fin N ↦ ρ)).prod (Measure.pi (fun _ : Fin N ↦ ρ))
  let kin := fun j k vec ↦ (2 * (R : ℝ)) ^ 2 * C.clockClassKinetic Q ref.val j k vec
  let probe := C.clockClassProbe Q ref.val ref.property f
  have hz : Measurable z := (continuous_labelCubeCoordinates basis (R : ℝ)).measurable.comp
    (MeasureTheory.Option.measurable_elim 0 measurable_id)
  have hθ : Measurable θ := by
    convert MeasureTheory.Option.measurable_elim (none : Option Unit)
      (measurable_const : Measurable (fun _ : Seed.covector.ker ↦ some ())) using 1
    funext w
    cases w <;> rfl
  have hunit : ∀ᵐ w ∂spatial, (θ w).isSome = true → z w ∈ unitCube q := by
    filter_upwards [hspatial] with w hw
    cases w with
    | none => simp [θ]
    | some x =>
      intro _
      obtain ⟨xroot,hxroot,rfl⟩ := hw x rfl
      exact hroot xroot hxroot
  have hjoint : law.map (fun sample ↦ (sample.1,sample.2)) = law := Measure.map_id
  obtain ⟨hxi,hyi,hxl,hyl,hxy⟩ := iid_facts_of_array_product_law law ρ
    Prod.fst Prod.snd measurable_fst measurable_snd hjoint
  have hkm : Measurable (Function.uncurry (fun p : Fin Q.count × Fin Q.count ↦ kin p.1 p.2)) :=
    (C.measurable_clockClassKinetic Q ref.val).const_mul ((2 * (R : ℝ)) ^ 2)
  have hgp : Measurable (Function.uncurry probe) := C.measurable_clockClassProbe Q ref.val ref.property f
  have h := integral_pairedClass_active_grid_value_div_le (density := 1) (tilt := tilt)
    q m depth N hq hN hm hdepth hdepth2 law spatial P₀ hP₀ hmassP (C.clockClassAllowed Q) hzero
    (fun j sample ↦ sample.1 j) (fun k sample ↦ sample.2 k)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun k ↦ (measurable_pi_apply k).comp measurable_snd)
    hxi hyi hxl hyl hxy θ hθ z hz hunit kin hkm probe hgp zero_le_one measureReal_le_one hK
    (norm_nonneg f) (fun j k _ vec ↦ hbound j k vec)
    (fun j k _ ↦ C.clockClassProbe_abs_le Q ref.val ref.property f j k)
  have hcost (x y : Option Seed.covector.ker × (Fin Q.count × Fin Q.count)) :
      pairedClassScaledEdgeCost z kin probe ((N : ℝ) ^ (2 / (q : ℝ))) tilt x y =
      (N : ℝ) ^ (2 / (q : ℝ)) * C.clockClassKinetic Q ref.val x.2.1 y.2.2
        (basis.equivFun (point y.1 - point x.1)) + tilt * probe x.2.1 y.2.2 := by
    dsimp only [pairedClassScaledEdgeCost,kin,z]
    rw [hchange (point x.1) (point y.1) x.2.1 y.2.2]
  simpa only [mul_one,hcost,Fintype.card_fin] using h

end OTSelector.Reconstruction
