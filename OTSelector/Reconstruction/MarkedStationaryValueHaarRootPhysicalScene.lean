import OTSelector.Reconstruction.MarkedStationaryValueHaarRootStationarity
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedLaw

/-!
# Stationarity of the actual multidimensional physical plan scene

Both endpoints retain their original potential clocks and both original plans
use the same physical spatial reroot. The action is continuous on the actual
locally finite vague measure carrier and satisfies the original-root cocycle.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal CompactlySupported
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false

section LocallyFiniteMap
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X] [BorelSpace X]

/-- Pushforward of an actual locally finite diffuse plan by a physical
homeomorphism, retaining its actual measure. -/
def localFiniteMapHomeomorph (e : X ≃ₜ X) (μ : LocalFiniteMeasure X) : LocalFiniteMeasure X :=
  ⟨(μ : Measure X).map e, Measure.IsFiniteMeasureOnCompacts.map (μ : Measure X) e⟩

omit [T2Space X] [LocallyCompactSpace X] in
@[simp]
theorem coe_localFiniteMapHomeomorph (e : X ≃ₜ X) (μ : LocalFiniteMeasure X) :
    (localFiniteMapHomeomorph e μ : Measure X) = (μ : Measure X).map e := rfl

omit [T2Space X] [LocallyCompactSpace X] in
/-- Compact-test pushforward is continuous for the actual vague topology. -/
theorem continuous_localFiniteMapHomeomorph (e : X ≃ₜ X) :
    Continuous (localFiniteMapHomeomorph e) := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro f
  have heq : (fun μ : LocalFiniteMeasure X ↦
      LocalFiniteMeasure.testIntegral (localFiniteMapHomeomorph e μ) f) =
      (fun μ ↦ LocalFiniteMeasure.testIntegral μ (f.comp e.toCocompactMap)) := by
    funext μ
    exact integral_map e.continuous.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable
  change Continuous (fun μ : LocalFiniteMeasure X ↦
    LocalFiniteMeasure.testIntegral (localFiniteMapHomeomorph e μ) f)
  rw [heq]
  exact LocalFiniteMeasure.continuous_testIntegral _
end LocallyFiniteMap

variable {ι : Type*} [Fintype ι]

local instance : PolishSpace
    (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

/-- The original physical clock is fixed by every spatial root translation. -/
def physicalScenePointReroot (v : ι → ℝ) : ((ι → ℝ) × ℝ) ≃ₜ ((ι → ℝ) × ℝ) :=
  (Homeomorph.addRight (-v)).prodCongr (Homeomorph.refl ℝ)

omit [Fintype ι] in
@[simp]
theorem physicalScenePointReroot_apply (v : ι → ℝ) (p : (ι → ℝ) × ℝ) :
    physicalScenePointReroot v p = (p.1 - v, p.2) := by
  rfl

/-- Both original endpoints undergo the same physical root change. -/
def physicalSceneEdgeReroot (v : ι → ℝ) :
    (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) ≃ₜ (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  (physicalScenePointReroot v).prodCongr (physicalScenePointReroot v)

/-- The actual pair of locally finite physical plans is rerooted without any
change of original clocks, chart tag or frozen coefficient tag. -/
def physicalSceneReroot (v : ι → ℝ)
    (scene : CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ)) :
    CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ) :=
  (localFiniteMapHomeomorph (physicalSceneEdgeReroot v) scene.1,
    localFiniteMapHomeomorph (physicalSceneEdgeReroot v) scene.2)

theorem continuous_physicalSceneReroot (v : ι → ℝ) : Continuous (physicalSceneReroot v) :=
  ((continuous_localFiniteMapHomeomorph _).comp continuous_fst).prodMk
    ((continuous_localFiniteMapHomeomorph _).comp continuous_snd)

variable {M Ω : Type*} [MeasurableSpace M] [MeasurableSpace Ω]

omit [Fintype ι] [MeasurableSpace M] in
/-- The concrete physical observation obeys the exact multidimensional
root-change cocycle with its original potential clock. -/
theorem physicalSceneEdgeReroot_observation (v z : ι → ℝ)
    (coord : M → (ι → ℝ)) (u : M → ℝ) (p : M × M) :
    physicalSceneEdgeReroot v (physicalSceneRootedObservation coord u z p) =
      physicalSceneRootedObservation coord u (z + v) p := by
  change ((coord p.1 - z - v, u p.1), (coord p.2 - z - v, u p.2)) =
    ((coord p.1 - (z + v), u p.1), (coord p.2 - (z + v), u p.2))
  simp only [sub_sub]

omit [MeasurableSpace Ω] in
/-- The actual scaled original plan, including its diffuse source mass, obeys
the same root-change cocycle exactly. -/
theorem physicalSceneReroot_localPlan (v : ι → ℝ)
    (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (w : Ω) (z : ι → ℝ) :
    localFiniteMapHomeomorph (physicalSceneEdgeReroot v)
      (physicalSceneRootedLocalPlan Γ coord u N (w, z)) =
        physicalSceneRootedLocalPlan Γ coord u N (w, z + v) := by
  apply Subtype.ext
  change (physicalSceneRootedPlan (Γ w) coord u N z).map (physicalSceneEdgeReroot v) =
    physicalSceneRootedPlan (Γ w) coord u N (z + v)
  unfold physicalSceneRootedPlan
  rw [Measure.map_smul, Measure.map_map (physicalSceneEdgeReroot v).continuous.measurable
    (measurable_physicalSceneRootedObservation coord hcoord u hu z)]
  congr 2
  funext p
  exact physicalSceneEdgeReroot_observation v z coord u p

omit [MeasurableSpace Ω] in
/-- The two original plans share a single exact physical reroot cocycle. -/
theorem physicalSceneReroot_localScene (v : ι → ℝ)
    (Γplus Γminus : Ω → Measure (M × M))
    [∀ w, IsFiniteMeasure (Γplus w)] [∀ w, IsFiniteMeasure (Γminus w)]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord) (u : M → ℝ) (hu : Measurable u)
    (N : ℝ) (w : Ω) (z : ι → ℝ) :
    physicalSceneReroot v (physicalSceneRootedLocalScene Γplus Γminus coord u N (w, z)) =
      physicalSceneRootedLocalScene Γplus Γminus coord u N (w, z + v) := by
  apply Prod.ext
  · exact physicalSceneReroot_localPlan v Γplus coord hcoord u hu N w z
  · exact physicalSceneReroot_localPlan v Γminus coord hcoord u hu N w z

/-- A weak limit of the actual two original physical plans rooted in expanding
Haar cubes is spatially stationary in every transverse dimension. -/
theorem measurePreserving_physicalSceneReroot_of_cubeRooted_tendsto
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Γplus Γminus : ∀ n, Ω n → Measure (M × M))
    [∀ n w, IsFiniteMeasure (Γplus n w)] [∀ n w, IsFiniteMeasure (Γminus n w)]
    (hplus : ∀ n, Measurable (Γplus n)) (hminus : ∀ n, Measurable (Γminus n))
    (coord : ℕ → M → (ι → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (u : M → ℝ) (hu : Measurable u)
    (N R : ℕ → ℝ) (hN : ∀ n, 0 < N n) (hR : ∀ n, 0 < R n)
    (hD : ∀ n, volume (haarRootCube ι (R n)) = ENNReal.ofReal (N n))
    (hlarge : Tendsto R atTop atTop)
    {ν : ProbabilityMeasure (CavityLocalScene ((ι → ℝ) × ℝ) ((ι → ℝ) × ℝ))}
    (hlim : Tendsto (fun n ↦ physicalSceneRootedLocalSceneLaw (P n) (Γplus n) (Γminus n)
      (hplus n) (hminus n) (coord n) (hcoord n) u hu (N n) (hN n)
        (haarRootCube ι (R n)) (hD n)) atTop (𝓝 ν)) (v : ι → ℝ) :
    MeasurePreserving (physicalSceneReroot v) (ν : Measure _) (ν : Measure _) := by
  have hmass (n : ℕ) : N n = (2 * R n) ^ Fintype.card ι := by
    have hpow : 0 ≤ (2 * R n) ^ Fintype.card ι := pow_nonneg (by linarith [hR n]) _
    have h := congrArg ENNReal.toReal (hD n)
    simpa only [volume_haarRootCube ι (hR n).le,
      ENNReal.toReal_ofReal (hN n).le, ENNReal.toReal_ofReal hpow] using h.symm
  have hlaw (n : ℕ) :
      (physicalSceneRootedLocalSceneLaw (P n) (Γplus n) (Γminus n)
        (hplus n) (hminus n) (coord n) (hcoord n) u hu (N n) (hN n)
          (haarRootCube ι (R n)) (hD n) : Measure _) =
        haarCubeAverageLaw (P n)
          (physicalSceneRootedLocalScene (Γplus n) (Γminus n) (coord n) u (N n)) (R n) := by
    change ((P n).prod (cavityRootMeasure volume (haarRootCube ι (R n)) (N n))).map
      (physicalSceneRootedLocalScene (Γplus n) (Γminus n) (coord n) u (N n)) =
      ((P n).prod (cavityRootMeasure volume (haarRootCube ι (R n))
        ((2 * R n) ^ Fintype.card ι))).map
      (physicalSceneRootedLocalScene (Γplus n) (Γminus n) (coord n) u (N n))
    rw [hmass n]
  exact measurePreserving_of_haarCubeAverageLaw_tendsto P
    (fun n ↦ physicalSceneRootedLocalScene (Γplus n) (Γminus n) (coord n) u (N n))
    (fun n ↦ measurable_physicalSceneRootedLocalScene _ _ (hplus n) (hminus n)
      (coord n) (hcoord n) u hu (N n)) R hR hlarge _ hlaw hlim
    (continuous_physicalSceneReroot v) v (fun n w z ↦
      physicalSceneReroot_localScene v (Γplus n) (Γminus n) (coord n) (hcoord n) u hu (N n) w z)

end OTSelector.Reconstruction
