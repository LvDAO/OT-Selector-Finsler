import OTSelector.Reconstruction.MarkedStationaryValueLegalInputRootMoments
import OTSelector.Reconstruction.MarkedStationaryValueLegalOptimalPalmLimit
import OTSelector.Probability.JointLawTightness

/-!
# Joint compactness of the actual optimum and its unchanged colored inputs

Original Haar averaging gives uniform local first moments for both input
colors. Their tight laws and the actual matching's tight law are coupled on
exactly the same original environment and root; no replacement coupling or
independence of selected observations is used.
-/
open Set Function MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace Metric
open scoped ENNReal NNReal
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
local instance markedStationaryValueLegalInputJointTightnessLocalInputPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointTightnessLocalPlanPolish (q : ℕ) : PolishSpace
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := LocalFiniteMeasure.instPolishSpace
local instance markedStationaryValueLegalInputJointTightnessLocalInputNonempty (q : ℕ) : Nonempty
    (LocalFiniteMeasure (LegalColoredInputPoint q)) := ⟨⟨0, inferInstance⟩⟩
local instance markedStationaryValueLegalInputJointTightnessLocalPlanNonempty (q : ℕ) : Nonempty
    (LocalFiniteMeasure (LegalMarkedPhysicalEdge q)) := ⟨⟨0, inferInstance⟩⟩

/-- The original colored input laws are tight at arbitrary positive physical
scales, from their internally produced actual local mass moments. -/
theorem isTightMeasureSet_legalMarkedRootedColoredInputLocal
    {I : Type*} (q : ℕ) (L : I → ℝ) (hL : ∀ k, 0 < L k)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β] :
    IsTightMeasureSet (range (fun k ↦
      ((twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L k ^ q))).prod
        (legalMarkedHaarRootLaw q (L k))).map (legalMarkedRootedColoredInputLocal q (L k)))) := by
  let K := CompactExhaustion.choice (LegalColoredInputPoint q)
  have hb (n : ℕ) : ∃ R > 0, ∀ x ∈ K n, ‖x.1.1‖ < R := by
    obtain ⟨R, hR, hbound⟩ := ((K.isCompact n).image
      (continuous_fst.comp continuous_fst)).isBounded.exists_pos_norm_lt
    exact ⟨R, hR, fun x hx ↦ hbound _ ⟨x, hx, rfl⟩⟩
  choose R hR hKR using hb
  refine LocalFiniteMeasure.isTightMeasureSet_map_of_lintegral_localMass_le
    (fun k ↦ (twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L k ^ q))).prod
      (legalMarkedHaarRootLaw q (L k)))
    (fun k ↦ legalMarkedRootedColoredInputLocal q (L k))
    (fun k ↦ measurable_legalMarkedRootedColoredInputLocal q (L k))
    (fun n ↦ interior (K n)) (fun _ ↦ isOpen_interior) ?_
    (fun n ↦ 2 * volume (ball (0 : Fin q → ℝ) (R n)))
    (fun n ↦ ENNReal.mul_ne_top (by norm_num) measure_ball_lt_top.ne) ?_
  · intro A hA
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hA
    exact ⟨n + 1, hn.trans (K.subset_interior_succ n)⟩
  · intro k n
    apply (lintegral_mono (fun p ↦ measure_mono ?_)).trans
      (lintegral_legalMarkedRootedColoredInputMeasure_spatialWindow_le q (hL k) α β
        measurableSet_ball measure_ball_lt_top.ne)
    intro x hx
    have hxn := hKR n x (interior_subset hx)
    simpa only [mem_ofPred_eq, mem_ball, dist_zero_right] using hxn

/-- Matching and immutable original input colors in one actual joint carrier. -/
abbrev LegalMarkedOptimalInputScene (q : ℕ) :=
  CavityLocalScene (LegalMarkedPhysicalPoint q) (LegalMarkedPhysicalPoint q) ×
    LocalFiniteMeasure (LegalColoredInputPoint q)

/-- The true finite optimizer and all original observations share one literal
original sample and one literal Haar root. -/
def legalMarkedOptimalInputObservation (q : ℕ) {L : ℝ} (hL : 0 < L)
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ) (g : ℝ → ℝ → ℝ) (t : ℝ)
    (p : TwoMarkedCloudSpace q ℝ ℝ × (Fin q → ℝ)) : LegalMarkedOptimalInputScene q := by
  have : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  exact (physicalSceneRootedLocalScene (legalMarkedNormalizedOptimalPlan q L kin g t)
    (legalMarkedNormalizedOptimalPlan q L kin g t) (legalMarkedCenteredCoordinate q L)
    Prod.snd (L ^ q) p, legalMarkedRootedColoredInputLocal q L p)

theorem measurable_legalMarkedOptimalInputObservation (q : ℕ) {L : ℝ} (hL : 0 < L)
    {kin : ℝ → ℝ → (Fin q → ℝ) → ℝ}
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    {g : ℝ → ℝ → ℝ} (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    Measurable (legalMarkedOptimalInputObservation q hL kin g t) := by
  have : ∀ ω : TwoMarkedCloudSpace q ℝ ℝ,
      IsFiniteMeasure (legalMarkedNormalizedOptimalPlan q L kin g t ω) :=
    fun ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q hL kin g t ω
  exact (measurable_physicalSceneRootedLocalScene _ _
    (measurable_legalMarkedNormalizedOptimalPlan q L hk hg t)
    (measurable_legalMarkedNormalizedOptimalPlan q L hk hg t)
    (legalMarkedCenteredCoordinate q L) (measurable_legalMarkedCenteredCoordinate q L)
    Prod.snd measurable_snd (L ^ q)).prodMk (measurable_legalMarkedRootedColoredInputLocal q L)

/-- The literal original joint probability law, with no independent selected
input or orphan process substituted. -/
def legalMarkedOptimalInputSceneLaw (q : ℕ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ)
    (L : ℝ) (hL : 0 < L) : ProbabilityMeasure (LegalMarkedOptimalInputScene q) := by
  let : IsProbabilityMeasure (legalMarkedHaarRootLaw q L) :=
    isProbabilityMeasure_legalMarkedHaarRootLaw q hL
  exact ⟨((twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L ^ q))).prod
    (legalMarkedHaarRootLaw q L)).map (legalMarkedOptimalInputObservation q hL kin g t),
    Measure.isProbabilityMeasure_map (measurable_legalMarkedOptimalInputObservation q hL hk hg t).aemeasurable⟩

/-- Original mass and original input moments produce actual joint tightness,
without a supplied joint law, tightness bound or selected-input independence. -/
theorem isTightMeasureSet_legalMarkedOptimalInputSceneLaw
    {I : Type*} (q : ℕ) (L : I → ℝ) (hL : ∀ k, 0 < L k)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    IsTightMeasureSet (range (fun k ↦ (legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
      (L k) (hL k) : Measure (LegalMarkedOptimalInputScene q)))) := by
  let P k := twoMarkedCloudLaw q ℝ ℝ α β (Real.toNNReal (L k ^ q))
  let Γ k := legalMarkedNormalizedOptimalPlan q (L k) kin g t
  have : ∀ k ω, IsFiniteMeasure (Γ k ω) :=
    fun k ω ↦ isFiniteMeasure_legalMarkedNormalizedOptimalPlan q (hL k) kin g t ω
  have hΓ k : Measurable (Γ k) := measurable_legalMarkedNormalizedOptimalPlan q (L k) hk hg t
  let coord k := legalMarkedCenteredCoordinate q (L k)
  have hcoord k : Measurable (coord k) := measurable_legalMarkedCenteredCoordinate q (L k)
  let N k := L k ^ q
  have hN k : 0 < N k := pow_pos (hL k) q
  let D k := haarRootCube (Fin q) (L k / 2)
  have hplan := isTightMeasureSet_physicalSceneRootedLocalPlan P Γ hΓ coord hcoord
    Prod.snd measurable_snd N hN D 1 (by simp)
    (fun k ↦ lintegral_legalMarkedNormalizedOptimalPlan_univ_le_one q (hL k) α β kin g t)
  have hpm k := measurable_physicalSceneRootedLocalPlan (Γ k) (hΓ k)
    (coord k) (hcoord k) Prod.snd measurable_snd (N k)
  let E k := (P k).prod (legalMarkedHaarRootLaw q (L k))
  have hscene := isTightMeasureSet_original_joint_of_marginals E
    (fun k ↦ physicalSceneRootedLocalPlan (Γ k) (coord k) Prod.snd (N k))
    (fun k ↦ physicalSceneRootedLocalPlan (Γ k) (coord k) Prod.snd (N k)) hpm hpm hplan hplan
  have hj := isTightMeasureSet_original_joint_of_marginals E
    (fun k ↦ physicalSceneRootedLocalScene (Γ k) (Γ k) (coord k) Prod.snd (N k))
    (fun k ↦ legalMarkedRootedColoredInputLocal q (L k))
    (fun k ↦ (hpm k).prodMk (hpm k))
    (fun k ↦ measurable_legalMarkedRootedColoredInputLocal q (L k)) hscene
    (isTightMeasureSet_legalMarkedRootedColoredInputLocal q L hL α β)
  exact hj

/-- Prokhorov chooses one common weak subsequence of the same original legal
optimum and its unchanged source and target input colors. -/
theorem exists_tendsto_subseq_legalMarkedOptimalInputSceneLaw
    (q : ℕ) (L : ℕ → ℝ) (hL : ∀ k, 0 < L k)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (kin : ℝ → ℝ → (Fin q → ℝ) → ℝ)
    (hk : Measurable (Function.uncurry (fun p : ℝ × ℝ ↦ kin p.1 p.2)))
    (g : ℝ → ℝ → ℝ) (hg : Measurable (Function.uncurry g)) (t : ℝ) :
    ∃ Q : ProbabilityMeasure (LegalMarkedOptimalInputScene q), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ Tendsto (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t
        (L (φ k)) (hL (φ k))) atTop (𝓝 Q) := by
  apply exists_tendsto_subseq_probabilityMeasure_of_isTight
    (fun k ↦ legalMarkedOptimalInputSceneLaw q α β kin hk g hg t (L k) (hL k))
  exact isTightMeasureSet_legalMarkedOptimalInputSceneLaw q L hL α β kin hk g hg t

end OTSelector.Reconstruction
