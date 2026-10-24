import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalMacroIntrinsicClock
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalIntrinsicClockCountableRigidity
import OTSelector.Reconstruction.FinslerPhysicalSceneOriginalCanonicalSceneScale
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedOriginalClosedClockCarrier

/-! Actual original countable closed-clock carriers provide the true intrinsic
clock domain for the unchanged full plans and their original macro cost. -/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
open scoped Topology ContDiff ENNReal
noncomputable section
namespace OTSelector.Reconstruction
open PointProcess PointProcess.LocalConfiguration OTSelector.Probability
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

local instance originalClockCarrierRigidityStandardBorel {ι : Type*} [Fintype ι] :
    StandardBorelSpace ((ι → ℝ) × ℝ) := inferInstance
local instance originalClockCarrierRigidityConfigTopology {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : TopologicalSpace (LocalConfiguration base) := vagueTopology base
local instance originalClockCarrierRigidityConfigBorel {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : BorelSpace (LocalConfiguration base) := vagueBorelSpace
local instance originalClockCarrierRigidityConfigPolish {ι : Type*} [Fintype ι]
    (base : (ι → ℝ) × ℝ) : PolishSpace (LocalConfiguration base) := vaguePolishSpace
local instance originalClockCarrierRigidityPlanPolish {ι : Type*} [Fintype ι] :
    PolishSpace (LocalFiniteMeasure (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ))) :=
  LocalFiniteMeasure.instPolishSpace

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop}

variable (j : ℕ)
set_option quotPrecheck false
local notation "Point" => ((Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "Edge" => (Point × Point)
variable (base : (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × ℝ)
local notation "PairScene" => CavityLocalScene Point Point
local notation "MacroScene" => (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ) × (PairScene × LocalConfiguration base)
variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

namespace PopulationLocalPressureCore
/-- Every actual closed-window carrier edge is in the single true intrinsic domain. -/
theorem originalClosedClockCarrier_mem_intrinsicDomain
    {r : ℝ} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    {s : MacroScene} {e : Edge} (he : (s,e) ∈ D.originalClosedClockCarrier j base) :
    e ∈ physicalSceneOriginalIntrinsicClockDomain (P j).seed
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm s.1) := by
  obtain ⟨i, hi, htag, hclock⟩ := he
  subst j
  exact (D.haar.continuous.coefficient i).mem_intrinsicClockDomain_of_macroLabel_region
    hF hcomplete hu ha hinj htag hclock

/-- A nonempty actual carrier edge also supplies the original moment witness
at its unchanged native macro label. -/
theorem originalClosedClockCarrier_has_intrinsicClockMoments
    {r : ℝ} {δ loss : ℝ≥0∞}
    (D : PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good r δ loss)
    {s : MacroScene} {e : Edge} (he : (s,e) ∈ D.originalClosedClockCarrier j base) :
    ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm s.1 ∈ (P j).seed.labels) ∧
    ∃ α β : Measure ℝ, Nonempty (OriginalSeedConditionalMoments (P j).seed
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm s.1) α β) := by
  obtain ⟨i, hi, htag, _⟩ := he
  subst j
  exact (D.haar.continuous.coefficient i).exists_intrinsicClockMoments_of_macroLabel
    hF hcomplete hu ha hinj htag

variable (rseq : ℕ → ℝ) (δseq lossseq : ℕ → ℝ≥0∞)
  (Dseq : ∀ m, PopulationLocalPressureCore P a κ lambda μ ν ρ₀ ρ₁ v b Good
    (rseq m) (δseq m) (lossseq m))

/-- The full unchanged plans agree once the actual countable core carrier,
full-average source AC and the same original macro-cost cycles are known. -/
theorem plans_eq_of_originalClosedClockCarrierUnion
    (s : MacroScene)
    (hcarrier : ∀ᵐ e ∂(LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge),
      (s,e) ∈ originalClosedClockCarrierUnion j base rseq δseq lossseq Dseq)
    (hsource : (s.2.1.1 : Measure Edge).fst = (s.2.1.2 : Measure Edge).fst)
    (htarget : (s.2.1.1 : Measure Edge).snd = (s.2.1.2 : Measure Edge).snd)
    (hac : (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).fst ≪
      (volume : Measure (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)).prod
        (volume : Measure ℝ))
    (hdim : 2 ≤ finrank ℝ E)
    {T : Set Point} (hT : T.Countable)
    (hTcarried : ∀ᵐ y ∂(s.2.1.1 : Measure Edge).snd, y ∈ T)
    (hcycle : ∀ᵐ p ∂((LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge).prod
      (LocalFiniteMeasure.cavityAverage s.2.1 : Measure Edge)),
      p.1.1.2 < p.1.2.2 → p.2.1.2 < p.2.2.2 →
      p.1.1.2 < p.2.2.2 → p.2.1.2 < p.1.2.2 →
      physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.1.1 p.1.2 +
        physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.2.1 p.2.2 ≤
      physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.1.1 p.2.2 +
        physicalSceneOriginalMacroCost (P := P) (a := a) j s.1 p.2.1 p.1.2) :
    (s.2.1.1 : Measure Edge) = (s.2.1.2 : Measure Edge) := by
  let avg : Measure Edge := LocalFiniteMeasure.cavityAverage s.2.1
  by_cases hz : avg = 0
  · have hsum : (s.2.1.1 : Measure Edge) + (s.2.1.2 : Measure Edge) = 0 := by
      exact (Measure.ennreal_smul_eq_zero.mp hz).resolve_left (by norm_num)
    have h₀ : (s.2.1.1 : Measure Edge) ≤ 0 :=
      hsum ▸ Measure.le_add_right (le_refl (s.2.1.1 : Measure Edge))
    have h₁ : (s.2.1.2 : Measure Edge) ≤ 0 :=
      hsum ▸ Measure.le_add_left (le_refl (s.2.1.2 : Measure Edge))
    exact (le_antisymm h₀ bot_le).trans (le_antisymm h₁ bot_le).symm
  have _inst : (ae avg).NeBot := ae_neBot.mpr hz
  obtain ⟨edge, hedge⟩ := hcarrier.exists
  obtain ⟨m, hm⟩ := mem_iUnion.mp hedge
  obtain ⟨hw, α, β, ⟨Dmom⟩⟩ := (Dseq m).originalClosedClockCarrier_has_intrinsicClockMoments
    j base hF hcomplete hu ha hinj hm
  have hlegalavg : ∀ᵐ e ∂avg, e ∈ physicalSceneOriginalIntrinsicClockDomain (P j).seed
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFun.symm s.1) := by
    filter_upwards [hcarrier] with e he
    obtain ⟨n, hn⟩ := mem_iUnion.mp he
    exact (Dseq n).originalClosedClockCarrier_mem_intrinsicDomain j base hF hcomplete hu ha hinj hn
  have hlegal := ae_add_measure_iff.mp
    ((Measure.ae_ennreal_smul_measure_iff (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0)).mp hlegalavg)
  have hsourceavg : avg.fst = (s.2.1.1 : Measure Edge).fst := by
    change ((2 : ℝ≥0∞)⁻¹ • ((s.2.1.1 : Measure Edge) +
      (s.2.1.2 : Measure Edge))).map Prod.fst = _
    rw [Measure.map_smul, Measure.map_add _ _ measurable_fst]
    change (2 : ℝ≥0∞)⁻¹ • ((s.2.1.1 : Measure Edge).fst +
      (s.2.1.2 : Measure Edge).fst) = _
    rw [← hsource, ← two_smul ℝ≥0∞, smul_smul]
    rw [ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]
  have hρ : (s.2.1.1 : Measure Edge).fst ≪
      (volume : Measure (Fin (finrank ℝ (P j).seed.covector.ker) → ℝ)).prod
        (volume : Measure ℝ) := by
    change avg.fst ≪ _ at hac
    rwa [hsourceavg] at hac
  have hcost := physicalSceneOriginalMacroCost_eq_intrinsicClockCost
    hF hcomplete hu ha hinj j hw
  apply Dmom.ambient_plans_eq_of_calibrationInterior_ae_twoCycle_countable_targets hF hu hw
    (original_seed_transverse_finrank_pos (P j).seed hdim) hρ hT _ hTcarried
    (s.2.1.1 : Measure Edge) (s.2.1.2 : Measure Edge) rfl hsource.symm
    rfl htarget.symm hlegal.1 hlegal.2
  simpa only [← hcost, LocalFiniteMeasure.coe_cavityAverage] using hcycle
end PopulationLocalPressureCore
end OTSelector.Reconstruction
