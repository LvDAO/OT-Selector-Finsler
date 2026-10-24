import OTSelector.Reconstruction.FinslerPhysicalSceneRootedClock
import OTSelector.Reconstruction.FinslerPhysicalSceneDisplacement

/-!
# Rooted long edges of the actual physical plan

The actual translated plan reads spatial long edges directly from the original
physical plan.  Haar root averaging bounds their window mass by that plan's
actual squared spatial displacement energy.  On an original population near
event, the same basis and radius as the physical coercivity theorem turn the
original scaled global slack energy into this displacement bound.  Every near
restriction is retained explicitly.
-/

open Set Function MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal Classical

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Rooted

variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

/-- The rooted source lies in the observed window and its actual squared
spatial displacement is at least the specified threshold. -/
def physicalSceneLongEdgeWindow (U : Set (ι → ℝ)) (r : ℝ≥0∞) :
    Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  {e | e.1.1 ∈ U ∧ r ≤ ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2)}

/-- Actual spatial long-edge windows are measurable. -/
theorem measurableSet_physicalSceneLongEdgeWindow
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (r : ℝ≥0∞) :
    MeasurableSet (physicalSceneLongEdgeWindow U r) :=
  (hU.preimage measurable_fst.fst).inter
    (measurableSet_le measurable_const
      ((measurable_snd.fst.sub measurable_fst.fst).norm.pow_const 2).ennreal_ofReal)

/-- The rooted long-edge mass is exactly the original physical displacement
tail read in the translated original source window. -/
theorem physicalSceneRootedPlan_longEdgeWindow
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (r : ℝ≥0∞) :
    physicalSceneRootedPlan Γ coord u N z (physicalSceneLongEdgeWindow U r) =
      ENNReal.ofReal N * cavityRootWindowReadout Γ (fun p ↦ coord p.1)
        (fun p ↦ if r ≤ ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) then 1 else 0) U z := by
  let f := physicalSceneRootedObservation coord u z
  have hf : Measurable f := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have hwindow := measurableSet_physicalSceneLongEdgeWindow hU r
  change (ENNReal.ofReal N • Γ.map f) _ = _
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply hf hwindow,
    ← lintegral_indicator_one (hwindow.preimage hf)]
  congr 1
  apply lintegral_congr
  intro p
  simp only [Set.indicator_apply, mem_preimage, f, physicalSceneRootedObservation,
    physicalSceneLongEdgeWindow, mem_ofPred_eq, sub_sub_sub_cancel_right]
  by_cases hx : coord p.1 - z ∈ U <;>
    simp only [hx, ite_true, ite_false, true_and, false_and, Pi.one_apply]

/-- The actual original squared displacement energy controls Haar averaged
rooted long-edge mass for every finite physical plan. -/
theorem lintegral_physicalSceneRootedPlan_longEdgeWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    (∫⁻ z, physicalSceneRootedPlan Γ coord u N z (physicalSceneLongEdgeWindow U r)
      ∂cavityRootMeasure volume D N) ≤
      (volume U * ∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γ) / r := by
  simp_rw [physicalSceneRootedPlan_longEdgeWindow Γ coord hcoord u hu N _ U hU r]
  exact lintegral_cavityRoot_scaled_window_tail_le volume Γ
    (fun p ↦ coord p.1) (hcoord.comp measurable_fst)
    (fun p ↦ ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2))
    (((hcoord.comp measurable_snd).sub
      (hcoord.comp measurable_fst)).norm.pow_const 2).ennreal_ofReal
    U hU D N hN r hr0 hrt

end Rooted

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

namespace PopulationLocalPressureCore

variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- The original physical seed-label position in the retained coefficient basis. -/
def physicalBasisPosition (i : Fin D.haar.continuous.count) (x : M) :
    Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ :=
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  (Module.finBasis ℝ S.covector.ker).equivFun (populationSeedRootLabelValue S a (a x))

/-- The same physical basis position at the actual spatial scale. -/
def scaledPhysicalBasisPosition (i : Fin D.haar.continuous.count) (spatialScale : ℝ) (x : M) :
    Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ :=
  spatialScale • D.physicalBasisPosition i x

/-- Squared displacement in the scaled physical observation is exactly the
original basis displacement times the square of the actual spatial scale. -/
theorem scaledPhysicalBasisPosition_displacement_sq
    (i : Fin D.haar.continuous.count) (spatialScale : ℝ) (x y : M) :
    ‖D.scaledPhysicalBasisPosition i spatialScale y -
      D.scaledPhysicalBasisPosition i spatialScale x‖ ^ 2 =
      spatialScale ^ 2 * ‖D.basisDisplacement i (x, y)‖ ^ 2 := by
  have hd : D.scaledPhysicalBasisPosition i spatialScale y -
      D.scaledPhysicalBasisPosition i spatialScale x =
      spatialScale • D.basisDisplacement i (x, y) := by
    simp only [scaledPhysicalBasisPosition, physicalBasisPosition, basisDisplacement,
      map_sub, smul_sub]
  rw [hd, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]

variable (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSceneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))

include hF hcomplete hu ha hinj

/-- The actual original scaled basis observation is measurable. -/
theorem measurable_scaledPhysicalBasisPosition
    (i : Fin D.haar.continuous.count) (spatialScale : ℝ) :
    Measurable (D.scaledPhysicalBasisPosition i spatialScale) := by
  let _instSceneMetric : MetricSpace M := F.metricSpace
  let _instSceneProper : ProperSpace M := F.properSpace_of_complete hcomplete
  let _instScenePolish : PolishSpace M := inferInstance
  let S := (P (D.haar.continuous.coefficient i).seedIndex).seed
  have hw := measurable_populationSeedRootLabelValue S hF hcomplete hu ha hinj
  exact ((Module.finBasis ℝ S.covector.ker).equivFunL.continuous.measurable.comp
    (hw.comp ha)).const_smul spatialScale

/-- The original common local coercivity controls actual scaled displacement
energy and rooted long-edge mass of the explicitly retained near-event plan.
The optional source restriction keeps its realized columns and can only reduce
the energy paid by the global original physical slack. -/
theorem exists_uniform_rooted_nearDisplacement_energy_tail :
    ∃ q > 0, ∃ radius > 0,
      ∀ (i : Fin D.haar.continuous.count) (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
        (H : Set M) (_hH : MeasurableSet H) (spatialScale N : ℝ), 0 < N →
        ∀ (rootDomain U : Set
          (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)),
        MeasurableSet U → ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ →
        let coord := D.scaledPhysicalBasisPosition i spatialScale
        let Γnear := Γ.restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ))
        let globalEnergy := ∫⁻ p, ENNReal.ofReal
          (spatialScale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ
        (ENNReal.ofReal q *
          (∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γnear) ≤ globalEnergy) ∧
        ((∫⁻ z, physicalSceneRootedPlan Γnear coord u N z
          (physicalSceneLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N) ≤
          (volume U * (globalEnergy / ENNReal.ofReal q)) / threshold) := by
  obtain ⟨q, hq, radius, hradius, hbound⟩ :=
    D.exists_uniform_nearDisplacement_coercivity hF hcomplete hu ha hinj
  refine ⟨q, hq, radius, hradius, ?_⟩
  intro i Γ _ H hH spatialScale N hN rootDomain U hU threshold ht0 htt
  dsimp only
  let coord := D.scaledPhysicalBasisPosition i spatialScale
  let Γnear := Γ.restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ))
  let globalEnergy := ∫⁻ p, ENNReal.ofReal
    (spatialScale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ
  have hnear := (D.measurableSet_nearDisplacementEvent hF hcomplete hu ha hinj i radius).inter
    (hH.prod MeasurableSet.univ)
  have hpoint : ∀ᵐ p ∂Γnear, ENNReal.ofReal q *
      ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ≤ ENNReal.ofReal
        (spatialScale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) := by
    filter_upwards [ae_restrict_mem hnear] with p hp
    rw [← ENNReal.ofReal_mul hq.le,
      D.scaledPhysicalBasisPosition_displacement_sq i spatialScale p.1 p.2]
    apply ENNReal.ofReal_le_ofReal
    have hb := hbound i p.1 p.2
    rw [nearDisplacementSquared, indicator_of_mem hp.1] at hb
    calc
      q * (spatialScale ^ 2 * ‖D.basisDisplacement i p‖ ^ 2) =
          spatialScale ^ 2 * (q * ‖D.basisDisplacement i p‖ ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (sq_nonneg spatialScale)
  have henergy : ENNReal.ofReal q *
      (∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γnear) ≤ globalEnergy := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact (lintegral_mono_ae hpoint).trans (lintegral_mono' Measure.restrict_le_self le_rfl)
  have henergydiv : (∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γnear) ≤
      globalEnergy / ENNReal.ofReal q := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hq)) (Or.inl ENNReal.ofReal_ne_top)).mpr
    rwa [mul_comm]
  refine ⟨henergy, ?_⟩
  let _instSceneMetric : MetricSpace M := F.metricSpace
  have hcoord := D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale
  refine (lintegral_physicalSceneRootedPlan_longEdgeWindow_le Γnear coord hcoord
    u hu.continuous.measurable N hN rootDomain U hU threshold ht0 htt).trans ?_
  gcongr

/-- In the original environment, a bound on the expected global physical slack
energy controls the expected rooted long-edge mass of the explicitly retained
near-event plan.  All actual restricted target column masses are preserved. -/
theorem exists_uniform_rooted_nearDisplacement_expected_tail :
    ∃ q > 0, ∃ radius > 0,
      ∀ (i : Fin D.haar.continuous.count) (Ω : Type*) [MeasurableSpace Ω]
        (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ env, IsFiniteMeasure (Γ env)]
        (H : Set M) (_hH : MeasurableSet H) (spatialScale N : ℝ), 0 < N →
        ∀ (rootDomain U : Set
          (Fin (finrank ℝ (P (D.haar.continuous.coefficient i).seedIndex).seed.covector.ker) → ℝ)),
        MeasurableSet U → volume U ≠ ⊤ →
        ∀ threshold : ℝ≥0∞, threshold ≠ 0 → threshold ≠ ⊤ →
        ∀ C : ℝ≥0∞,
        (∫⁻ env, ∫⁻ p, ENNReal.ofReal
          (spatialScale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1))
          ∂Γ env ∂Penv) ≤ C →
        let coord := D.scaledPhysicalBasisPosition i spatialScale
        (∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
          ((Γ env).restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)))
          coord u N z (physicalSceneLongEdgeWindow U threshold)
          ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
          (volume U * (C / ENNReal.ofReal q)) / threshold := by
  obtain ⟨q, hq, radius, hradius, hpoint⟩ :=
    D.exists_uniform_rooted_nearDisplacement_energy_tail hF hcomplete hu ha hinj
  refine ⟨q, hq, radius, hradius, ?_⟩
  intro i Ω _ Penv Γ _ H hH spatialScale N hN rootDomain U hU hUf threshold ht0 htt C henergy
  dsimp only
  let energy := fun env ↦ ∫⁻ p, ENNReal.ofReal
    (spatialScale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ env
  have hq0 : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hfactor : volume U / ENNReal.ofReal q / threshold ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.div_ne_top hUf hq0) ht0
  have heq (env : Ω) : (volume U * (energy env / ENNReal.ofReal q)) / threshold =
      (volume U / ENNReal.ofReal q / threshold) * energy env := by
    simp only [div_eq_mul_inv]
    ac_rfl
  calc
    _ ≤ ∫⁻ env, (volume U * (energy env / ENNReal.ofReal q)) / threshold ∂Penv :=
      lintegral_mono fun env ↦
        (hpoint i (Γ env) H hH spatialScale N hN rootDomain U hU threshold ht0 htt).2
    _ = (volume U / ENNReal.ofReal q / threshold) * ∫⁻ env, energy env ∂Penv := by
      simp_rw [heq]
      exact lintegral_const_mul' _ _ hfactor
    _ ≤ (volume U / ENNReal.ofReal q / threshold) * C := by gcongr
    _ = _ := by simp only [div_eq_mul_inv]; ac_rfl

end PopulationLocalPressureCore
end OTSelector.Reconstruction
