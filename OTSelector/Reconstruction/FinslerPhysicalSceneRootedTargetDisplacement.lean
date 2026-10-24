import OTSelector.Reconstruction.FinslerPhysicalSceneRootedDisplacement
import OTSelector.Reconstruction.FinslerPhysicalSceneRootedTargetMass

/-!
# Target-window long-edge control for the actual retained physical plan

Transposition moves only the observed window.  Its squared displacement energy
is unchanged.  The physical near restriction remains the same original event,
so its original forward coercivity certificate is used without reversal.
-/

open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  OTSelector.Probability
open scoped Topology ContDiff ENNReal Classical

noncomputable section
namespace OTSelector.Reconstruction

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section Rooted
variable {ι M : Type*} [Fintype ι] [MeasurableSpace M]

/-- The rooted target lies in the observed window and the same actual squared
spatial displacement is at least the specified threshold. -/
def physicalSceneTargetLongEdgeWindow (U : Set (ι → ℝ)) (r : ℝ≥0∞) :
    Set (((ι → ℝ) × ℝ) × ((ι → ℝ) × ℝ)) :=
  {e | e.2.1 ∈ U ∧ r ≤ ENNReal.ofReal (‖e.2.1 - e.1.1‖ ^ 2)}

theorem measurableSet_physicalSceneTargetLongEdgeWindow
    {U : Set (ι → ℝ)} (hU : MeasurableSet U) (r : ℝ≥0∞) :
    MeasurableSet (physicalSceneTargetLongEdgeWindow U r) :=
  (hU.preimage measurable_snd.fst).inter
    (measurableSet_le measurable_const
      ((measurable_snd.fst.sub measurable_fst.fst).norm.pow_const 2).ennreal_ofReal)

/-- Transposing an actual physical plan turns its rooted target long-edge
window into the existing rooted source long-edge window. -/
theorem physicalSceneRootedPlan_targetLongEdgeWindow_eq_swap_sourceLongEdgeWindow
    (Γ : Measure (M × M)) (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (z : ι → ℝ)
    (U : Set (ι → ℝ)) (hU : MeasurableSet U) (r : ℝ≥0∞) :
    physicalSceneRootedPlan Γ coord u N z (physicalSceneTargetLongEdgeWindow U r) =
      physicalSceneRootedPlan (Γ.map Prod.swap) coord u N z (physicalSceneLongEdgeWindow U r) := by
  have hobs := measurable_physicalSceneRootedObservation coord hcoord u hu z
  have ht := measurableSet_physicalSceneTargetLongEdgeWindow hU r
  have hs := measurableSet_physicalSceneLongEdgeWindow hU r
  unfold physicalSceneRootedPlan
  simp only [Measure.smul_apply, smul_eq_mul]
  congr 1
  rw [Measure.map_apply hobs ht, Measure.map_apply hobs hs,
    Measure.map_apply measurable_swap (hs.preimage hobs)]
  congr 1
  ext p
  simp only [mem_preimage, physicalSceneRootedObservation,
    physicalSceneTargetLongEdgeWindow, physicalSceneLongEdgeWindow, mem_ofPred_eq, Prod.swap]
  rw [norm_sub_rev (coord p.1 - z) (coord p.2 - z)]

/-- The same original squared spatial displacement energy controls Haar
averaged rooted target long-edge mass. -/
theorem lintegral_physicalSceneRootedPlan_targetLongEdgeWindow_le
    (Γ : Measure (M × M)) [IsFiniteMeasure Γ]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (u : M → ℝ) (hu : Measurable u) (N : ℝ) (hN : 0 < N)
    (D U : Set (ι → ℝ)) (hU : MeasurableSet U)
    (r : ℝ≥0∞) (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    (∫⁻ z, physicalSceneRootedPlan Γ coord u N z (physicalSceneTargetLongEdgeWindow U r)
      ∂cavityRootMeasure volume D N) ≤
      (volume U * ∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γ) / r := by
  simp_rw [physicalSceneRootedPlan_targetLongEdgeWindow_eq_swap_sourceLongEdgeWindow
    Γ coord hcoord u hu N _ U hU r]
  have hm : Measurable (fun p : M × M ↦ ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2)) :=
    (((hcoord.comp measurable_snd).sub (hcoord.comp measurable_fst)).norm.pow_const 2).ennreal_ofReal
  have heq : (∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γ.map Prod.swap) =
      ∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γ := by
    rw [lintegral_map hm measurable_swap]
    apply lintegral_congr
    intro p
    change ENNReal.ofReal (‖coord p.1 - coord p.2‖ ^ 2) = _
    rw [norm_sub_rev]
  exact (lintegral_physicalSceneRootedPlan_longEdgeWindow_le (Γ.map Prod.swap)
    coord hcoord u hu N hN D U hU r hr0 hrt).trans_eq (by rw [heq])

/-- An actual event-mass bound also controls its rooted target-window mass;
the optional original source restriction keeps its exact realized columns. -/
theorem lintegral_event_restricted_rooted_targetWindow_expected_le_of_mass
    {Ω : Type*} [MeasurableSpace Ω]
    (Penv : Measure Ω) (Γ : Ω → Measure (M × M)) [∀ w, IsFiniteMeasure (Γ w)]
    (coord : M → (ι → ℝ)) (hcoord : Measurable coord)
    (clock : M → ℝ) (hclock : Measurable clock)
    (N : ℝ) (hN : 0 < N) (rootDomain U : Set (ι → ℝ))
    (hU : MeasurableSet U) (hUf : volume U ≠ ⊤)
    (Q : Set (M × M)) (H : Set M) (C : ℝ≥0∞)
    (hmass : (∫⁻ w, Γ w Q ∂Penv) ≤ C) :
    (∫⁻ w, ∫⁻ z, physicalSceneRootedPlan ((Γ w).restrict (Q ∩ (H ×ˢ univ)))
      coord clock N z {e | e.2.1 ∈ U}
        ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤ volume U * C := by
  calc
    _ ≤ ∫⁻ w, volume U * Γ w Q ∂Penv := by
      apply lintegral_mono
      intro w
      apply (lintegral_physicalSceneRootedPlan_targetWindow_le
        ((Γ w).restrict (Q ∩ (H ×ˢ univ))) coord hcoord clock hclock
        N hN rootDomain U hU).trans
      rw [Measure.restrict_apply_univ]
      exact mul_le_mul_right (measure_mono inter_subset_left) _
    _ = volume U * ∫⁻ w, Γ w Q ∂Penv := lintegral_const_mul' _ _ hUf
    _ ≤ _ := mul_le_mul_right hmass _

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
  (hF : F.IsSmoothStronglyConvex)
  (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
  (hu : let _instSceneMetric : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
  (ha : Measurable a)
  (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val, u x.val)))
include hF hcomplete hu ha hinj

/-- The original common near-event coercivity gives both source-window and
target-window tails for exactly the same retained physical near plan. -/
theorem exists_uniform_rooted_nearDisplacement_both_energy_tails :
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
          (volume U * (globalEnergy / ENNReal.ofReal q)) / threshold) ∧
        ((∫⁻ z, physicalSceneRootedPlan Γnear coord u N z
          (physicalSceneTargetLongEdgeWindow U threshold) ∂cavityRootMeasure volume rootDomain N) ≤
          (volume U * (globalEnergy / ENNReal.ofReal q)) / threshold) := by
  obtain ⟨q, hq, radius, hradius, hsource⟩ :=
    D.exists_uniform_rooted_nearDisplacement_energy_tail hF hcomplete hu ha hinj
  refine ⟨q, hq, radius, hradius, ?_⟩
  intro i Γ _ H hH spatialScale N hN rootDomain U hU threshold ht0 htt
  dsimp only
  let coord := D.scaledPhysicalBasisPosition i spatialScale
  let Γnear := Γ.restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ))
  let globalEnergy := ∫⁻ p, ENNReal.ofReal
    (spatialScale ^ 2 * ((F.lengthEDist p.1 p.2).toReal - u p.2 + u p.1)) ∂Γ
  have hs := hsource i Γ H hH spatialScale N hN rootDomain U hU threshold ht0 htt
  refine ⟨hs.1, hs.2, ?_⟩
  have henergydiv : (∫⁻ p, ENNReal.ofReal (‖coord p.2 - coord p.1‖ ^ 2) ∂Γnear) ≤
      globalEnergy / ENNReal.ofReal q := by
    apply (ENNReal.le_div_iff_mul_le
      (Or.inl (ENNReal.ofReal_ne_zero_iff.mpr hq)) (Or.inl ENNReal.ofReal_ne_top)).mpr
    rw [mul_comm]
    exact hs.1
  let _instSceneMetric : MetricSpace M := F.metricSpace
  have hcoord := D.measurable_scaledPhysicalBasisPosition hF hcomplete hu ha hinj i spatialScale
  refine (lintegral_physicalSceneRootedPlan_targetLongEdgeWindow_le Γnear coord hcoord
    u hu.continuous.measurable N hN rootDomain U hU threshold ht0 htt).trans ?_
  gcongr

/-- The same expected original global slack energy controls both near-window
tails, with one common original near radius and coefficient. -/
theorem exists_uniform_rooted_nearDisplacement_both_expected_tails :
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
        ((∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
          ((Γ env).restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)))
          coord u N z (physicalSceneLongEdgeWindow U threshold)
          ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
          (volume U * (C / ENNReal.ofReal q)) / threshold) ∧
        ((∫⁻ env, ∫⁻ z, physicalSceneRootedPlan
          ((Γ env).restrict (D.nearDisplacementEvent i radius ∩ (H ×ˢ univ)))
          coord u N z (physicalSceneTargetLongEdgeWindow U threshold)
          ∂cavityRootMeasure volume rootDomain N ∂Penv) ≤
          (volume U * (C / ENNReal.ofReal q)) / threshold) := by
  obtain ⟨q, hq, radius, hradius, hpoint⟩ :=
    D.exists_uniform_rooted_nearDisplacement_both_energy_tails hF hcomplete hu ha hinj
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
  have hbound : (∫⁻ env, (volume U * (energy env / ENNReal.ofReal q)) / threshold ∂Penv) ≤
      (volume U * (C / ENNReal.ofReal q)) / threshold := by
    calc
      _ = (volume U / ENNReal.ofReal q / threshold) * ∫⁻ env, energy env ∂Penv := by
        simp_rw [heq]
        exact lintegral_const_mul' _ _ hfactor
      _ ≤ (volume U / ENNReal.ofReal q / threshold) * C := by gcongr
      _ = _ := by simp only [div_eq_mul_inv]; ac_rfl
  constructor
  · exact (lintegral_mono fun env ↦
      (hpoint i (Γ env) H hH spatialScale N hN rootDomain U hU threshold ht0 htt).2.1).trans hbound
  · exact (lintegral_mono fun env ↦
      (hpoint i (Γ env) H hH spatialScale N hN rootDomain U hU threshold ht0 htt).2.2).trans hbound

end PopulationLocalPressureCore
end OTSelector.Reconstruction
