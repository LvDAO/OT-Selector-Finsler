import OTSelector.Reconstruction.FinslerConcreteUpperOriginalModelCoreBounds
import OTSelector.Reconstruction.FinslerConcreteUpperOriginalEndpointAllowed
import OTSelector.Reconstruction.FinslerConcreteUpperAggregateInverseCore
/-! The physical forward-core upper estimate applies to the exact Q/U choices
already used by the original population and its canonical optimizer. -/
open Set Function MeasureTheory ProbabilityTheory Matrix Manifold OTSelector.Geometry Module
open scoped Topology ContDiff ENNReal Matrix.Norms.Operator BigOperators BoundedContinuousFunction Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000
set_option linter.unusedSectionVars false
namespace OTSelector.Reconstruction.PopulationLocalPressureCore
variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  {η₀ η₁ : Measure M} [IsFiniteMeasure η₀] [IsFiniteMeasure η₁]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}
variable (D : PopulationLocalPressureCore P a κ lambda η₀ η₁ ρ₀ ρ₁ v b Good r δ loss)

/-- Arbitrary retained geometry choices are consumed without reselecting the
bins, reference neighborhoods, or original population split. The unscaled edge
constant is produced internally from the original compact seed labels. -/
theorem original_dependent_model_family_bound_of_geometry
    {Cell : Type*} [Fintype Cell] (coreIndex : Cell → Fin D.haar.continuous.count)
    (f : M × M →ᵇ ℝ)
    {A B : Set M} {I : Set ℝ} {globalGap ε : ℝ}
    (Q : Cell → FiniteScalarBins I globalGap)
    (U : Cell → Set (ℚ → M))
    (reference : ∀ c, (D.haar.continuous.coefficient (coreIndex c)).roots)
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1)
    (houter : ∀ c j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
          (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1)
    (hregion : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient (coreIndex c)).window.val.1 : ℝ)
        (D.haar.continuous.coefficient (coreIndex c)).window.val.2.1,
      s < t → D.corePoint (coreIndex c) (z, s) ∈ A → D.corePoint (coreIndex c) (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient (coreIndex c)).window.region)
    (hkin : ∀ c,
      ∀ z ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ z' ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c,
      ∀ j k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c) j k →
      ∀ s ∈ (Q c).cell j, ∀ t ∈ (Q c).cell k,
      D.corePoint (coreIndex c) (z, s) ∈ A → D.corePoint (coreIndex c) (z', t) ∈ B →
      let C := D.haar.continuous.coefficient (coreIndex c)
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let vec := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
      |populationSeedPairDeficit S (s, t) (R z, R z') -
        C.clockClassKinetic (Q c) (reference c).val j k vec| ≤
          (3 * ε + 2 * ε ^ 2) * C.clockClassKinetic (Q c) (reference c).val j k vec)
    (classify : ∀ c, ℝ → Fin (Q c).count) :
    ∃ edgeBound : Cell → ℝ, (∀ c, 0 ≤ edgeBound c) ∧
    ∀ (m n : ℕ) (xs : Fin m → M) (ys : Fin n → M)
      (activeS : Cell → Fin m → Prop) (activeT : Cell → Fin n → Prop),
    (∀ c j, activeS c j →
      a (xs j) ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c ∧
      u (xs j) ∈ (Q c).cell (classify c (u (xs j))) ∧
      (∃ k, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c)
        (classify c (u (xs j))) k) ∧
      D.corePoint (coreIndex c) (a (xs j),u (xs j)) = xs j ∧ xs j ∈ A) →
    (∀ c k, activeT c k →
      a (ys k) ∈ (D.haar.continuous.coefficient (coreIndex c)).roots ∩ U c ∧
      u (ys k) ∈ (Q c).cell (classify c (u (ys k))) ∧
      (∃ j, (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c)
        j (classify c (u (ys k)))) ∧
      D.corePoint (coreIndex c) (a (ys k),u (ys k)) = ys k ∧ ys k ∈ B) →
    ∀ σ : Cell → OTSelector.PartialMatching m n,
    (∀ c e, e ∈ (σ c).edges → activeS c e.1 ∧ activeT c e.2 ∧ u (xs e.1) < u (ys e.2)) →
    ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
    let allowed := fun c ↦ Finset.univ.filter (fun e : Fin m × Fin n ↦
      activeS c e.1 ∧ activeT c e.2 ∧
        D.originalClockClassAllowed (coreIndex c) (Q c) (classify c) (xs e.1) (ys e.2))
    let frozen := fun c j k ↦ scale *
      D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c) (xs j) (ys k)
    let probe := fun c j k ↦
      D.originalClockClassProbe (coreIndex c) (Q c) (reference c) (classify c) f (xs j) (ys k)
    (∀ c, PartialMatching.IsLegal (allowed c) (σ c)) ∧
    (∑ c, PartialMatching.legalMaximumValue (allowed c) (fun j k ↦ frozen c j k + tilt * probe c j k)) ≤
      (∑ c, (σ c).cost (fun j k ↦ scale *
        ((F.lengthEDist (xs j) (ys k)).toReal - u (ys k) + u (xs j)))) /
        (1 - (3 * ε + 2 * ε ^ 2)) +
      (∑ c, ((σ c).card : ℝ)) * (|tilt| * ‖f‖) +
      (∑ c, (2 * ((Q c).count + 1 : ℝ) + 1) * (scale * edgeBound c + |tilt| * ‖f‖)) *
        (∑ c, (((Finset.univ.filter (activeS c)).card : ℝ) - ((σ c).card : ℝ))) := by
  classical
  choose edgeBound hB hedge using fun c ↦
    D.exists_originalClockClass_physical_edge_bound (coreIndex c) (Q c) (reference c) (classify c) f
  refine ⟨edgeBound,hB,?_⟩
  intro m n xs ys activeS activeT hsource htarget σ hσ scale hscale tilt
  dsimp only
  let allowed := fun c ↦ Finset.univ.filter (fun e : Fin m × Fin n ↦
    activeS c e.1 ∧ activeT c e.2 ∧
      D.originalClockClassAllowed (coreIndex c) (Q c) (classify c) (xs e.1) (ys e.2))
  have hlegal (c) : PartialMatching.IsLegal (allowed c) (σ c) := by
    intro e he
    obtain ⟨hs,ht,hf⟩ := hσ c e he
    obtain ⟨hzs,hbins,hactives,hrestores,hAs⟩ := hsource c e.1 hs
    obtain ⟨hzt,hbint,hactivet,hrestoret,hBt⟩ := htarget c e.2 ht
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs,ht,?_⟩
    exact D.original_endpoint_clockClass_allowed_of_geometry (coreIndex c) (fun _ ↦ Q c) (fun _ ↦ U c) (fun _ ↦ houter c) (fun _ ↦ hregion c)
      (reference c) (xs e.1) (ys e.2) (classify c (u (xs e.1))) (classify c (u (ys e.2)))
      hzs hzt hbins hbint hactives hactivet hrestores hrestoret hAs hBt hf
  refine ⟨hlegal,?_⟩
  have hrel : ∀ c e, e ∈ (σ c).edges →
      |scale * ((F.lengthEDist (xs e.1) (ys e.2)).toReal - u (ys e.2) + u (xs e.1)) -
        scale * D.originalClockClassKinetic (coreIndex c) (Q c) (reference c) (classify c)
          (xs e.1) (ys e.2)| ≤
      (3 * ε + 2 * ε ^ 2) * (scale * D.originalClockClassKinetic (coreIndex c) (Q c)
        (reference c) (classify c) (xs e.1) (ys e.2)) := by
    intro c e he
    obtain ⟨hs,ht,_⟩ := hσ c e he
    obtain ⟨hzs,hbins,_,hrestores,hAs⟩ := hsource c e.1 hs
    obtain ⟨hzt,hbint,_,hrestoret,hBt⟩ := htarget c e.2 ht
    have hr := D.originalClockClassKinetic_comparison_of_geometry (coreIndex c) (Q c)
      (reference c) (U c) hsmall (hkin c) (classify c)
      (xs e.1) (ys e.2) hzs hzt hbins hbint (Finset.mem_filter.mp (hlegal c he)).2.2.2
      hrestores hrestoret hAs hBt
    rw [← mul_sub, abs_mul, abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left hr.1 hscale).trans_eq (by ring)
  have h := PartialMatching.sum_gatedClassValue_le_inverse_relative_cores
    (fun c j ↦ classify c (u (xs j))) (fun c k ↦ classify c (u (ys k)))
    (fun c ↦ (D.haar.continuous.coefficient (coreIndex c)).clockClassAllowed (Q c))
    activeS activeT σ hlegal
    (fun _ j k ↦ scale * ((F.lengthEDist (xs j) (ys k)).toReal - u (ys k) + u (xs j)))
    (fun c j k ↦ scale * D.originalClockClassKinetic (coreIndex c) (Q c) (reference c)
      (classify c) (xs j) (ys k))
    (fun c j k ↦ D.originalClockClassProbe (coreIndex c) (Q c) (reference c)
      (classify c) f (xs j) (ys k)) hsmall (norm_nonneg f)
    (fun c ↦ scale * edgeBound c + |tilt| * ‖f‖) (fun c ↦ add_nonneg (mul_nonneg hscale (hB c))
      (mul_nonneg (abs_nonneg tilt) (norm_nonneg f))) hrel
    (fun c j k _ _ _ ↦ (D.haar.continuous.coefficient (coreIndex c)).clockClassProbe_abs_le
      (Q c) (reference c).val (reference c).property f _ _) tilt
    (fun c j k hs ht _ ↦ hedge c (xs j) (ys k) (hsource c j hs).1.1
      (htarget c k ht).1.1 scale hscale tilt)
  simpa only [Fintype.card_fin, originalClockClassAllowed] using h

end OTSelector.Reconstruction.PopulationLocalPressureCore
