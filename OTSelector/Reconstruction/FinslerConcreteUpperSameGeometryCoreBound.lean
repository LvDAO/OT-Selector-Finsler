import OTSelector.Reconstruction.FinslerConcreteUpperForwardCoreBound
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
theorem original_forward_clockClass_core_bounds_of_geometry
    (i : Fin D.haar.continuous.count) (f : M × M →ᵇ ℝ)
    {A B : Set M} {I : Set ℝ} {globalGap ε : ℝ}
    (Q : (D.haar.continuous.coefficient i).roots → FiniteScalarBins I globalGap)
    (U : (D.haar.continuous.coefficient i).roots → Set (ℚ → M))
    (hsmall : 3 * ε + 2 * ε ^ 2 < 1)
    (houter : ∀ ref j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k →
      ∀ s ∈ (Q ref).cell j, ∀ t ∈ (Q ref).cell k,
        s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1 ∧
        t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
          (D.haar.continuous.coefficient i).window.val.2.1)
    (hregion : ∀ ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ s ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      ∀ t ∈ Icc ((D.haar.continuous.coefficient i).window.val.1 : ℝ)
        (D.haar.continuous.coefficient i).window.val.2.1,
      s < t → D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
        (s, t) ∈ (D.haar.continuous.coefficient i).window.region)
    (hkin : ∀ ref,
      ∀ z ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ z' ∈ (D.haar.continuous.coefficient i).roots ∩ U ref,
      ∀ j k, (D.haar.continuous.coefficient i).clockClassAllowed (Q ref) j k →
      ∀ s ∈ (Q ref).cell j, ∀ t ∈ (Q ref).cell k,
      D.corePoint i (z, s) ∈ A → D.corePoint i (z', t) ∈ B →
      let C := D.haar.continuous.coefficient i
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let vec := (Module.finBasis ℝ S.covector.ker).equivFun (R z' - R z)
      |populationSeedPairDeficit S (s, t) (R z, R z') -
        C.clockClassKinetic (Q ref) ref.val j k vec| ≤
          (3 * ε + 2 * ε ^ 2) * C.clockClassKinetic (Q ref) ref.val j k vec) :
    let C := D.haar.continuous.coefficient i
    ∀ ref, ∃ edgeBound ≥ 0,
      ∀ (m n : ℕ) (zs : Fin m → (ℚ → M)) (zt : Fin n → (ℚ → M))
      (cs : Fin m → Fin (Q ref).count) (ct : Fin n → Fin (Q ref).count)
      (ts : Fin m → ℝ) (tt : Fin n → ℝ),
      (∀ j, zs j ∈ C.roots ∩ U ref) → (∀ k, zt k ∈ C.roots ∩ U ref) →
      (∀ j, ts j ∈ (Q ref).cell (cs j)) → (∀ k, tt k ∈ (Q ref).cell (ct k)) →
      (∀ j, ∃ k, C.clockClassAllowed (Q ref) (cs j) k) →
      (∀ k, ∃ j, C.clockClassAllowed (Q ref) j (ct k)) →
      (∀ j, D.corePoint i (zs j, ts j) ∈ A) →
      (∀ k, D.corePoint i (zt k, tt k) ∈ B) →
      ∀ σ : OTSelector.PartialMatching m n,
      (∀ e ∈ σ.edges, ts e.1 < tt e.2) → ∀ scale : ℝ, 0 ≤ scale → ∀ tilt : ℝ,
      let S := (P C.seedIndex).seed
      let R := populationSeedRootLabelValue S a
      let d := fun j k ↦ (Module.finBasis ℝ S.covector.ker).equivFun (R (zt k) - R (zs j))
      let allowed := Finset.univ.filter (fun e : Fin m × Fin n ↦
        C.clockClassAllowed (Q ref) (cs e.1) (ct e.2))
      let frozen := fun j k ↦ scale * C.clockClassKinetic (Q ref) ref.val (cs j) (ct k) (d j k)
      let probe := fun j k ↦ C.clockClassProbe (Q ref) ref.val ref.property f (cs j) (ct k)
      PartialMatching.IsLegal allowed σ ∧
      PartialMatching.legalMaximumValue allowed (fun j k ↦ frozen j k + tilt * probe j k) ≤
        σ.cost (fun j k ↦ scale * populationSeedPairDeficit S (ts j, tt k) (R (zs j), R (zt k))) /
          (1 - (3 * ε + 2 * ε ^ 2)) + (σ.card : ℝ) * (|tilt| * ‖f‖) +
        ((PartialMatching.legalMaximumCard allowed - σ.card : ℕ) : ℝ) *
          ((2 * ((Q ref).count : ℝ) - 1) * (scale * edgeBound + |tilt| * ‖f‖)) := by
  classical
  dsimp only
  intro ref
  obtain ⟨edgeBound, hEdge0, hEdge⟩ := D.exists_original_clockClass_pair_bound i (Q ref) ref
  refine ⟨edgeBound, hEdge0, ?_⟩
  intro m n zs zt cs ct ts tt hzs hzt hts htt hactiveS hactiveT hAs hBt σ hforward scale hscale tilt
  let C := D.haar.continuous.coefficient i
  let S := (P C.seedIndex).seed
  let R := populationSeedRootLabelValue S a
  let d := fun j k ↦ (Module.finBasis ℝ S.covector.ker).equivFun (R (zt k) - R (zs j))
  let allowed := Finset.univ.filter (fun e : Fin m × Fin n ↦
    C.clockClassAllowed (Q ref) (cs e.1) (ct e.2))
  let frozen := fun j k ↦ scale * C.clockClassKinetic (Q ref) ref.val (cs j) (ct k) (d j k)
  let probe := fun j k ↦ C.clockClassProbe (Q ref) ref.val ref.property f (cs j) (ct k)
  have hSouter (j) : ts j ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    obtain ⟨k, hk⟩ := hactiveS j
    have hp := C.clockClassReference_mem (Q ref) hk
    exact (houter ref (cs j) k hk (ts j) (hts j) _ hp.2.2).1
  have hTouter (k) : tt k ∈ Icc (C.window.val.1 : ℝ) C.window.val.2.1 := by
    obtain ⟨j, hj⟩ := hactiveT k
    have hp := C.clockClassReference_mem (Q ref) hj
    exact (houter ref j (ct k) hj _ hp.2.1 (tt k) (htt k)).2
  have hlegal : PartialMatching.IsLegal allowed σ := by
    intro e he
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact ⟨(ts e.1, tt e.2), hregion ref (zs e.1) (hzs e.1) (zt e.2) (hzt e.2)
      (ts e.1) (hSouter e.1) (tt e.2) (hTouter e.2) (hforward e he) (hAs e.1) (hBt e.2),
      hts e.1, htt e.2⟩
  refine ⟨hlegal, ?_⟩
  have hbound := PartialMatching.legalMaximumValue_le_inverse_relative_core allowed σ hlegal cs
    (fun j k ↦ C.clockClassAllowed (Q ref) j (ct k))
    (fun j k ↦ by simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and])
    (fun j k ↦ scale * populationSeedPairDeficit S (ts j, tt k) (R (zs j), R (zt k)))
    frozen probe hsmall (norm_nonneg f) (by positivity : 0 ≤ scale * edgeBound + |tilt| * ‖f‖)
    ?_ (fun j k ↦ C.clockClassProbe_abs_le (Q ref) ref.val ref.property f (cs j) (ct k)) tilt ?_
  · simpa only [Fintype.card_fin] using hbound
  · intro e he
    have hallowed := (Finset.mem_filter.mp (hlegal he)).2
    have hcost := (hkin ref (zs e.1) (hzs e.1) (zt e.2) (hzt e.2)
      (cs e.1) (ct e.2) hallowed (ts e.1) (hts e.1) (tt e.2) (htt e.2) (hAs e.1) (hBt e.2))
    dsimp only [frozen, d, R, S]
    rw [← mul_sub, abs_mul, abs_of_nonneg hscale]
    exact (mul_le_mul_of_nonneg_left hcost hscale).trans_eq (by ring)
  · intro j k
    have hk := hEdge (cs j) (ct k) (zs j) (hzs j).1 (zt k) (hzt k).1
    calc |frozen j k + tilt * probe j k| ≤ |frozen j k| + |tilt * probe j k| := abs_add_le _ _
      _ ≤ scale * edgeBound + |tilt| * ‖f‖ := by
        apply add_le_add
        · simpa only [frozen, abs_mul, abs_of_nonneg hscale] using
            mul_le_mul_of_nonneg_left hk hscale
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (C.clockClassProbe_abs_le (Q ref) ref.val ref.property f (cs j) (ct k)) (abs_nonneg _)


end OTSelector.Reconstruction.PopulationLocalPressureCore
