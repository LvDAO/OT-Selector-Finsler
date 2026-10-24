import OTSelector.Reconstruction.OriginalIIDFixedCandidateCellEnergyLiminf
import OTSelector.Reconstruction.OriginalIIDCompactMacroFrames
import OTSelector.Reconstruction.OriginalIIDFixedCandidateRootRecovery
import OTSelector.Reconstruction.OriginalIIDTranslatedClockGuard
import OTSelector.Reconstruction.OriginalIIDSameSeedAuxiliaryCells
import OTSelector.Reconstruction.OriginalIIDRawPalmRootLabelLaw
import OTSelector.Reconstruction.OriginalIIDActualClockCutoffLoss

/-! Finite auxiliary cells and original frame owners share the SAME actual
iid physical budget. Each cell retains its own Taylor radius and threshold;
the physical window budget does not depend on those radii. -/
open Set Function Filter MeasureTheory ProbabilityTheory Manifold Module OTSelector.Geometry
  Topology TopologicalSpace
open scoped Topology ContDiff ENNReal NNReal BigOperators
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability OTSelector.PointProcess
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 30000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-- The actual optimizer's physical window readout is jointly measurable in
its original sample and root. The plan is restricted by the same source mask. -/
theorem measurable_originalIID_physical_window_readout
    {M : Type*} [MeasurableSpace M] {q n : ℕ}
    (cost : M → M → ℝ) (hcost : Measurable (Function.uncurry cost))
    (k : ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : M → (Fin q → ℝ)) (hcoord : Measurable coord)
    (upper : M × M → ℝ≥0∞) (hupper : Measurable upper)
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (offset : Fin q → ℝ) (N : ℝ) :
    Measurable (fun p : ((Fin (n+1) → M) × (Fin (n+1) → M)) × (Fin q → ℝ) ↦
      ENNReal.ofReal N * cavityRootWindowReadout
        ((originalIIDOptimalPhysicalPlan (n := n+1) cost k p.1).restrict (H ×ˢ univ))
        (fun e ↦ coord e.1) upper U (p.2+offset)) := by
  classical
  let Γ := fun ξ : (Fin (n+1) → M) × (Fin (n+1) → M) ↦
    (originalIIDOptimalPhysicalPlan (n := n+1) cost k ξ).restrict (H ×ˢ univ)
  have hΓ : Measurable Γ := measurable_physicalPlan_sourceRestriction _
    (measurable_originalIIDOptimalPhysicalPlan cost hcost k) H hH
  let κ : Kernel (((Fin (n+1) → M) × (Fin (n+1) → M)) × (Fin q → ℝ)) (M × M) :=
    ⟨fun p ↦ Γ p.1,hΓ.comp measurable_fst⟩
  letI : IsFiniteKernel κ := ⟨1,by simp,by
    intro p
    change Γ p.1 univ ≤ 1
    rw [Measure.restrict_apply_univ]
    exact prob_le_one⟩
  have hm : Measurable (fun p :
      ((((Fin (n+1) → M) × (Fin (n+1) → M)) × (Fin q → ℝ)) × (M × M)) ↦
      U.indicator (fun _ ↦ upper p.2) (coord p.2.1-(p.1.2+offset))) := by
    change Measurable (fun p :
      ((((Fin (n+1) → M) × (Fin (n+1) → M)) × (Fin q → ℝ)) × (M × M)) ↦
      if coord p.2.1-(p.1.2+offset) ∈ U then upper p.2 else 0)
    exact Measurable.ite
      (hU.preimage ((hcoord.comp measurable_snd.fst).sub (measurable_fst.snd.add_const offset)))
      (hupper.comp measurable_snd) measurable_const
  exact (hm.lintegral_kernel_prod_right' (κ := κ)).const_mul (ENNReal.ofReal N)

/-- Splitting a literal physical readout from a cell's own guard requires
measurability only of the actual physical term; the guard stays unaltered. -/
theorem lintegral_originalIID_physical_window_add_guard
    {M : Type*} [MeasurableSpace M] {q n : ℕ}
    (μ ν : Measure M) (cost : M → M → ℝ)
    (hcost : Measurable (Function.uncurry cost)) (k : ℝ)
    (H : Set M) (hH : MeasurableSet H)
    (coord : M → (Fin q → ℝ)) (hcoord : Measurable coord)
    (upper : M × M → ℝ≥0∞) (hupper : Measurable upper)
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U)
    (offset : Fin q → ℝ) (N B : ℝ) (roots : Set (Fin q → ℝ))
    (guard : ((Fin (n+1) → M) × (Fin (n+1) → M)) → (Fin q → ℝ) → ℝ≥0∞) :
    let law := (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let f := fun ξ root ↦ ENNReal.ofReal N * cavityRootWindowReadout
      ((originalIIDOptimalPhysicalPlan (n := n+1) cost k ξ).restrict (H ×ˢ univ))
      (fun e ↦ coord e.1) upper U (root+offset)
    (∫⁻ ξ, ∫⁻ root, f ξ root+ENNReal.ofReal B*guard ξ root
      ∂cavityRootMeasure volume roots N ∂law) =
      (∫⁻ ξ, ∫⁻ root, f ξ root ∂cavityRootMeasure volume roots N ∂law) +
        ENNReal.ofReal B*(∫⁻ ξ, ∫⁻ root, guard ξ root
          ∂cavityRootMeasure volume roots N ∂law) := by
  intro law f
  letI : SFinite (cavityRootMeasure volume roots N) := by
    unfold cavityRootMeasure
    infer_instance
  have hf : Measurable (Function.uncurry f) :=
    measurable_originalIID_physical_window_readout cost hcost k H hH coord hcoord upper hupper U hU offset N
  have hroot (ξ : (Fin (n+1) → M) × (Fin (n+1) → M)) : Measurable (f ξ) := by
    have hpair : Measurable (fun root : Fin q → ℝ ↦ (ξ,root)) :=
      measurable_const.prodMk measurable_id
    have hsection := hf.comp hpair
    simp only [Function.comp_def,Function.uncurry] at hsection
    exact hsection
  have havg : Measurable (fun ξ ↦ ∫⁻ root, f ξ root ∂cavityRootMeasure volume roots N) :=
    hf.lintegral_prod_right (ν := cavityRootMeasure volume roots N)
  calc
    _ = ∫⁻ ξ, (∫⁻ root, f ξ root ∂cavityRootMeasure volume roots N) +
        ENNReal.ofReal B*(∫⁻ root, guard ξ root ∂cavityRootMeasure volume roots N) ∂law := by
      apply lintegral_congr
      intro ξ
      rw [lintegral_add_left (hroot ξ)]
      rw [lintegral_const_mul' (ENNReal.ofReal B) (guard ξ) ENNReal.ofReal_ne_top]
    _ = _ := by
      rw [lintegral_add_left havg]
      rw [lintegral_const_mul' (ENNReal.ofReal B)
        (fun ξ ↦ ∫⁻ root, guard ξ root ∂cavityRootMeasure volume roots N) ENNReal.ofReal_ne_top]

/-- A finite family of genuine local lower readouts consumes one actual iid
physical budget. Every guard may use its OWN radius; only the physical upper
window, original coordinate and original optimizer are shared. -/
theorem originalIID_finite_cell_readouts_le_shared_budget
    {I M : Type*} [Fintype I] [MeasurableSpace M] {q : ℕ}
    (μ ν : Measure M) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (H : Set M) (hH : MeasurableSet H)
    (coord : ℕ → M → (Fin q → ℝ)) (hcoord : ∀ n, Measurable (coord n))
    (physicalEnergy : ℕ → M × M → ℝ) (he : ∀ n, Measurable (physicalEnergy n))
    (ε B : ℝ) (s : ℕ → ℝ) (hs : ∀ n, s n ≠ 0)
    (center : I → (Fin q → ℝ))
    (domains : ℕ → I → Set (Fin q → ℝ)) (hdomains : ∀ n i, MeasurableSet (domains n i))
    (cells : I → Set (Fin q → ℝ)) (hcells : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j)))
    (U : Set (Fin q → ℝ)) (hU : MeasurableSet U) (hUf : volume U ≠ (∞ : ℝ≥0∞))
    (guard : I → (n : ℕ) → ((Fin (n+1) → M) × (Fin (n+1) → M)) → (Fin q → ℝ) → ℝ≥0∞)
    (guardBudget : I → ℝ≥0∞) (budget : ℝ≥0∞)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (cell : I → ℝ≥0∞) :
    let law := fun n : ℕ ↦ (Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
      (Measure.pi (fun _ : Fin (n+1) ↦ ν))
    let Γ := fun n ξ ↦ originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
    let roots := fun n i ↦ domains n i ∩
      (fun root ↦ center i+physicalSceneMacroscopicRoot (s n) root) ⁻¹' cells i
    (∀ᶠ n in atTop, (∫⁻ ξ, ∫⁻ e, ENNReal.ofReal (physicalEnergy n e) ∂Γ n ξ ∂law n) ≤ budget) →
    (∀ᶠ n in atTop, ∀ i, (∫⁻ ξ, ∫⁻ root, guard i n ξ root
      ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n) ≤ guardBudget i) →
    (∀ i, cell i ≤ liminf (fun r ↦ ∫⁻ ξ, ∫⁻ root,
      ENNReal.ofReal ((m r : ℝ)+1)*cavityRootWindowReadout
        ((Γ (m r) ξ).restrict (H ×ˢ univ)) (fun e ↦ coord (m r) e.1)
        (fun e ↦ ENNReal.ofReal (physicalEnergy (m r) e+ε)) U (root+s (m r) • center i) +
          ENNReal.ofReal B*guard i (m r) ξ root
        ∂cavityRootMeasure volume (roots (m r) i) ((m r : ℝ)+1) ∂law (m r)) atTop) →
    (∑ i, cell i) ≤ volume U*(budget+ENNReal.ofReal ε*μ H) +
      ENNReal.ofReal B*∑ i, guardBudget i := by
  intro law Γ roots henergy hguard hlocal
  let f := fun i n ↦ ∫⁻ ξ, ∫⁻ root,
    ENNReal.ofReal ((n : ℝ)+1)*cavityRootWindowReadout
      ((Γ n ξ).restrict (H ×ˢ univ)) (fun e ↦ coord n e.1)
      (fun e ↦ ENNReal.ofReal (physicalEnergy n e+ε)) U (root+s n • center i) +
        ENNReal.ofReal B*guard i n ξ root
      ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n
  let total := volume U*(budget+ENNReal.ofReal ε*μ H) +
    ENNReal.ofReal B*∑ i, guardBudget i
  have hsplit (i : I) (n : ℕ) : f i n =
      (∫⁻ ξ, ∫⁻ root, ENNReal.ofReal ((n : ℝ)+1)*cavityRootWindowReadout
        ((Γ n ξ).restrict (H ×ˢ univ)) (fun e ↦ coord n e.1)
        (fun e ↦ ENNReal.ofReal (physicalEnergy n e+ε)) U (root+s n • center i)
        ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n) +
      ENNReal.ofReal B*(∫⁻ ξ, ∫⁻ root, guard i n ξ root
        ∂cavityRootMeasure volume (roots n i) ((n : ℝ)+1) ∂law n) :=
    lintegral_originalIID_physical_window_add_guard μ ν (cost n) (hcost n) (k n) H hH
      (coord n) (hcoord n) (fun e ↦ ENNReal.ofReal (physicalEnergy n e+ε))
      ((he n).add_const ε).ennreal_ofReal U hU (s n • center i) ((n : ℝ)+1) B
      (roots n i) (guard i n)
  have hshared : ∀ᶠ n in atTop, (∑ i, f i n) ≤ total := by
    filter_upwards [henergy,hguard] with n hn hg
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib,← Finset.mul_sum]
    apply add_le_add
    · exact (lintegral_originalIID_translated_window_sum_le μ ν n (cost n) (hcost n) (k n)
        H hH (coord n) (hcoord n) (physicalEnergy n) (he n) ε (hs n) center
        (domains n) (hdomains n) cells hcells hdisjoint U hU hUf).trans
        (mul_le_mul_of_nonneg_left (add_le_add hn le_rfl) bot_le)
    · exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ hg i)) bot_le
  have hresult := fixedCandidate_sum_cell_liminf_le_shared_budget cell
    (fun i n ↦ f i (m n)) (fun _ ↦ total) hlocal (hm.eventually hshared)
  simpa only [liminf_const] using hresult

/-- The actual clock deficit is paid by the original unnormalized Palm root
mass. The clipped observable and kernel are fixed throughout this estimate. -/
theorem lintegral_clipped_kernel_le_clock_cutoff_add_root_mass
    {C X : Type*} [MeasurableSpace C] [MeasurableSpace X]
    (η : Measure C) (κ : Kernel C X) [IsSFiniteKernel κ]
    (clock : X → ℝ × ℝ) (hclock : Measurable clock)
    (ψ : C(ℝ × ℝ,ℝ)) (hrange : ∀ p, ψ p ∈ Icc 0 1)
    (energy : C × X → ℝ≥0∞) (henergy : Measurable energy)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (loss : ℝ≥0∞)
    (A : Set C) (hA : MeasurableSet A)
    (hmiss : ∀ᵐ c ∂η.restrict A,
      (∫⁻ x, ENNReal.ofReal (1-ψ (clock x)) ∂κ c) ≤ κ c univ*loss) :
    (∫⁻ c in A, ∫⁻ x, min B (energy (c,x)) ∂κ c ∂η) ≤
      (∫⁻ c in A, ∫⁻ x, ENNReal.ofReal (ψ (clock x))*min B (energy (c,x)) ∂κ c ∂η) +
        B*loss*fixedCandidateRootMass η κ A := by
  have hweight : Measurable (fun p : C × X ↦
      ENNReal.ofReal (ψ (clock p.2))*min B (energy p)) :=
    ((ψ.continuous.measurable.comp (hclock.comp measurable_snd)).ennreal_ofReal).mul
      (measurable_const.min henergy)
  have hm : Measurable (fun c ↦ κ c univ) := κ.measurable_coe MeasurableSet.univ
  calc
    _ ≤ ∫⁻ c in A, (∫⁻ x, ENNReal.ofReal (ψ (clock x))*min B (energy (c,x)) ∂κ c) +
        (B*loss)*(κ c univ) ∂η := by
      apply lintegral_mono_ae
      filter_upwards [hmiss] with c hc
      apply (lintegral_min_le_clock_cutoff_add_missed (κ c) clock hclock ψ hrange
        (fun x ↦ energy (c,x)) (henergy.comp (measurable_const.prodMk measurable_id)) B hB).trans
      apply add_le_add le_rfl
      exact (mul_le_mul_of_nonneg_left hc bot_le).trans_eq (by ac_rfl)
    _ = _ := by
      rw [lintegral_add_left (hweight.lintegral_kernel_prod_right' (κ := κ)),
        lintegral_const_mul _ hm,fixedCandidateRootMass,withDensity_apply _ hA]

/-- Clock facts holding for the actual Palm root mass suffice even where
that mass has zero density in the original root volume. Zero-mass kernels
contribute zero, so no positive lower intensity bound is required. -/
theorem lintegral_clipped_kernel_le_clock_cutoff_add_root_mass_of_weighted_ae
    {C X : Type*} [MeasurableSpace C] [MeasurableSpace X]
    (η : Measure C) (κ : Kernel C X) [IsSFiniteKernel κ]
    (clock : X → ℝ × ℝ) (hclock : Measurable clock)
    (ψ : C(ℝ × ℝ,ℝ)) (hrange : ∀ p, ψ p ∈ Icc 0 1)
    (energy : C × X → ℝ≥0∞) (henergy : Measurable energy)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (loss : ℝ≥0∞)
    (A : Set C) (hA : MeasurableSet A)
    (hmiss : ∀ᵐ c ∂(fixedCandidateRootMass η κ).restrict A,
      (∫⁻ x, ENNReal.ofReal (1-ψ (clock x)) ∂κ c) ≤ κ c univ*loss) :
    (∫⁻ c in A, ∫⁻ x, min B (energy (c,x)) ∂κ c ∂η) ≤
      (∫⁻ c in A, ∫⁻ x, ENNReal.ofReal (ψ (clock x))*min B (energy (c,x)) ∂κ c ∂η) +
        B*loss*fixedCandidateRootMass η κ A := by
  have hm : Measurable (fun c ↦ κ c univ) := κ.measurable_coe MeasurableSet.univ
  rw [fixedCandidateRootMass,restrict_withDensity hA] at hmiss
  have hpositive := (ae_withDensity_iff hm).mp hmiss
  apply lintegral_clipped_kernel_le_clock_cutoff_add_root_mass η κ clock hclock ψ hrange
    energy henergy B hB loss A hA
  filter_upwards [hpositive] with c hc
  by_cases hz : κ c univ = 0
  · have hzero : κ c = 0 := Measure.measure_univ_eq_zero.mp hz
    simp [hzero]
  · exact hc hz

/-- Disjoint measured cells pay their common original clock loss once,
weighted by the actual union root mass, with no cell-count multiplier. -/
theorem sum_clipped_kernel_le_clock_cutoffs_add_union_root_mass
    {I C X : Type*} [Fintype I] [MeasurableSpace C] [MeasurableSpace X]
    (η : Measure C) (κ : Kernel C X) [IsSFiniteKernel κ]
    (clock : X → ℝ × ℝ) (hclock : Measurable clock)
    (ψ : I → C(ℝ × ℝ,ℝ)) (hrange : ∀ i p, ψ i p ∈ Icc 0 1)
    (energy : C × X → ℝ≥0∞) (henergy : Measurable energy)
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (loss : ℝ≥0∞)
    (cells : I → Set C) (hmeas : ∀ i, MeasurableSet (cells i))
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j)))
    (hmiss : ∀ i, ∀ᵐ c ∂(fixedCandidateRootMass η κ).restrict (cells i),
      (∫⁻ x, ENNReal.ofReal (1-ψ i (clock x)) ∂κ c) ≤ κ c univ*loss) :
    (∑ i, ∫⁻ c in cells i, ∫⁻ x, min B (energy (c,x)) ∂κ c ∂η) ≤
      (∑ i, ∫⁻ c in cells i, ∫⁻ x, ENNReal.ofReal (ψ i (clock x))*
        min B (energy (c,x)) ∂κ c ∂η) +
      B*loss*fixedCandidateRootMass η κ (⋃ i, cells i) := by
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦
    lintegral_clipped_kernel_le_clock_cutoff_add_root_mass_of_weighted_ae
      η κ clock hclock (ψ i) (hrange i) energy henergy B hB loss (cells i) (hmeas i) (hmiss i))
  have hmass : fixedCandidateRootMass η κ (⋃ i, cells i) =
      ∑ i, fixedCandidateRootMass η κ (cells i) := by
    simpa only [tsum_fintype] using
      measure_iUnion hdisjoint hmeas (μ := fixedCandidateRootMass η κ)
  simpa only [Finset.sum_add_distrib,← Finset.mul_sum,hmass] using hsum



/-- Disjoint actual auxiliary cells split along finitely many original frame
owners, without any boundary-null or integrand measurability assumption. -/
theorem exists_finite_original_owner_cell_partition
    {I : Type*} [Fintype I] {q : ℕ}
    (K : Set (Fin q → ℝ)) (hK : IsCompact K)
    (cells : I → Set (Fin q → ℝ)) (hmeas : ∀ i, MeasurableSet (cells i))
    (hsub : ∀ i, cells i ⊆ K)
    (hdisjoint : Pairwise (fun i j ↦ Disjoint (cells i) (cells j))) :
    ∃ J : ℕ, 0 < J ∧
      (∀ p : I × Fin J, MeasurableSet
        (cells p.1 ∩ originalMacroFrameOwner q K p.2.val)) ∧
      Pairwise (fun p r : I × Fin J ↦ Disjoint
        (cells p.1 ∩ originalMacroFrameOwner q K p.2.val)
        (cells r.1 ∩ originalMacroFrameOwner q K r.2.val)) ∧
      (∀ p : I × Fin J, cells p.1 ∩ originalMacroFrameOwner q K p.2.val ⊆ K) ∧
      ∀ readout : I → (Fin q → ℝ) → ℝ≥0∞,
      (∑ i, ∫⁻ c in cells i, readout i c ∂volume) =
        ∑ p : I × Fin J, ∫⁻ c in cells p.1 ∩ originalMacroFrameOwner q K p.2.val,
          readout p.1 c ∂volume := by
  classical
  obtain ⟨J,hJ,hcover,htail,hunion⟩ :=
    exists_originalMacroFrameOwner_finite_cover_of_isCompact hK
  have howners : Pairwise (fun f g : Fin J ↦ Disjoint
      (originalMacroFrameOwner q K f.val) (originalMacroFrameOwner q K g.val)) := by
    intro f g hfg
    exact pairwiseDisjoint_originalMacroFrameOwner q K (fun h ↦ hfg (Fin.ext h))
  have hp : Pairwise (fun p r : I × Fin J ↦ Disjoint
      (cells p.1 ∩ originalMacroFrameOwner q K p.2.val)
      (cells r.1 ∩ originalMacroFrameOwner q K r.2.val)) := by
    rintro ⟨i,f⟩ ⟨k,g⟩ hne
    by_cases hik : i = k
    · subst k
      have hfg : f ≠ g := by intro h; exact hne (by cases h; rfl)
      exact (howners hfg).mono inter_subset_right inter_subset_right
    · exact (hdisjoint hik).mono inter_subset_left inter_subset_left
  refine ⟨J,hJ,fun p ↦ (hmeas p.1).inter
    (measurableSet_originalMacroFrameOwner q hK.measurableSet p.2.val),hp,
    fun p ↦ inter_subset_left.trans (hsub p.1),?_⟩
  intro readout
  have hsplit (i : I) : (∫⁻ c in cells i, readout i c ∂volume) =
      ∑ f : Fin J, ∫⁻ c in cells i ∩ originalMacroFrameOwner q K f.val,
        readout i c ∂volume := by
    have heq : (⋃ f : Fin J, cells i ∩ originalMacroFrameOwner q K f.val) = cells i := by
      rw [← inter_iUnion,hunion,inter_eq_left.mpr (hsub i)]
    conv_lhs => rw [← heq]
    simpa only [tsum_fintype] using lintegral_iUnion
      (μ := (volume : Measure (Fin q → ℝ)))
      (s := fun f : Fin J ↦ cells i ∩ originalMacroFrameOwner q K f.val)
      (fun (f : Fin J) ↦ (hmeas i).inter (measurableSet_originalMacroFrameOwner q hK.measurableSet f.val))
      (fun f g hfg ↦ (howners hfg).mono inter_subset_right inter_subset_right) (readout i)
  simp_rw [hsplit]
  exact (Fintype.sum_prod_type (fun p : I × Fin J ↦
    ∫⁻ c in cells p.1 ∩ originalMacroFrameOwner q K p.2.val, readout p.1 c ∂volume)).symm


variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [T2Space M] [PreconnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {F : ContinuousFinslerNorm E M} {u : M → ℝ}
  {P : ℕ → F.CalibratedSeedWindow u} {a : M → (ℚ → M)}
  {κ : ∀ j, Measure (P j).seed.covector.ker} {lambda : Measure (ℚ → M)}
  [IsFiniteMeasure lambda] [∀ j, SigmaFinite (κ j)]
  {μ ν : Measure M} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  {ρ₀ ρ₁ : M → ℝ} {v : ℕ → E → ℝ} {b : (ℚ → M) × ℝ → M}
  {Good : (ℚ → M) → Prop} {r : ℝ} {δ loss : ℝ≥0∞}

variable (j : ℕ)
set_option quotPrecheck false
local notation "qj" => finrank ℝ (P j).seed.covector.ker
local notation "Vj" => OriginalIIDSeedCoordinateSpace P j
local notation "Xj" => Vj × ℝ
local notation "Macroj" => OriginalIIDMaskedMacroCarrier (0 : Xj)
attribute [local instance] iidFixedCandidatePalmPointStandardBorel
  iidFixedCandidatePalmPlanPolish iidFixedCandidatePalmInputPolish
  iidFixedCandidatePalmPlanNonempty iidFixedCandidatePalmInputNonempty
  iidFixedCandidatePalmConfigurationTopology iidFixedCandidatePalmConfigurationBorel
  iidFixedCandidatePalmConfigurationPolish

/-- The actual auxiliary core produces its own literal guard and true local
lower readouts in a fixed original seed. Radii may differ across finite cells;
no guard or lower-energy conclusion is assumed. -/
theorem PopulationLocalPressureCore.exists_originalIID_fixed_seed_auxiliary_lower_readout
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)
    (i : Fin D.haar.continuous.count)
    (hseed : (D.haar.continuous.coefficient i).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (ψ : C(ℝ × ℝ,ℝ)) (hψrange : ∀ clocks, ψ clocks ∈ Icc 0 1)
    (hψsupport : tsupport ψ ⊆ (D.haar.continuous.coefficient i).window.region)
    (K : Set Vj) (hK : MeasurableSet K)
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj)) (frame : ℕ)
    (hroot : (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) {ε : ℝ} (hε : 0 < ε)
    (η : ℝ≥0∞) (hη : 0 < η) :
    let center := originalMacroFrameCenter qj frame
    let scale := physicalSceneCanonicalHaarScale qj
    let tag := fun n ↦ physicalSceneMacroscopicRoot (scale n)
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let shifted := fun n x ↦ coord n x-scale n • center
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let auxCore := originalIIDSeedCoordinateCast (P := P) hseed ''
      (D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots)
    Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH (shifted (m n))
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable)) →
    ∃ guard : (n : ℕ) → ((Fin (n+1) → M) × (Fin (n+1) → M)) → Vj → ℝ≥0∞,
      (∀ᶠ n in atTop, ∀ A : Set Vj, MeasurableSet A → A ⊆ auxCore →
        (∫⁻ ξ, ∫⁻ root, guard n ξ root
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain qj n ∩ tag n ⁻¹'
            ((fun w ↦ center+w) ⁻¹' A)) ((n : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ η) ∧
      ∀ A : Set Vj, MeasurableSet A → A ⊆ originalMacroFrameOwner qj K frame → A ⊆ auxCore →
      ∀ B : ℝ,
      (∫⁻ c in A, ∫⁻ mark, ENNReal.ofReal (ψ mark.1)*min (ENNReal.ofReal B)
        (ENNReal.ofReal (matrixQuadratic
          (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,mark.1)) mark.2))
        ∂cubePalm (Fin qj) (physicalScenePairCampbell
          ((originalIIDWholeCoreSceneKernel K hK Q c).map Prod.fst)) ∂volume) ≤
        liminf (fun r ↦ ∫⁻ ξ, ∫⁻ root,
          ENNReal.ofReal ((m r : ℝ)+1)*cavityRootWindowReadout
            ((originalIIDOptimalPhysicalPlan (n := m r+1) (cost (m r)) (k (m r)) ξ).restrict (H ×ˢ univ))
            (fun p ↦ coord (m r) p.1)
            (fun p ↦ ENNReal.ofReal ((scale (m r))^2 *
              ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1)+ε)) U (root+scale (m r) • center) +
          ENNReal.ofReal B*guard (m r) ξ root
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain qj (m r) ∩ tag (m r) ⁻¹'
            ((fun w ↦ center+w) ⁻¹' A)) ((m r : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (m r+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (m r+1) ↦ ν))) atTop := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro center scale tag coord shifted H hH auxCore hweak
  obtain ⟨R,hR,hRW,hsmall⟩ := D.exists_eventually_originalIID_translated_clock_guard_small
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist i cost hcost k hq center budget hbudget henergy
    hU.measurableSet W hW η hη
  let guard := fun (n : ℕ) (ξ : (Fin (n+1) → M) × (Fin (n+1) → M))
      (root : D.coreSpatialCoordinateSpace i) ↦ ENNReal.ofReal ((n : ℝ)+1)*
    D.originalTaylorGuardMass i R (scale n) U
      (physicalSceneOriginalMacroRootValue (P := P) (a := a)
        (D.haar.continuous.coefficient i).seedIndex (center+tag n root)) (root+scale n • center)
      (((originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ).restrict (H ×ˢ univ)).restrict
        {p | (u p.1,u p.2) ∈ (D.haar.continuous.coefficient i).window.region})
  refine ⟨guard,?_,?_⟩
  · filter_upwards [hsmall] with n hn
    intro A hAm hAsub
    have hnative : A ⊆ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots := by
      simpa only [auxCore,originalIIDSeedCoordinateCast_rfl,image_id'] using hAsub
    exact hn ((fun w ↦ center+w) ⁻¹' A)
      (hAm.preimage (measurable_const.add measurable_id)) (preimage_mono hnative)
  · intro A hAm howner hAsub B
    have hnative : A ⊆ D.coreMacroLabel i '' (D.haar.continuous.coefficient i).roots := by
      simpa only [auxCore,originalIIDSeedCoordinateCast_rfl,image_id'] using hAsub
    exact D.fixed_candidate_owner_clock_cutoff_energy_liminf i hF hcomplete hu ha hinj horder
      hq H hH ψ hψrange hψsupport R hR hε cost hcost k K hK Q frame hroot m hm hweak
      A hAm howner hnative B U hU hcube

/-- All actual auxiliary cells of a finite original-seed family consume one
physical energy budget. The original frame partition and every actual guard
are constructed internally, then their fixed-height errors tend to zero. -/
theorem PopulationLocalPressureCore.originalIID_finite_weighted_auxiliary_cells_le
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)

    {I : Type*} [Fintype I]
    (index : I → Fin D.haar.continuous.count)
    (hseed : ∀ i, (D.haar.continuous.coefficient (index i)).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (ψ : I → C(ℝ × ℝ,ℝ)) (hψrange : ∀ i clocks, ψ i clocks ∈ Icc 0 1)
    (hψsupport : ∀ i, tsupport (ψ i) ⊆
      (D.haar.continuous.coefficient (index i)).window.region)
    (K : Set Vj) (hK : IsCompact K)
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞))
    (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W)
    (cells : I → Set Vj) (hcells : ∀ i, MeasurableSet (cells i))
    (hsubK : ∀ i, cells i ⊆ K)
    (hsubaux : ∀ i, cells i ⊆ originalIIDSeedCoordinateCast (P := P) (hseed i) ''
      (D.coreMacroLabel (index i) '' (D.haar.continuous.coefficient (index i)).roots))
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (cells i) (cells k))) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →
    ∀ B : ℝ,
      (∑ i, ∫⁻ c in cells i, ∫⁻ mark, ENNReal.ofReal (ψ i mark.1)*min (ENNReal.ofReal B)
        (ENNReal.ofReal (matrixQuadratic
          (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,mark.1)) mark.2))
        ∂originalIIDRawPairPalmKernel (originalIIDWholeCoreSceneKernel K hK.measurableSet Q) c ∂volume) ≤
      volume U*budget := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  intro scale coord H hH hweak B
  let raw := originalIIDRawPairPalmKernel (originalIIDWholeCoreSceneKernel K hK.measurableSet Q)
  let readout := fun i c ↦ ∫⁻ mark, ENNReal.ofReal (ψ i mark.1)*min (ENNReal.ofReal B)
    (ENNReal.ofReal (matrixQuadratic
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,mark.1)) mark.2)) ∂raw c
  obtain ⟨J,hJ,hpairmeas,hpairdisjoint,hpairsub,hpartition⟩ :=
    exists_finite_original_owner_cell_partition K hK cells hcells hsubK hdisjoint
  let paircell := fun p : I × Fin J ↦ cells p.1 ∩ originalMacroFrameOwner qj K p.2.val
  let center := fun p : I × Fin J ↦ originalMacroFrameCenter qj p.2.val
  have hperturb (ε : ℝ) (hε : 0 < ε) (η : ℝ≥0∞) (hη : 0 < η) :
      (∑ i, ∫⁻ c in cells i, readout i c ∂volume) ≤
        volume U*(budget+ENNReal.ofReal ε*μ H)+
          ENNReal.ofReal B*∑ _p : I × Fin J, η := by
    have hex (p : I × Fin J) :=
      D.exists_originalIID_fixed_seed_auxiliary_lower_readout (j := j)
        hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
        hA hB hμ hν hreg hμreg hface hgap hdist (index p.1) (hseed p.1)
        cost hcost k hq budget hbudget henergy (ψ p.1) (hψrange p.1) (hψsupport p.1)
        K hK.measurableSet Q p.2.val (hroot p.2.val) m hm U hU hcube W hW hε η hη
        (hweak p.2.val)
    choose guard hguards hlocal using hex
    have hsmall : ∀ᶠ n in atTop, ∀ p : I × Fin J,
        (∫⁻ ξ, ∫⁻ root, guard p n ξ root
          ∂cavityRootMeasure volume (physicalSceneCanonicalHaarDomain qj n ∩
            (fun root ↦ center p+physicalSceneMacroscopicRoot (scale n) root) ⁻¹' paircell p)
            ((n : ℝ)+1)
          ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
            (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ η := by
      have hall := Filter.eventually_all.mpr hguards
      filter_upwards [hall] with n hn
      intro p
      exact hn p (paircell p) (hpairmeas p) (inter_subset_left.trans (hsubaux p.1))
    have hbound := originalIID_finite_cell_readouts_le_shared_budget μ ν cost hcost k H hH
      coord (fun n ↦ measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale n))
      (fun n p ↦ (scale n)^2*((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
      (fun n ↦ (F.measurable_distance_slack hu).const_mul ((scale n)^2))
      ε B scale (fun n ↦ (physicalSceneCanonicalHaarScale_pos qj n).ne') center
      (fun n _ ↦ physicalSceneCanonicalHaarDomain qj n) (fun _ _ ↦ measurableSet_Icc)
      paircell hpairmeas hpairdisjoint U hU.measurableSet hUf guard (fun _ ↦ η) budget
      m hm (fun p ↦ ∫⁻ c in paircell p, readout p.1 c ∂volume) henergy hsmall
      (fun p ↦ by
        simpa only [readout,raw,originalIIDRawPairPalmKernel_apply,center,scale,coord,H,Set.preimage_preimage,Function.comp_def] using
          hlocal p (paircell p) (hpairmeas p) inter_subset_right
            (inter_subset_left.trans (hsubaux p.1)) B)
    rw [← hpartition readout] at hbound
    exact hbound
  let e := fun n : ℕ ↦ (1 / ((n : ℝ)+1))
  have hepos (n : ℕ) : 0 < e n := by positivity
  have he : Tendsto e atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hee : Tendsto (fun n ↦ ENNReal.ofReal (e n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp he
  have hsum : Tendsto (fun n ↦ ∑ _p : I × Fin J, ENNReal.ofReal (e n)) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum (s := (Finset.univ : Finset (I × Fin J))) (fun _ _ ↦ hee)
  have hright : Tendsto (fun n ↦ volume U*(budget+ENNReal.ofReal (e n)*μ H)+
      ENNReal.ofReal B*∑ _p : I × Fin J, ENNReal.ofReal (e n)) atTop (𝓝 (volume U*budget)) := by
    have hm := ENNReal.Tendsto.mul_const hee (b := μ H) (Or.inr (measure_ne_top μ H))
    have ha := (tendsto_const_nhds (x := budget)).add hm
    have hfirst := ENNReal.Tendsto.const_mul ha (a := volume U) (Or.inr hUf)
    have hlast := ENNReal.Tendsto.const_mul hsum (a := ENNReal.ofReal B)
      (Or.inr ENNReal.ofReal_ne_top)
    simpa only [zero_mul,add_zero,mul_zero] using hfirst.add hlast
  exact ge_of_tendsto hright (Eventually.of_forall (fun n ↦
    hperturb (e n) (hepos n) (ENNReal.ofReal (e n)) (ENNReal.ofReal_pos.mpr (hepos n))))


/-- Removing all auxiliary clock cutoffs costs only their true original clock
deficit times the original unnormalized root mass. The finite auxiliary cells
still use the SAME whole-core candidate and one actual physical budget. -/
theorem PopulationLocalPressureCore.originalIID_auxiliary_clipped_cell_sum_le
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)


    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.continuous.count)
    (hseed₀ : (D₀.continuous.coefficient i₀).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (ψ : Fin D.haar.continuous.count → C(ℝ × ℝ,ℝ))
    (hψrange : ∀ i clocks, ψ i clocks ∈ Icc 0 1)
    (hψsupport : ∀ i, tsupport (ψ i) ⊆ (D.haar.continuous.coefficient i).window.region)
    (clockLoss : ℝ≥0∞)
    (hclock : ∀ i, ∀ᵐ z ∂(μ.map a).restrict (D.haar.continuous.coefficient i).roots,
      ∀ π : Measure (ℝ × ℝ), Vlasov.IsCoupling π (condDistrib u a μ z) (condDistrib u a ν z) →
        (∀ᵐ p ∂π, p.1 ≤ p.2) → (∫⁻ p, ENNReal.ofReal (1-ψ i p) ∂π) ≤ clockLoss)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.continuous.coefficient i₀).seedIndex '' (D₀.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞)) (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let Λ := originalIIDWholeCoreSceneKernel K hK.measurableSet Q
    let ref := fun c : Vj ↦ a ((P j).seed.curve
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) j
    ∀ (input : Vj → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint qj) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint qj))),
    (∀ᵐ c ∂(volume : Measure Vj).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →
    ∀ B : ℝ,
      (∑ i : Fin D.haar.continuous.count,
        ∫⁻ c in originalIIDSeedCoordinateCast (P := P) hseed₀ ''
          originalIIDAuxiliaryCell (D₀.continuous.coefficient i₀) (D.haar.continuous.coefficient i),
          ∫⁻ mark, min (ENNReal.ofReal B) (ENNReal.ofReal (matrixQuadratic
            (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,mark.1)) mark.2))
            ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤
        volume U*budget + ENNReal.ofReal B*clockLoss*(μ.map a) (D₀.continuous.coefficient i₀).roots := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro scale coord H hH Λ ref root input hprofile hweak B
  let C₀ := D₀.continuous.coefficient i₀
  let S₀ := (P C₀.seedIndex).seed
  let e₀ := (Module.finBasis ℝ S₀.covector.ker).equivFunL
  let R₀ := populationSeedRootLabelValue S₀ a
  let I := OriginalIIDSameSeedAuxiliaryIndex C₀ D.haar
  let cells := fun i : I ↦ originalIIDAuxiliaryCell C₀ (D.haar.continuous.coefficient i.val)
  let energy := fun p : (OriginalIIDSeedCoordinateSpace P C₀.seedIndex) × PhysicalPairPalmMark (Fin (finrank ℝ S₀.covector.ker)) ↦
    ENNReal.ofReal (matrixQuadratic
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a) C₀.seedIndex (p.1,p.2.1)) p.2.2)
  simp only [originalIIDSeedCoordinateCast_rfl,image_id'] at hK₀ ⊢
  have hKbasis : K = e₀ '' (R₀ '' C₀.roots) := by
    rw [hK₀,image_image]
    rfl
  have hcells (i : I) : MeasurableSet (cells i) := by
    dsimp only [cells]
    rw [originalIIDAuxiliaryCell_eq_basis_image]
    exact e₀.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (D₀.measurable_cell_label_image hcomplete i₀
        (C₀.roots_compact.measurableSet.inter
          (D.haar.continuous.coefficient i.val).roots_compact.measurableSet) inter_subset_left)
  have hsubK (i : I) : cells i ⊆ K := by
    rw [hK₀]
    exact image_mono inter_subset_left
  have hsubaux (i : I) : cells i ⊆ originalIIDSeedCoordinateCast (P := P) i.property ''
      (D.coreMacroLabel i.val '' (D.haar.continuous.coefficient i.val).roots) :=
    originalIIDAuxiliaryCell_subset_cast_aux_core C₀ _ i.property
  have hdisjoint : Pairwise (fun i k : I ↦ Disjoint (cells i) (cells k)) := by
    intro i k hik
    dsimp only [cells]
    rw [originalIIDAuxiliaryCell_eq_basis_image,originalIIDAuxiliaryCell_eq_basis_image]
    simp only [image_image]
    exact ((D.haar.continuous.disjoint (fun h ↦ hik (Subtype.ext h))).mono
      inter_subset_right inter_subset_right).image (D₀.original_coordinate_injOn i₀)
        inter_subset_left inter_subset_left
  have hweighted := D.originalIID_finite_weighted_auxiliary_cells_le
    (j := C₀.seedIndex) hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist (fun i : I ↦ i.val) (fun i ↦ i.property)
    cost hcost k hq budget hbudget henergy (fun i : I ↦ ψ i.val)
    (fun i ↦ hψrange i.val) (fun i ↦ hψsupport i.val)
    K hK Q hroot m hm U hU hcube hUf W hW cells hcells hsubK hsubaux hdisjoint hweak B
  have henergyMeas : Measurable energy := by
    exact (continuous_matrixQuadratic.measurable.comp
      (((measurable_physicalSceneOriginalMacroCoefficient hF hcomplete hu ha hinj C₀.seedIndex).comp
        (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)).ennreal_ofReal
  have hprofile₀ : ∀ᵐ c ∂(volume : Measure (OriginalIIDSeedCoordinateSpace P C₀.seedIndex)).restrict
      (e₀ '' (R₀ '' C₀.roots)), OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) C₀.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c) := by
    rwa [← hKbasis]
  have hmiss (i : I) : ∀ᵐ c ∂(fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ)).restrict (cells i),
      (∫⁻ mark, ENNReal.ofReal (1-ψ i.val mark.1) ∂originalIIDRawPairPalmKernel Λ c) ≤
        originalIIDRawPairPalmKernel Λ c univ*clockLoss := by
    have h := D₀.ae_fixed_candidate_raw_clock_cutoff_missed_le hF hcomplete hu ha hinj i₀
      Λ gap hgap input hprofile₀ (ψ i.val) (hψrange i.val) clockLoss
      (C₀.roots_compact.measurableSet.inter (D.haar.continuous.coefficient i.val).roots_compact.measurableSet)
      inter_subset_left (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hclock i.val))
    simpa only [cells,originalIIDAuxiliaryCell_eq_basis_image] using h
  have hmass : fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ) (⋃ i : I, cells i) ≤
      (μ.map a) C₀.roots := by
    have hfull := D₀.fixed_candidate_raw_palm_mass_eq_label hF hcomplete hu ha hinj i₀
      Λ gap (fun c ↦ condDistrib u a μ (root c)) (fun c ↦ condDistrib u a ν (root c))
      (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) input hprofile₀
      C₀.roots_compact.measurableSet Subset.rfl
    calc
      _ ≤ fixedCandidateRootMass volume (originalIIDRawPairPalmKernel Λ) K :=
        measure_mono (iUnion_subset hsubK)
      _ = _ := by rw [hKbasis]; exact hfull
  rw [sum_originalIIDAuxiliaryCell_eq_same_seed C₀ D.haar
    (fun A ↦ ∫⁻ c in A, ∫⁻ mark, min (ENNReal.ofReal B) (energy (c,mark))
      ∂originalIIDRawPairPalmKernel Λ c ∂volume) (by simp)]
  exact (sum_clipped_kernel_le_clock_cutoffs_add_union_root_mass volume
    (originalIIDRawPairPalmKernel Λ) Prod.fst measurable_fst (fun i : I ↦ ψ i.val)
    (fun i ↦ hψrange i.val) energy henergyMeas (ENNReal.ofReal B) ENNReal.ofReal_ne_top
    clockLoss cells hcells hdisjoint hmiss).trans
      (add_le_add hweighted (mul_le_mul_of_nonneg_left hmass bot_le))

/-- True original accuracy refinement removes clock and uncovered-root losses
at each fixed height on the SAME candidate. Auxiliary cores, clocks and errors
are produced from the original population data; no energy conclusion is assumed. -/
theorem originalIID_fixed_candidate_clipped_energy_le
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)


    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationHaarPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.continuous.count)
    (hseed₀ : (D₀.continuous.coefficient i₀).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (hGood : ∀ᵐ z ∂μ.map a, Good z)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.continuous.coefficient i₀).seedIndex '' (D₀.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞)) (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let Λ := originalIIDWholeCoreSceneKernel K hK.measurableSet Q
    let ref := fun c : Vj ↦ a ((P j).seed.curve
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) j
    ∀ (input : Vj → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint qj) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint qj))),
    (∀ᵐ c ∂(volume : Measure Vj).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →

    ∀ B : ℝ,
      (∫⁻ c in K, ∫⁻ mark, min (ENNReal.ofReal B) (ENNReal.ofReal (matrixQuadratic
        (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,mark.1)) mark.2))
        ∂originalIIDRawPairPalmKernel Λ c ∂volume) ≤ volume U*budget := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : Nonempty M := nonempty_of_isProbabilityMeasure μ
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro scale coord H hH Λ ref root input hprofile hweak Bclip
  let C₀ := D₀.continuous.coefficient i₀
  let S₀ := (P C₀.seedIndex).seed
  let e₀ := (Module.finBasis ℝ S₀.covector.ker).equivFunL
  let R₀ := populationSeedRootLabelValue S₀ a
  let errorScale := fun n : ℕ ↦ (1/((n : ℝ)+1))
  have hpos (n : ℕ) : 0 < errorScale n := by positivity
  have ht : Tendsto errorScale atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have he : Tendsto (fun n ↦ ENNReal.ofReal (errorScale n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,ENNReal.ofReal_zero] using
      (ENNReal.continuous_ofReal.tendsto 0).comp ht
  have hAB : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro x hxA hxB
    exact (not_le_of_gt hgap) (by simpa only [dist_self] using hdist x hxA x hxB)
  have hex (n : ℕ) := exists_original_population_core_uniform_clock_cutoffs
    (Good := Good) (δ := ENNReal.ofReal (errorScale n)) (loss := ENNReal.ofReal (errorScale n))
    hpopulation hrecovery hF hcomplete hu ha hinj hκ hbalance hGood
    hA hB hAB (hF.measurableSet_potentialRegularDomain hcomplete u) hμ hν hμreg hreg horder
    (ne_of_gt (ENNReal.ofReal_pos.mpr (hpos n))) (ne_of_gt (ENNReal.ofReal_pos.mpr (hpos n)))
  choose Daux hcutoffs using hex
  have hcuts (n : ℕ) (i : Fin (Daux n).haar.continuous.count) := hcutoffs n i (errorScale n) (hpos n)
  choose ψ hψcompact hψsupport hψrange hclock using hcuts
  let error := fun n ↦ ENNReal.ofReal Bclip*(ENNReal.ofReal (errorScale n)+ENNReal.ofReal (errorScale n))*
    (μ.map a) C₀.roots
  have herror : Tendsto error atTop (𝓝 0) := by
    have hadd := he.add he
    have hmul := ENNReal.Tendsto.const_mul hadd (a := ENNReal.ofReal Bclip) (Or.inr ENNReal.ofReal_ne_top)
    have hlast := ENNReal.Tendsto.mul_const hmul (b := (μ.map a) C₀.roots)
      (Or.inr (measure_ne_top (μ.map a) C₀.roots))
    simpa only [add_zero,mul_zero,zero_mul] using hlast
  have hfamily (n : ℕ) := (Daux n).originalIID_auxiliary_clipped_cell_sum_le
    (j := C₀.seedIndex) hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist D₀ i₀ rfl cost hcost k hq budget hbudget henergy
    (ψ n) (hψrange n) (hψsupport n) (ENNReal.ofReal (errorScale n)+ENNReal.ofReal (errorScale n))
    (hclock n) K hK hK₀ Q hroot m hm U hU hcube hUf W hW input hprofile hweak Bclip
  simp only [originalIIDSeedCoordinateCast_rfl,image_id'] at hK₀
  have hKbasis : K = e₀ '' (R₀ '' C₀.roots) := by
    rw [hK₀,image_image]
    rfl
  have hprofile₀ : ∀ᵐ c ∂(volume : Measure (OriginalIIDSeedCoordinateSpace P C₀.seedIndex)).restrict
      (e₀ '' (R₀ '' C₀.roots)), OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) C₀.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c) := by
    rwa [← hKbasis]
  have hwhole := D₀.fixed_candidate_clipped_le_of_auxiliary_cores hF hcomplete hu ha hinj i₀
    (fun _ ↦ Good) (fun _ ↦ r) (fun n ↦ ENNReal.ofReal (errorScale n))
    (fun n ↦ ENNReal.ofReal (errorScale n)) (fun n ↦ (Daux n).haar) he
    Λ gap (fun c ↦ condDistrib u a μ (root c)) (fun c ↦ condDistrib u a ν (root c))
    (fun _ ↦ inferInstance) (fun _ ↦ inferInstance) input hprofile₀
    (fun p ↦ ENNReal.ofReal (matrixQuadratic
      (physicalSceneOriginalMacroCoefficient (P := P) (a := a) C₀.seedIndex (p.1,p.2.1)) p.2.2))
    (ENNReal.ofReal Bclip) ENNReal.ofReal_ne_top (volume U*budget) error herror
    (fun n ↦ by
      simpa only [originalIIDSeedCoordinateCast_rfl,image_id',originalIIDAuxiliaryCell_eq_basis_image,error]
        using hfamily n)
  rwa [← hKbasis] at hwhole



/-- The actual full matching profile gives the raw Palm clock marginals and
strict forwardness. The original population moment witness then proves sign
on every original clock, without an interval support assumption. -/
theorem PopulationLocalPressureCore.ae_originalIID_fixed_candidate_full_clock_kinetic_nonneg
    (D : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good r δ loss)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (i : Fin D.haar.continuous.count) :
    let C := D.haar.continuous.coefficient i
    let S := (P C.seedIndex).seed
    let q := finrank ℝ S.covector.ker
    let label := physicalSceneOriginalMacroLabel (P := P) (a := a) C.seedIndex
    let K := label '' C.roots
    let ref := fun c : Fin q → ℝ ↦ a (S.curve
      ((Module.finBasis ℝ S.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) C.seedIndex
    ∀ (Λ : Kernel (Fin q → ℝ) (OriginalIIDMaskedMacroInputScene (Fin q)))
      (gap : ℝ), 0 < gap →
    ∀ input : (Fin q → ℝ) → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)),
    (∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ᵐ mark ∂originalIIDRawPairPalmKernel Λ c,
        0 ≤ matrixQuadratic (physicalSceneOriginalMacroCoefficient
          (P := P) (a := a) C.seedIndex (c,mark.1)) mark.2 := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  intro C S q label K ref root Λ gap hgap input hprofile
  have hlabel : ContinuousOn label C.roots := by
    apply (Module.finBasis ℝ S.covector.ker).equivFunL.continuous.comp_continuousOn
    have hc := (D.haar.intensity i).continuous_label
    rwa [D.haar.intensity_roots i] at hc
  have hK : MeasurableSet K := (C.roots_compact.image_of_continuousOn hlabel).measurableSet
  filter_upwards [hprofile,ae_restrict_mem hK] with c hc hcK
  obtain ⟨z,hz,rfl⟩ := hcK
  have hr : root (label z) = z :=
    physicalSceneOriginalMacroRootValue_at_label hF hcomplete hu ha hinj C.seedIndex
      (C.roots_subset_piece hz)
  let θ := originalSeedCoordinateIntensity P a κ (μ.map a) C.seedIndex (ref (label z))
  have hθ : 0 ≤ θ := mul_nonneg (NNReal.coe_nonneg _)
    (populationAtlasTheta_nonneg P a κ (μ.map a) C.seedIndex (ref (label z)))
  letI : IsProbabilityMeasure (Λ (label z)) := hc.1
  have hraw := original_raw_campbell_of_stationary_full_input_profile q θ hθ
    (condDistrib u a μ (root (label z))) (condDistrib u a ν (root (label z))) (Λ (label z))
    hc.2.2.1 (hc.2.2.2.2.2.mono fun scene hs ↦ hs.2.1) hc.2.2.2.1
  have hforward := ae_original_raw_palm_forward_of_matching_profile q gap θ hgap
    (condDistrib u a μ (root (label z))) (condDistrib u a ν (root (label z)))
    (input (label z)) (Λ (label z)) hc
  have hs := hraw.2.2.2.1
  have ht := hraw.2.2.2.2
  rw [hr] at hs ht
  simpa only [originalIIDRawPairPalmKernel_apply,PopulationLocalPressureCore.coreMacroLabel,
      physicalSceneOriginalMacroLabel,label] using
    D.ae_fixed_raw_macro_kinetic_nonneg hF hcomplete hu ha hinj i hz
      (cubePalm (Fin q) (physicalScenePairCampbell ((Λ (label z)).map Prod.fst))) θ hs ht hforward

/-- Actual original data, one original iid weak candidate and its genuine
matching profile imply full matrix kinetic integrability almost everywhere.
All clock/root precision limits are taken before monotone height exhaustion. -/
theorem originalIID_fixed_candidate_ae_kinetic_integrable
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)


    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.haar.continuous.count)
    (hseed₀ : (D₀.haar.continuous.coefficient i₀).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (hGood : ∀ᵐ z ∂μ.map a, Good z)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.haar.continuous.coefficient i₀).seedIndex '' (D₀.haar.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞)) (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let Λ := originalIIDWholeCoreSceneKernel K hK.measurableSet Q
    let ref := fun c : Vj ↦ a ((P j).seed.curve
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) j
    ∀ (input : Vj → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint qj) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint qj))),
    (∀ᵐ c ∂(volume : Measure Vj).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →


    ∀ᵐ c ∂(volume : Measure Vj).restrict K,
      Integrable (fun mark : PhysicalPairPalmMark (Fin qj) ↦ matrixQuadratic
        (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,mark.1)) mark.2)
        (originalIIDRawPairPalmKernel Λ c) := by
  classical
  subst j
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  letI : ∀ j, (κ j).IsAddHaarMeasure := hκ
  intro scale coord H hH Λ ref root input hprofile hweak
  let C₀ := D₀.haar.continuous.coefficient i₀
  let q := finrank ℝ (P C₀.seedIndex).seed.covector.ker
  let energy := fun p : (Fin q → ℝ) × PhysicalPairPalmMark (Fin q) ↦
    matrixQuadratic (physicalSceneOriginalMacroCoefficient (P := P) (a := a) C₀.seedIndex (p.1,p.2.1)) p.2.2
  have hbound := originalIID_fixed_candidate_clipped_energy_le (j := C₀.seedIndex)
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist D₀.haar i₀ rfl cost hcost k hq budget hbudget henergy
    hGood K hK hK₀ Q hroot m hm U hU hcube hUf W hW input hprofile hweak
  have henergyMeas : Measurable energy := continuous_matrixQuadratic.measurable.comp
    (((measurable_physicalSceneOriginalMacroCoefficient hF hcomplete hu ha hinj C₀.seedIndex).comp
      (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd)
  have hKnative : K = physicalSceneOriginalMacroLabel (P := P) (a := a) C₀.seedIndex '' C₀.roots := by
    simpa only [originalIIDSeedCoordinateCast_rfl,image_id'] using hK₀
  have hprofile₀ : ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict
      (physicalSceneOriginalMacroLabel (P := P) (a := a) C₀.seedIndex '' C₀.roots),
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) C₀.seedIndex (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c) := by
    rwa [← hKnative]
  have hnonneg : ∀ᵐ c ∂(volume : Measure (Fin q → ℝ)).restrict K,
      ∀ᵐ mark ∂originalIIDRawPairPalmKernel Λ c, 0 ≤ energy (c,mark) := by
    rw [hKnative]
    exact D₀.ae_originalIID_fixed_candidate_full_clock_kinetic_nonneg
      hF hcomplete hu ha hinj hκ i₀ Λ gap hgap input hprofile₀
  exact ae_integrable_of_uniform_clipped_kernel_bounds
    (volume.restrict K) (originalIIDRawPairPalmKernel Λ) energy henergyMeas hnonneg
    (volume U*budget) (ENNReal.mul_ne_top hUf hbudget)
    (fun n ↦ by simpa only [ENNReal.ofReal_natCast] using hbound (n : ℝ))


/-- Integrability passes to the literal normalized law of the SAME original
conditional matching. The raw profile supplies its own stationary finite Palm;
no stationarity, Palm mass or integrability field of the normalized law is assumed. -/
theorem integrable_same_originalIID_unit_candidate_of_profile
    (q : ℕ) (gap θ : ℝ) (hθ : 0 < θ)
    (α β : Measure ℝ) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (input : Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint q) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint q)))
    (Q : Measure (OriginalIIDMaskedMacroInputScene (Fin q)))
    (hprofile : OriginalIIDConditionalMatchingProfile gap θ α β input Q)
    (A : (ℝ × ℝ) → Matrix (Fin q) (Fin q) ℝ) (hA : Measurable A)
    (hkin : Integrable (fun mark ↦ matrixQuadratic (A mark.1) mark.2)
      (cubePalm (Fin q) (physicalScenePairCampbell (Q.map Prod.fst))))
    (law : ProbabilityMeasure (LegalMarkedOptimalInputScene q))
    (hlaw : (law : Measure _) = (Q.map (originalColoredScene q)).map
      (legalMarkedInputSceneDilation q (originalIIDUnitDilation q θ)
        (originalIIDUnitDilation_pos q θ).ne')) :
    Integrable (fun mark ↦ matrixQuadratic (A mark.1) mark.2) (legalMarkedJointPalm q law) := by
  letI : IsProbabilityMeasure Q := hprofile.1
  have hraw := original_raw_campbell_of_stationary_full_input_profile q θ hθ.le α β Q
    hprofile.2.2.1 (hprofile.2.2.2.2.2.mono fun scene hs ↦ hs.2.1) hprofile.2.2.2.1
  have hmass := hraw.2.2.1
  rw [cubePalm_apply (Fin q) _ MeasurableSet.univ,physicalScenePairCampbell_unitCube] at hmass
  have hunit : (∫⁻ scene, (scene.1 : Measure (LegalMarkedPhysicalEdge q))
      {e | e.1.1 ∈ palmUnitCube (Fin q)} ∂Q.map Prod.fst) < (⊤ : ℝ≥0∞) := by
    rw [hmass]
    exact ENNReal.ofReal_lt_top
  have hlaw' : law = originalUnitColoredLaw q ⟨Q,hprofile.1⟩ (originalIIDUnitDilation q θ)
      (originalIIDUnitDilation_pos q θ).ne' := ProbabilityMeasure.toMeasure_injective hlaw
  rw [hlaw']
  exact (integrable_originalUnitColoredLaw_matrix_iff q ⟨Q,hprofile.1⟩ hraw.1 hunit
    (originalIIDUnitDilation q θ) (originalIIDUnitDilation_pos q θ).ne' A hA).mpr hkin

/-- The SAME existing measurable unit-density kernel inherits kinetic
integrability from the actual original experiment. Its positive branch is
only the literal dilation identity already proved by its original producer. -/
theorem originalIID_fixed_candidate_ae_unit_kinetic_integrable
    (hpopulation : PopulationHaarPressureCoreLaw P a κ (μ.map a) μ ν ρ₀ ρ₁ v b r)
    (hrecovery : PopulationLabelCoreRecoveryLaw u a b (μ.map a) μ ν)
    (hF : F.IsSmoothStronglyConvex)
    (hcomplete : @CompleteSpace M F.metricSpace.toUniformSpace)
    (hu : let _inst : MetricSpace M := F.metricSpace; LipschitzWith 1 u)
    (ha : Measurable a)
    (hinj : Injective (fun x : F.potentialRegularDomain u ↦ (a x.val,u x.val)))
    (hκ : ∀ j, (κ j).IsAddHaarMeasure)
    (horder : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ F.potentialRegularDomain u, ∀ y ∈ F.potentialRegularDomain u,
        (a x = a y ∧ u x ≤ u y) ↔ u y-u x = dist x y)
    (hbalance : μ.map a = ν.map a)
    {A B : Set M} (hA : IsCompact A) (hB : IsCompact B)
    (hμ : ∀ᵐ x ∂μ, x ∈ A) (hν : ∀ᵐ y ∂ν, y ∈ B)
    (hreg : ∀ᵐ y ∂ν, y ∈ F.potentialRegularDomain u)
    (hμreg : ∀ᵐ x ∂μ, x ∈ F.potentialRegularDomain u)
    (hface : let _inst : MetricSpace M := F.metricSpace
      let _instProper : ProperSpace M := F.properSpace_of_complete hcomplete
      let _instBorel : StandardBorelSpace M := inferInstance
      let _instNonempty : Nonempty M := nonempty_of_isProbabilityMeasure μ
      ∀ π : Measure (M × M), IsOptimalCoupling edist μ ν π ↔
        ∃ k : Kernel (ℚ → M) (M × M), IsMarkovKernel k ∧ k ∘ₘ μ.map a = π ∧
          ∀ᵐ z ∂μ.map a, Vlasov.IsCoupling (k z)
            (condDistrib id a μ z) (condDistrib id a ν z) ∧
            ∀ᵐ p ∂k z, p.1 ∈ F.potentialRegularDomain u ∧
              p.2 ∈ F.potentialRegularDomain u ∧ a p.1 = a p.2 ∧ u p.1 ≤ u p.2)
    {gap : ℝ} (hgap : 0 < gap)
    (hdist : let _inst : MetricSpace M := F.metricSpace
      ∀ x ∈ A, ∀ y ∈ B, gap ≤ dist x y)


    {Good₀ : (ℚ → M) → Prop} {r₀ : ℝ} {δ₀ loss₀ : ℝ≥0∞}
    (D₀ : PopulationLocalPressureCore P a κ (μ.map a) μ ν ρ₀ ρ₁ v b Good₀ r₀ δ₀ loss₀)
    (i₀ : Fin D₀.haar.continuous.count)
    (hseed₀ : (D₀.haar.continuous.coefficient i₀).seedIndex = j)
    (cost : ℕ → M → M → ℝ) (hcost : ∀ n, Measurable (Function.uncurry (cost n)))
    (k : ℕ → ℝ) (hq : 0 < qj)
    (budget : ℝ≥0∞) (hbudget : budget ≠ ⊤)
    (henergy : ∀ᶠ n in atTop,
      (∫⁻ ξ, ∫⁻ p, ENNReal.ofReal ((physicalSceneCanonicalHaarScale qj n)^2 *
        ((F.lengthEDist p.1 p.2).toReal-u p.2+u p.1))
        ∂originalIIDOptimalPhysicalPlan (n := n+1) (cost n) (k n) ξ
        ∂(Measure.pi (fun _ : Fin (n+1) ↦ μ)).prod
          (Measure.pi (fun _ : Fin (n+1) ↦ ν))) ≤ budget)
    (hGood : ∀ᵐ z ∂μ.map a, Good z)
    (K : Set Vj) (hK : IsCompact K)
    (hK₀ : K = originalIIDSeedCoordinateCast (P := P) hseed₀ ''
      (physicalSceneOriginalMacroLabel (P := P) (a := a)
        (D₀.haar.continuous.coefficient i₀).seedIndex '' (D₀.haar.continuous.coefficient i₀).roots))
    (Q : ℕ → ProbabilityMeasure (Macroj × Macroj))
    (hroot : ∀ frame, (originalIIDFixedCandidateFullSceneJoint (Q frame)).fst =
      (physicalSceneUnitMassHaarLaw (physicalSceneCanonicalMacroCarrier qj)
        (physicalScene_centered_unitCube_mass (Fin qj)) : Measure Vj))
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop)
    (U : Set Vj) (hU : IsOpen U) (hcube : palmUnitCube (Fin qj) ⊆ U)
    (hUf : volume U ≠ (∞ : ℝ≥0∞)) (W : ℝ) (hW : ∀ x ∈ U, ‖x‖ ≤ W) :
    let scale := physicalSceneCanonicalHaarScale qj
    let coord := fun n ↦ physicalSceneOriginalSeedScaledPosition (P := P) (a := a) j (scale n)
    let H := physicalSceneOriginalSeedSource (P := P) (a := a) (κ := κ) (lambda := μ.map a) j
    let hH := measurableSet_physicalSceneOriginalSeedSource hF hcomplete hu ha hinj j
    let Λ := originalIIDWholeCoreSceneKernel K hK.measurableSet Q
    let ref := fun c : Vj ↦ a ((P j).seed.curve
      ((Module.finBasis ℝ (P j).seed.covector.ker).equivFunL.symm c) 0)
    let root := physicalSceneOriginalMacroRootValue (P := P) (a := a) j
    ∀ (input : Vj → Measure (LocalFiniteMeasure (LegalMarkedPhysicalPoint qj) ×
      LocalFiniteMeasure (LegalMarkedPhysicalPoint qj))),
    (∀ᵐ c ∂(volume : Measure Vj).restrict K,
      OriginalIIDConditionalMatchingProfile gap
        (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))
        (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c)) →
    (∀ frame, Tendsto (fun n ↦ originalIIDMaskedMacroPlanLaw (0 : Xj) μ ν
      (by simpa only [Fintype.card_fin] using hq)
      (cost (m n)) (hcost (m n)) (k (m n)) (m n) H hH
      (fun x ↦ coord (m n) x-scale (m n) • originalMacroFrameCenter qj frame)
      ((measurable_physicalSceneOriginalSeedScaledPosition hF hcomplete hu ha hinj j (scale (m n))).sub
        measurable_const)
      u (by letI : MetricSpace M := F.metricSpace; exact hu.continuous.measurable)) atTop
      (𝓝 ((Q frame).map (continuous_originalIIDMaskedMacroPlanProjection (0 : Xj)).measurable.aemeasurable))) →



    ∀ (Ξ : Kernel Vj (LegalMarkedOptimalInputScene qj)) (hΞ : IsMarkovKernel Ξ),
    (∀ c ∈ K, 0 < originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c) →
      Ξ c = ((Λ c).map (originalColoredScene qj)).map
        (legalMarkedInputSceneDilation qj
          (originalIIDUnitDilation qj (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c)))
          (originalIIDUnitDilation_pos qj (originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c))).ne')) →
    letI := hΞ
    ∀ᵐ c ∂(volume : Measure Vj).restrict K,
      0 < originalSeedCoordinateIntensity P a κ (μ.map a) j (ref c) →
      Integrable (fun mark : PhysicalPairPalmMark (Fin qj) ↦ matrixQuadratic
        (physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,mark.1)) mark.2)
        (legalMarkedJointPalm qj ⟨Ξ c,inferInstance⟩) := by
  classical
  letI : MetricSpace M := F.metricSpace
  letI : ProperSpace M := F.properSpace_of_complete hcomplete
  letI : PolishSpace M := inferInstance
  intro scale coord H hH Λ ref root input hprofile hweak Ξ hΞ hread
  letI := hΞ
  have hraw := originalIID_fixed_candidate_ae_kinetic_integrable (j := j)
    hpopulation hrecovery hF hcomplete hu ha hinj hκ horder hbalance
    hA hB hμ hν hreg hμreg hface hgap hdist D₀ i₀ hseed₀ cost hcost k hq budget hbudget henergy
    hGood K hK hK₀ Q hroot m hm U hU hcube hUf W hW input hprofile hweak
  filter_upwards [hraw,hprofile,ae_restrict_mem hK.measurableSet] with c hc hp hmem hpos
  have hAmeas : Measurable (fun clocks : ℝ × ℝ ↦
      physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,clocks)) :=
    (measurable_physicalSceneOriginalMacroCoefficient hF hcomplete hu ha hinj j).comp
      (measurable_const.prodMk measurable_id)
  exact integrable_same_originalIID_unit_candidate_of_profile qj gap _ hpos
    (condDistrib u a μ (root c)) (condDistrib u a ν (root c)) (input c) (Λ c) hp
    (fun clocks ↦ physicalSceneOriginalMacroCoefficient (P := P) (a := a) j (c,clocks)) hAmeas
    (by simpa only [originalIIDRawPairPalmKernel_apply] using hc)
    ⟨Ξ c,inferInstance⟩ (hread c hmem hpos)

end OTSelector.Reconstruction
