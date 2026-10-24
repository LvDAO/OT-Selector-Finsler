import OTSelector.Transport.Coupling.FiniteClockMixture
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Reconstruction.FinslerConcreteUpperClassThinning.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Reconstruction.FinslerConcreteUpperClassThinning`; the selected original proof blocks follow. -/
section

/-!
# Reconstruction.FinslerConcreteUpperClassThinning

**Conditions:** A finite-measure kernel is partitioned into finitely many disjoint measurable bins, with a specified in-bin fallback and finite frozen class weights.

**Objects:** Normalized bin Markov kernels and a class-thinned retained kernel with exact label/class product law.

**Proof detail:** Normalize each nonzero restricted bin and use the fallback at zero mass; multiplying back by bin mass recovers the restriction, disjoint sums give domination, and bin support makes classification a point mass.

**Sources:** [D. H. Fremlin, Measure Theory, Volume 4](https://www1.essex.ac.uk/maths/people/fremlin/chap45.pdf#page=18), Section 452A–452F (integration of families and disintegrations), 452M (product disintegration); [D. H. Fremlin, Measure Theory, Volume 2](https://www1.essex.ac.uk/maths/people/fremlin/chap23.pdf), Sections 232E–232I, Radon–Nikodym and Lebesgue decomposition; Section 235K, change of measure; [Sheldon Axler, Measure, Integration & Real Analysis (author PDF, 12 June 2026)](https://measure.axler.net/MIRA.pdf#page=144), Section 5B, Theorem 5.28 (Tonelli), printed p. 129, PDF page 144.

Source relation (composition): The cited sections provide the stated mathematical foundations; the exact finite construction and quantitative bound in this module are local consequences, not a claim that the book states the Lean theorem verbatim.
-/

/-!
Classwise thinning preserves actual clocks inside their original bins. Each
normalized bin law is a measurable Markov kernel, with a fixed in-bin fallback
only at zero-mass bins. Exact frozen class weights then give an exact product
law of the original spatial label and finite clock class.
-/

open Set Function MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace OTSelector.Reconstruction

variable {Z X : Type*} [MeasurableSpace Z] [MeasurableSpace X]

/-- The actual normalized law inside one measurable bin. A fixed fallback is
used at null bins so the kernel remains Markov at every original label. -/
def normalizedActualBinKernel (κ : Kernel Z X) (B : Set X) (hB : MeasurableSet B)
    (fallback : X) : Kernel Z X where
  toFun z := if κ z B = 0 then Measure.dirac fallback
    else (κ z B)⁻¹ • (κ z).restrict B
  measurable' := by
    classical
    apply Measure.measurable_of_measurable_coe
    intro s hs
    have hm := κ.measurable_coe hB
    change Measurable (fun z ↦ (if κ z B = 0 then Measure.dirac fallback
      else (κ z B)⁻¹ • (κ z).restrict B) s)
    have hh : Measurable (fun z : Z ↦ if κ z B = 0 then Measure.dirac fallback s
        else (κ z B)⁻¹ * κ z (s ∩ B)) :=
      (measurable_const : Measurable (fun _ : Z ↦ Measure.dirac fallback s)).ite
        (measurableSet_eq_fun hm (measurable_const (a := (0 : ℝ≥0∞))))
        (hm.inv.mul (κ.measurable_coe (hs.inter hB)))
    convert hh using 1
    funext z
    split_ifs <;> simp [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs]

/-- Every normalized original-bin kernel is a probability kernel. -/
instance normalizedActualBinKernel_isMarkov (κ : Kernel Z X)
    [∀ z, IsFiniteMeasure (κ z)] (B : Set X) (hB : MeasurableSet B) (fallback : X) :
    IsMarkovKernel (normalizedActualBinKernel κ B hB fallback) where
  isProbabilityMeasure z := ⟨by
    change (if κ z B = 0 then Measure.dirac fallback
      else (κ z B)⁻¹ • (κ z).restrict B) univ = 1
    split_ifs with hzero
    · simp
    · rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
        ENNReal.inv_mul_cancel hzero (measure_ne_top _ _)]⟩

/-- The fallback can be chosen in the same bin, so even null-bin normalization
never changes the raw clock class. -/
theorem normalizedActualBinKernel_supported (κ : Kernel Z X) (B : Set X)
    (hB : MeasurableSet B) {fallback : X} (hfallback : fallback ∈ B) (z : Z) :
    ∀ᵐ x ∂normalizedActualBinKernel κ B hB fallback z, x ∈ B := by
  change ∀ᵐ x ∂(if κ z B = 0 then Measure.dirac fallback
    else (κ z B)⁻¹ • (κ z).restrict B), x ∈ B
  split_ifs with hzero
  · exact (ae_dirac_iff hB).mpr hfallback
  · exact Measure.ae_smul_measure (ae_restrict_mem hB) _

/-- Positive actual bin mass gives in-bin support independently of the fallback. -/
theorem normalizedActualBinKernel_supported_of_mass_ne_zero
    (κ : Kernel Z X) (B : Set X) (hB : MeasurableSet B) (fallback : X)
    (z : Z) (hpos : κ z B ≠ 0) :
    ∀ᵐ x ∂normalizedActualBinKernel κ B hB fallback z, x ∈ B := by
  change ∀ᵐ x ∂(if κ z B = 0 then Measure.dirac fallback
    else (κ z B)⁻¹ • (κ z).restrict B), x ∈ B
  rw [if_neg hpos]
  exact Measure.ae_smul_measure (ae_restrict_mem hB) _

/-- Restoring the original bin mass recovers the literal original restriction,
including its zero-mass case. -/
theorem binMass_smul_normalizedActualBinKernel (κ : Kernel Z X)
    [∀ z, IsFiniteMeasure (κ z)] (B : Set X) (hB : MeasurableSet B)
    (fallback : X) (z : Z) :
    κ z B • normalizedActualBinKernel κ B hB fallback z = (κ z).restrict B := by
  change κ z B • (if κ z B = 0 then Measure.dirac fallback
    else (κ z B)⁻¹ • (κ z).restrict B) = (κ z).restrict B
  split_ifs with hzero
  · rw [hzero, zero_smul, Measure.restrict_eq_zero.mpr hzero]
  · rw [smul_smul, ENNReal.mul_inv_cancel hzero (measure_ne_top _ _), one_smul]

/-- A fixed frozen class mass dominated by the actual weighted bin mass can be
retained without moving any clock out of that bin. -/
theorem frozenBinMass_smul_normalizedActualBinKernel_le
    (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)]
    (B : Set X) (hB : MeasurableSet B) (fallback : X) (z : Z)
    {d p : ℝ≥0∞} (hp : p ≤ d * κ z B) :
    p • normalizedActualBinKernel κ B hB fallback z ≤ d • (κ z).restrict B := by
  calc
    _ ≤ (d * κ z B) • normalizedActualBinKernel κ B hB fallback z :=
      by
        intro s
        simp only [Measure.smul_apply, smul_eq_mul]
        exact mul_le_mul_of_nonneg_right hp bot_le
    _ = _ := by rw [mul_smul, binMass_smul_normalizedActualBinKernel]

section Classes

variable {I : Type*} [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]

/-- The measurable retained raw-clock kernel with fixed finite class weights. -/
def frozenClassRetainedKernel (κ : Kernel Z X) (B : I → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X) (p : I → ℝ≥0∞) : Kernel Z X :=
  ∑ i, {
    toFun z := p i • normalizedActualBinKernel κ (B i) (hB i) (fallback i) z
    measurable' := by
      apply Measure.measurable_of_measurable_coe
      intro s hs
      simp only [Measure.smul_apply, smul_eq_mul]
      exact measurable_const.mul ((normalizedActualBinKernel κ (B i) (hB i)
        (fallback i)).measurable_coe hs) }

/-- The whole retained population is a genuine submeasure of the same original
weighted mark law when its class masses are pointwise dominated. -/
theorem frozenClassRetainedKernel_le
    (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)] (B : I → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (hdisj : Pairwise (Disjoint on B))
    (fallback : I → X) (p : I → ℝ≥0∞) (z : Z) {d : ℝ≥0∞}
    (hp : ∀ i, p i ≤ d * κ z (B i)) :
    frozenClassRetainedKernel κ B hB fallback p z ≤ d • κ z := by
  classical
  simp only [frozenClassRetainedKernel, sum_apply, Kernel.coe_mk]
  change (∑ i, p i • normalizedActualBinKernel κ (B i) (hB i) (fallback i) z) ≤ _
  calc
    _ ≤ ∑ i, d • (κ z).restrict (B i) := Finset.sum_le_sum fun i _ ↦
      frozenBinMass_smul_normalizedActualBinKernel_le κ (B i) (hB i) (fallback i) z (hp i)
    _ = d • (κ z).restrict (⋃ i, B i) := by
      rw [← Finset.smul_sum, Measure.restrict_iUnion hdisj hB, Measure.sum_fintype]
    _ ≤ d • κ z := by
      intro s
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (Measure.restrict_le_self s) bot_le


/-- Fixed finite class masses give a finite retained kernel even when original
bin masses vary with the original label. -/
theorem frozenClassRetainedKernel_isFinite
    (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)] (B : I → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X) (p : I → ℝ≥0∞)
    (hp : ∀ i, p i ≠ ∞) : IsFiniteKernel (frozenClassRetainedKernel κ B hB fallback p) := by
  classical
  refine ⟨⟨∑ i, p i, ENNReal.sum_lt_top.mpr (fun i _ ↦ (hp i).lt_top), fun z ↦ ?_⟩⟩
  simp only [frozenClassRetainedKernel, sum_apply, Kernel.coe_mk,
    Measure.finsetSum_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, le_refl]

/-- Classifying an actual normalized bin gives its original class exactly. -/
theorem normalizedActualBinKernel_map_class
    (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)] (B : I → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X)
    (hfallback : ∀ i, fallback i ∈ B i) (classify : X → I)
    (hclass : ∀ i x, x ∈ B i → classify x = i) (i : I) (z : Z) :
    (normalizedActualBinKernel κ (B i) (hB i) (fallback i) z).map classify =
      Measure.dirac i := by
  have heq : classify =ᵐ[normalizedActualBinKernel κ (B i) (hB i) (fallback i) z]
      (fun _ ↦ i) :=
    (normalizedActualBinKernel_supported κ (B i) (hB i) (hfallback i) z).mono
      (fun x hx ↦ hclass i x hx)
  rw [Measure.map_congr heq, Measure.map_const, measure_univ, one_smul]

/-- The retained clock-class kernel is constant. The original label therefore
remains independent of this exact frozen finite class law. -/
theorem frozenClassRetainedKernel_map_class
    (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)] (B : I → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X)
    (hfallback : ∀ i, fallback i ∈ B i) (classify : X → I) (hm : Measurable classify)
    (hclass : ∀ i x, x ∈ B i → classify x = i) (p : I → ℝ≥0∞) :
    (frozenClassRetainedKernel κ B hB fallback p).map classify =
      Kernel.const Z (∑ i, p i • Measure.dirac i) := by
  ext z : 1
  rw [Kernel.map_apply _ hm]
  simp only [frozenClassRetainedKernel, sum_apply, Kernel.coe_mk]
  rw [Measure.map_finset_sum' hm.aemeasurable]
  simp_rw [Measure.map_smul,
    normalizedActualBinKernel_map_class κ B hB fallback hfallback classify hclass]
  rfl

/-- Exact product identity on the original spatial labels and retained classes;
only raw clocks are conditionally distributed inside their original bins. -/
theorem frozenClassRetainedKernel_label_class_law
    (μ : Measure Z) [SFinite μ]
    (κ : Kernel Z X) [∀ z, IsFiniteMeasure (κ z)] (B : I → Set X)
    (hB : ∀ i, MeasurableSet (B i)) (fallback : I → X)
    (hfallback : ∀ i, fallback i ∈ B i) (classify : X → I) (hm : Measurable classify)
    (hclass : ∀ i x, x ∈ B i → classify x = i) (p : I → ℝ≥0∞)
    (hp : ∀ i, p i ≠ ∞) :
    (μ ⊗ₘ frozenClassRetainedKernel κ B hB fallback p).map (Prod.map id classify) =
      μ.prod (∑ i, p i • Measure.dirac i) := by
  haveI := frozenClassRetainedKernel_isFinite κ B hB fallback p hp
  haveI : ∀ i, IsFiniteMeasure (p i • Measure.dirac i) := fun i ↦
    ⟨by simpa [Measure.smul_apply] using (hp i).lt_top⟩
  rw [← Measure.compProd_map hm,
    frozenClassRetainedKernel_map_class κ B hB fallback hfallback classify hm hclass p,
    Measure.compProd_const]

/-- The actual varying class masses recover the full original weighted clock
kernel whenever the original bins partition all clock values. -/
theorem finiteClassMarginalKernel_normalized_bins_eq_original
    (κ : Kernel Z X) [IsSFiniteKernel κ] [∀ z, IsFiniteMeasure (κ z)]
    (B : I → Set X) (hB : ∀ i, MeasurableSet (B i))
    (hdisj : Pairwise (Disjoint on B)) (hcover : (⋃ i, B i) = univ)
    (fallback : I → X) (d : Z → ℝ) (hd : Measurable d) (hd0 : ∀ z, 0 ≤ d z) :
    finiteClassMarginalKernel (fun z i ↦ d z * (κ z).real (B i))
      (fun i ↦ normalizedActualBinKernel κ (B i) (hB i) (fallback i)) =
      classWeightedKernel d κ := by
  classical
  have hm (i : I) : Measurable (fun z ↦ d z * (κ z).real (B i)) :=
    hd.mul ((κ.measurable_coe (hB i)).ennreal_toReal)
  ext z : 1
  rw [finiteClassMarginalKernel_apply _ hm, classWeightedKernel_apply _ hd]
  have hmass (i : I) : ENNReal.ofReal (d z * (κ z).real (B i)) =
      ENNReal.ofReal (d z) * κ z (B i) := by
    rw [ENNReal.ofReal_mul (hd0 z), measureReal_def,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  simp_rw [hmass, mul_smul, binMass_smul_normalizedActualBinKernel]
  rw [← Finset.smul_sum, ← Measure.sum_fintype, ← Measure.restrict_iUnion hdisj hB,
    hcover, Measure.restrict_univ]

end Classes
end OTSelector.Reconstruction

end
end
