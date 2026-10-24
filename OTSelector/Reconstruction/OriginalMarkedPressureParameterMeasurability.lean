import OTSelector.Reconstruction.MarkedStationaryValueLegalPoissonMap
import Mathlib.Probability.Kernel.Representation
import Mathlib.Probability.Kernel.MeasurableIntegral

/-! The unchanged original legal pressure is measurable in its original root,
including simultaneous variation of the conditional laws and literal kernels. -/
open Set Function MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
noncomputable section
namespace OTSelector.Reconstruction
open OTSelector.Probability
set_option maxHeartbeats 250000

variable {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A] [MeasurableSpace B]

/-- Parameter-dependent original mark maps preserve joint measurability of
all original positions, counts and marks. -/
theorem measurable_parameter_mapMarkedCloud (q : ℕ)
    {f : Z → A → B} (hf : Measurable (uncurry f)) :
    Measurable (fun p : Z × MarkedCloudSpace q A ↦ mapMarkedCloud (f p.1) p.2) := by
  apply Measurable.prodMk
  · exact measurable_fst.comp measurable_snd
  · apply measurable_pi_lambda
    intro i
    exact ((measurable_fst.comp ((measurable_pi_apply i).comp
      (measurable_snd.comp measurable_snd)))).prodMk
        (hf.comp (measurable_fst.prodMk (measurable_snd.comp
          ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)))))

/-- Literal original finite legal values are jointly measurable in the root
and cloud when clocks, coefficient and probe are jointly measurable. -/
theorem measurable_parameter_legalMarkedTilted (q : ℕ)
    {source : Z → A → ℝ} {target : Z → B → ℝ}
    (hs : Measurable (uncurry source)) (ht : Measurable (uncurry target))
    {kin : Z → A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (fun p : Z × ((A × B) × (Fin q → ℝ)) ↦
      kin p.1 p.2.1.1 p.2.1.2 p.2.2))
    {probe : Z → A → B → ℝ}
    (hg : Measurable (fun p : Z × (A × B) ↦ probe p.1 p.2.1 p.2.2))
    (r : ℝ) (tilt : Z → ℝ) (htilt : Measurable tilt) :
    Measurable (fun p : Z × TwoMarkedCloudSpace q A B ↦
      legalMarkedTilted q (source p.1) (target p.1) r (kin p.1) (probe p.1) (tilt p.1) p.2) := by
  classical
  have hsource (i : ℕ) : Measurable (fun p : Z × TwoMarkedCloudSpace q A B ↦
      source p.1 (mSourceMark p.2 i)) :=
    hs.comp (measurable_fst.prodMk ((measurable_mSourceMark q i).comp measurable_snd))
  have htarget (j : ℕ) : Measurable (fun p : Z × TwoMarkedCloudSpace q A B ↦
      target p.1 (mTargetMark p.2 j)) :=
    ht.comp (measurable_fst.prodMk ((measurable_mTargetMark q j).comp measurable_snd))
  have hgraph (m n : ℕ) (E : Finset (Fin m × Fin n)) :
      MeasurableSet {p : Z × TwoMarkedCloudSpace q A B |
        legalMarkedGraph q m n (source p.1) (target p.1) p.2 = E} := by
    have hrepr : {p : Z × TwoMarkedCloudSpace q A B |
        legalMarkedGraph q m n (source p.1) (target p.1) p.2 = E} =
        ⋂ e : Fin m × Fin n, {p |
          (source p.1 (mSourceMark p.2 e.1) < target p.1 (mTargetMark p.2 e.2)) ↔ e ∈ E} := by
      ext p
      simp [Finset.ext_iff,legalMarkedGraph]
    rw [hrepr]
    apply MeasurableSet.iInter
    intro e
    by_cases he : e ∈ E
    · simpa only [he,iff_true] using measurableSet_lt (hsource e.1) (htarget e.2)
    · simpa only [he,iff_false,not_lt] using measurableSet_le (htarget e.2) (hsource e.1)
  have hcost (i j : ℕ) : Measurable (fun p : Z × TwoMarkedCloudSpace q A B ↦
      mKineticCost q r (kin p.1) p.2 i j + tilt p.1 * mProbe (probe p.1) p.2 i j) := by
    have hkread : Measurable (fun p : Z × TwoMarkedCloudSpace q A B ↦
        kin p.1 (mSourceMark p.2 i) (mTargetMark p.2 j)
          (mDisplacement (mSourcePoint p.2 i) (mTargetPoint p.2 j))) :=
      hk.comp (measurable_fst.prodMk
        ((((measurable_mSourceMark q i).comp measurable_snd).prodMk
          ((measurable_mTargetMark q j).comp measurable_snd)).prodMk
            ((measurable_mDisplacement q i j).comp measurable_snd)))
    have hprobe : Measurable (fun p : Z × TwoMarkedCloudSpace q A B ↦
        probe p.1 (mSourceMark p.2 i) (mTargetMark p.2 j)) :=
      hg.comp (measurable_fst.prodMk
        (((measurable_mSourceMark q i).comp measurable_snd).prodMk
          ((measurable_mTargetMark q j).comp measurable_snd)))
    exact (hkread.const_mul _).add ((htilt.comp measurable_fst).mul hprobe)
  have hfixed (m n : ℕ) : Measurable (fun p : Z × TwoMarkedCloudSpace q A B ↦
      legalMarkedFixedValue q m n (source p.1) (target p.1) r (kin p.1) (probe p.1) (tilt p.1) p.2) :=
    PartialMatching.measurable_legalMaximumValue _ (hgraph m n)
      (fun p i j ↦ mKineticCost q r (kin p.1) p.2 i j + tilt p.1 * mProbe (probe p.1) p.2 i j)
      (fun i j ↦ hcost i j)
  intro U hU
  have hrepr : (fun p : Z × TwoMarkedCloudSpace q A B ↦
      legalMarkedTilted q (source p.1) (target p.1) r (kin p.1) (probe p.1) (tilt p.1) p.2) ⁻¹' U =
      ⋃ m : ℕ, ⋃ n : ℕ,
        ({p | mSourceCount p.2 = m} ∩ {p | mTargetCount p.2 = n}) ∩
        (fun p ↦ legalMarkedFixedValue q m n (source p.1) (target p.1) r
          (kin p.1) (probe p.1) (tilt p.1) p.2) ⁻¹' U := by
    ext p
    simp only [mem_preimage,mem_iUnion,mem_inter_iff,mem_ofPred_eq]
    constructor
    · intro hp
      exact ⟨mSourceCount p.2,mTargetCount p.2,⟨rfl,rfl⟩,hp⟩
    · rintro ⟨m,n,⟨hm,hn⟩,hp⟩
      simpa only [legalMarkedTilted,hm,hn] using hp
  rw [hrepr]
  exact MeasurableSet.iUnion fun m ↦ MeasurableSet.iUnion fun n ↦
    ((measurableSet_eq_fun ((measurable_mSourceCount q).comp measurable_snd) measurable_const).inter
      (measurableSet_eq_fun ((measurable_mTargetCount q).comp measurable_snd) measurable_const)).inter
      (hfixed m n hU)

/-- The actual original pressure is measurable under arbitrary original
Markov conditional laws. The common uniform sampler is constructed internally
and has exactly those original iid pushforward laws, including both colors. -/
theorem measurable_original_legalMarkedPressure (q : ℕ)
    [Nonempty A] [Nonempty B] [StandardBorelSpace A] [StandardBorelSpace B]
    (α : Kernel Z A) [IsMarkovKernel α] (β : Kernel Z B) [IsMarkovKernel β]
    {source : Z → A → ℝ} {target : Z → B → ℝ}
    (hs : Measurable (uncurry source)) (ht : Measurable (uncurry target))
    {kin : Z → A → B → (Fin q → ℝ) → ℝ}
    (hk : Measurable (fun p : Z × ((A × B) × (Fin q → ℝ)) ↦
      kin p.1 p.2.1.1 p.2.1.2 p.2.2))
    {probe : Z → A → B → ℝ}
    (hg : Measurable (fun p : Z × (A × B) ↦ probe p.1 p.2.1 p.2.2))
    (r : ℝ≥0) (tilt : Z → ℝ) (htilt : Measurable tilt) :
    Measurable (fun z ↦ legalMarkedPressure q (source z) (target z)
      (α z) (β z) r (kin z) (probe z) (tilt z)) := by
  obtain ⟨fs,hfs,hα⟩ := α.exists_measurable_map_eq_unitInterval
  obtain ⟨ft,hft,hβ⟩ := β.exists_measurable_map_eq_unitInterval
  let sampler := fun p : Z × TwoMarkedCloudSpace q unitInterval unitInterval ↦
    (mapMarkedCloud (fs p.1) p.2.1,mapMarkedCloud (ft p.1) p.2.2)
  have hsampler : Measurable sampler :=
    ((measurable_parameter_mapMarkedCloud q hfs).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      ((measurable_parameter_mapMarkedCloud q hft).comp
        (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hread := (measurable_parameter_legalMarkedTilted q hs ht hk hg r tilt htilt).comp
    (measurable_fst.prodMk hsampler)
  let law := twoMarkedCloudLaw q unitInterval unitInterval volume volume r
  have hmeas : Measurable (fun z ↦ ∫ ω,
      legalMarkedTilted q (source z) (target z) r (kin z) (probe z) (tilt z)
        (sampler (z,ω)) ∂law) :=
    hread.stronglyMeasurable.integral_prod_right'.measurable
  convert hmeas using 1
  funext z
  have hfsz : Measurable (fs z) := hfs.comp measurable_prodMk_left
  have hftz : Measurable (ft z) := hft.comp measurable_prodMk_left
  have hm := map_twoMarkedCloudLaw_marks q
    (volume : Measure unitInterval) (volume : Measure unitInterval) (α z) (β z)
    hfsz hftz (hα z) (hβ z) r
  unfold legalMarkedPressure
  rw [← hm,integral_map
    ((measurable_mapMarkedCloud hfsz).prodMap
      (measurable_mapMarkedCloud hftz)).aemeasurable]
  · rfl
  · exact (measurable_legalMarkedTilted q
      (sourceClock := source z) (targetClock := target z) (kin := kin z) (g := probe z)
      (hs.comp measurable_prodMk_left) (ht.comp measurable_prodMk_left)
      (hk.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left) r (tilt z)).aestronglyMeasurable

end OTSelector.Reconstruction
