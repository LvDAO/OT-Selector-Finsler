import OTSelector.Reconstruction.FinslerOriginalBlockRepairVanishing
import OTSelector.Reconstruction.FinslerOriginalKernelModulusPressure
import OTSelector.Reconstruction.FinslerOriginalKernelPressureStability
import OTSelector.Reconstruction.FinslerOriginalKernelBlockSubadditivity

/-!
# Block pressure limit identification for position-dependent kernels

The upper readout bound of `FinslerOriginalBlockRepairVanishing.lean` is
conditional on the *block pressure limit identification*: the average of the
block-rescaled scale pressures

  (1 / m ^ q) * sum_c kernelMarkedScalePressure (blockLocalKernel K c) L t

converges, at the fixed probe and tilt, to the reference limit `p t`.  This
module isolates the two exact ways in which that identification can be supplied:

* **uniform block reconciliation.**  If every block-rescaled kernel has the same
  normalized scale-pressure limit `p t`, the average has the same limit
  (`tendsto_blockAverageScalePressure_of_uniform_block_limit`); more generally the
  average limit is the average of the block limits
  (`tendsto_blockAverageScalePressure_of_blockwise_limit`);
* **blockwise pressure stabilization.**  If the reference scale pressure has a
  limit `p t` and every block scale pressure differs from it by `o(1)`, the
  average converges to `p t`
  (`tendsto_blockAverageScalePressure_of_blockwise_stability`).  This is the
  form exploited by the hupper-shaped readout
  (`eventually_kernelMarkedScalePressure_le_of_blockwise_stability`).

Two exact sufficient conditions for the blockwise stabilization are recorded:
equality of marked point laws (`tendsto_scalePressure_sub_of_markedPointLaw_eq`,
which covers the constant-kernel case, where all block kernels coincide with the
reference kernel) and the constant-kernel existence theorem
`exists_tendsto_blockAverageScalePressure_const`.

The exact remaining sub-gap is the position-dependent blockwise stabilization
itself: for a genuinely position-dependent mark kernel the block-rescaled kernel
`K c (x) = K (corner c + x / m)` differs from `K`, so the input needed is a
quantitative pressure stability estimate under a coupling of the marked point
laws, with an error vanishing faster than the scale `L ^ q`.  The producer steps
for that estimate (coupling construction, leaf-block law identification, kernel
modulus at the pairing scale, matching moment bound) are listed in
`FinslerOriginalKernelPressureStability.lean`; this module does not assume them
and states the reduction exactly.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators
open OTSelector OTSelector.Probability

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace OTSelector.Reconstruction

variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

/-! ## The block-averaged scale pressure -/

/-- The average of the block-rescaled scale pressures over the `m ^ q` blocks. -/
noncomputable def blockAverageScalePressure (q m : ℕ) (Ks : Kernel (Fin q → ℝ) A)
    [IsMarkovKernel Ks] (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    (kin : A → B → (Fin q → ℝ) → ℝ) (g : A → B → ℝ) (L t : ℝ) : ℝ :=
  (1 / (((m ^ q : ℕ) : ℝ))) *
    (∑ c : Fin q → Fin m,
      kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
        kin g L t)

/-- The cardinality of the block index set. -/
theorem card_blockIndex (q m : ℕ) :
    ((Finset.univ : Finset (Fin q → Fin m)).card) = m ^ q := by
  rw [Finset.card_univ, Fintype.card_fun]
  simp

/-- The normalization constant `1 / m ^ q` is nonzero for a positive block count. -/
theorem one_div_blockCard_ne_zero {q m : ℕ} (hm : 0 < m) :
    (1 / (((m ^ q : ℕ) : ℝ))) ≠ 0 := by
  have h : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
  positivity

/-! ## A finite averaging lemma -/

/-- A finite average of functions tending to zero tends to zero. -/
theorem tendsto_blockAveraged_sub_zero {q m : ℕ} {f : (Fin q → Fin m) → ℝ → ℝ}
    (h : ∀ c : Fin q → Fin m, Tendsto (fun L : ℝ => f c L) atTop (𝓝 0)) :
    Tendsto (fun L : ℝ =>
        (1 / (((m ^ q : ℕ) : ℝ))) * ∑ c : Fin q → Fin m, f c L) atTop (𝓝 0) := by
  have hsum : Tendsto (fun L : ℝ => ∑ c : Fin q → Fin m, f c L) atTop (𝓝 (0 : ℝ)) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset (Fin q → Fin m))
      (fun c _ => h c)
  simpa only [mul_zero] using hsum.const_mul (1 / (((m ^ q : ℕ) : ℝ)))

/-! ## Identification from blockwise pressure stabilization -/

/-- **Block-averaged pressure limit from blockwise stabilization.**  If the
reference scale pressure tends to `p` and each block scale pressure differs from
the reference one by a vanishing amount, then the block average tends to `p`. -/
theorem tendsto_blockAverageScalePressure_of_blockwise_stability
    (q m : ℕ) (hm : 0 < m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t p : ℝ}
    (hstab : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
            kin g L t -
          kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 0))
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    Tendsto (blockAverageScalePressure q m Ks Kt kin g · t) atTop (𝓝 p) := by
  classical
  have hmq0 : (((m ^ q : ℕ) : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
    exact h.ne'
  have hzero : Tendsto (fun L : ℝ =>
      (1 / (((m ^ q : ℕ) : ℝ))) *
        ∑ c : Fin q → Fin m,
          (kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
              (blockLocalKernel Kt c) kin g L t -
            kernelMarkedScalePressure q A B Ks Kt kin g L t))
      atTop (𝓝 0) :=
    tendsto_blockAveraged_sub_zero (q := q) (m := m) hstab
  have hmain : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t +
        (1 / (((m ^ q : ℕ) : ℝ))) *
          ∑ c : Fin q → Fin m,
            (kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
                (blockLocalKernel Kt c) kin g L t -
              kernelMarkedScalePressure q A B Ks Kt kin g L t))
      atTop (𝓝 (p + 0)) := href.add hzero
  rw [add_zero] at hmain
  refine hmain.congr' ?_
  filter_upwards with L
  unfold blockAverageScalePressure
  have hcard := card_blockIndex q m
  have hpoint : ∀ c : Fin q → Fin m,
      kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
          kin g L t =
        kernelMarkedScalePressure q A B Ks Kt kin g L t +
          (kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
              (blockLocalKernel Kt c) kin g L t -
            kernelMarkedScalePressure q A B Ks Kt kin g L t) := by
    intro c
    ring
  rw [Finset.sum_congr rfl (fun c _ => hpoint c), Finset.sum_add_distrib,
    Finset.sum_const, hcard, nsmul_eq_mul]
  field_simp


/-! ## Identification from a uniform block limit -/

/-- **Uniform block reconciliation implies the block average identification.**
If every block-rescaled kernel has the same normalized scale-pressure limit
`p`, then the block average has limit `p`. -/
theorem tendsto_blockAverageScalePressure_of_uniform_block_limit
    (q m : ℕ) (hm : 0 < m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t p : ℝ}
    (hlim : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 p)) :
    Tendsto (blockAverageScalePressure q m Ks Kt kin g · t) atTop (𝓝 p) := by
  classical
  have hmq0 : (((m ^ q : ℕ) : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
    exact h.ne'
  have hcard := card_blockIndex q m
  have hsum : Tendsto (fun L : ℝ => ∑ c : Fin q → Fin m,
      kernelMarkedScalePressure q A B (blockLocalKernel Ks c) (blockLocalKernel Kt c)
        kin g L t) atTop (𝓝 ((((m ^ q : ℕ) : ℝ)) * p)) := by
    have h := tendsto_finsetSum (Finset.univ : Finset (Fin q → Fin m))
      (fun c _ => hlim c)
    simpa only [Finset.sum_const, hcard, nsmul_eq_mul] using h
  have hmain := hsum.const_mul (1 / (((m ^ q : ℕ) : ℝ)))
  have hlimval : (1 / (((m ^ q : ℕ) : ℝ))) * ((((m ^ q : ℕ) : ℝ)) * p) = p := by
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hmq0, one_mul]
  rw [hlimval] at hmain
  exact hmain

/-- **The block average limit is the average of the block limits.**  With
position-dependent kernels the block limits may differ; the identification with
`p` is then exactly the numerical identity
`(1 / m ^ q) * sum_c p_c = p`. -/
theorem tendsto_blockAverageScalePressure_of_blockwise_limit
    (q m : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t : ℝ}
    {pc : (Fin q → Fin m) → ℝ}
    (hlim : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 (pc c))) :
    Tendsto (blockAverageScalePressure q m Ks Kt kin g · t) atTop
      (𝓝 ((1 / (((m ^ q : ℕ) : ℝ))) * ∑ c : Fin q → Fin m, pc c)) := by
  classical
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin q → Fin m))
    (fun c _ => hlim c)
  have hmain := hsum.const_mul (1 / (((m ^ q : ℕ) : ℝ)))
  simpa only [blockAverageScalePressure] using hmain

/-! ## Exact sufficient conditions for the blockwise stabilization -/

/-- **Equal marked point laws give exact blockwise stabilization.**  If the
block-rescaled kernels carry the same marked point laws as the reference
kernels, the block and reference scale pressures coincide at every scale. -/
theorem tendsto_scalePressure_sub_of_markedPointLaw_eq
    (q m : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t : ℝ}
    (hs : ∀ c : Fin q → Fin m,
      markedPointLaw q (blockLocalKernel Ks c) = markedPointLaw q Ks)
    (ht : ∀ c : Fin q → Fin m,
      markedPointLaw q (blockLocalKernel Kt c) = markedPointLaw q Kt) :
    ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) kin g L t -
          kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 0) := by
  intro c
  have hzero : ∀ L : ℝ,
      kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t -
        kernelMarkedScalePressure q A B Ks Kt kin g L t = 0 := by
    intro L
    rw [kernelMarkedScalePressure_eq_of_markedPointLaw q (hs c) (ht c)
      (kin := kin) (g := g) (R := L) (t := t)]
    ring
  rw [funext hzero]
  exact tendsto_const_nhds

/-- At constant kernels every block-rescaled kernel coincides with the reference
kernel, so the block average is exactly the reference scale pressure. -/
theorem blockAverageScalePressure_const
    (q m : ℕ) (hm : 0 < m)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} (L t : ℝ) :
    blockAverageScalePressure q m (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) kin g L t =
      kernelMarkedScalePressure q A B (Kernel.const (Fin q → ℝ) α)
        (Kernel.const (Fin q → ℝ) β) kin g L t := by
  classical
  have hmq0 : (((m ^ q : ℕ) : ℝ)) ≠ 0 := by
    have h : (0 : ℝ) < ((m ^ q : ℕ) : ℝ) := by exact_mod_cast pow_pos hm q
    exact h.ne'
  have hcard := card_blockIndex q m
  unfold blockAverageScalePressure
  rw [Finset.sum_congr rfl (fun c _ => ?_)]
  · rw [Finset.sum_const, hcard, nsmul_eq_mul]
    rw [one_div, ← mul_assoc, inv_mul_cancel₀ hmq0, one_mul]
  · refine kernelMarkedScalePressure_eq_of_markedPointLaw q ?_ ?_
      (kin := kin) (g := g) (R := L) (t := t)
    · rw [blockLocalKernel_const]
    · rw [blockLocalKernel_const]

/-- **The constant-kernel block average limit exists unconditionally.**  This is
the sharp case in which the block pressure identification is an identity with
zero error, and it shows that the identification hypothesis of the
position-dependent reduction is satisfiable. -/
theorem exists_tendsto_blockAverageScalePressure_const
    (q : ℕ) (hq : 4 < q) (m : ℕ) (hm : 0 < m)
    (α : Measure A) [IsProbabilityMeasure α]
    (β : Measure B) [IsProbabilityMeasure β]
    {C G : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G) :
    ∃ p : ℝ → ℝ,
      (∀ t, Tendsto (blockAverageScalePressure q m (Kernel.const (Fin q → ℝ) α)
          (Kernel.const (Fin q → ℝ) β) kin g · t) atTop (𝓝 (p t))) ∧
      ConcaveOn ℝ Set.univ p ∧ LipschitzWith ⟨G, hG0⟩ p := by
  obtain ⟨p, hp, hconc, hlip⟩ := exists_kernelMarkedScalePressure_limit_const q hq
    α β hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb
  refine ⟨p, fun t => ?_, hconc, hlip⟩
  refine (hp t).congr' ?_
  filter_upwards with L
  exact (blockAverageScalePressure_const q m hm α β (kin := kin) (g := g) L t).symm


/-! ## Interface with the block repair comparison -/

/-- The scale-level block comparison of `FinslerOriginalBlockRepairVanishing.lean`
with the aggregate block pressure written as the block average. -/
theorem kernelMarkedScalePressure_le_blockAverageScalePressure_add_gridRepairError
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {L : ℝ} (hL : 0 < L) :
    kernelMarkedScalePressure q A B Ks Kt kin g ((m : ℝ) * L) t ≤
      blockAverageScalePressure q m Ks Kt kin g L t +
        gridRepairError q (gridRepairConstant q) C G t L := by
  unfold blockAverageScalePressure
  exact kernelMarkedScalePressure_le_blockSum_add_gridRepairError q m J hq hm hJ hJ2
    Ks Kt (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb hL

/-! ## The `hupper`-shaped readout -/

/-- **Upper readout bound from blockwise pressure stabilization.**  This is the
`hupper`-shaped input of the expectation upper bound, now reduced exactly to the
blockwise stabilization of the block-rescaled scale pressures plus the reference
scale-pressure limit `p`. -/
theorem eventually_kernelMarkedScalePressure_le_of_blockwise_stability
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ}
    (hstab : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
            (blockLocalKernel Kt c) kin g L t -
          kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 0))
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      kernelMarkedScalePressure q A B Ks Kt kin g R t ≤ p + ε := by
  have hlimit := tendsto_blockAverageScalePressure_of_blockwise_stability
    (q := q) (m := m) hm Ks Kt (t := t) hstab href
  refine eventually_kernelMarkedScalePressure_le_of_blockPressureLimit (q := q)
    (m := m) (J := J) hq hm hJ hJ2 Ks Kt (t := t) hC0 hG0 hkin hkin_nonneg
    hkin_bound hkin_homog hg hgb ?_
  simpa only [blockAverageScalePressure] using hlimit

/-- **Exact-law case of the upper readout bound.**  If the block-rescaled
kernels carry the reference marked point laws, the blockwise stabilization holds
with zero error, so the readout bound follows from the reference limit alone.
This covers the constant-kernel case, where all block kernels are the reference
kernel. -/
theorem eventually_kernelMarkedScalePressure_le_of_markedPointLaw_eq
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ}
    (hs : ∀ c : Fin q → Fin m,
      markedPointLaw q (blockLocalKernel Ks c) = markedPointLaw q Ks)
    (ht : ∀ c : Fin q → Fin m,
      markedPointLaw q (blockLocalKernel Kt c) = markedPointLaw q Kt)
    (href : Tendsto (fun L : ℝ =>
      kernelMarkedScalePressure q A B Ks Kt kin g L t) atTop (𝓝 p)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      kernelMarkedScalePressure q A B Ks Kt kin g R t ≤ p + ε := by
  refine eventually_kernelMarkedScalePressure_le_of_blockwise_stability q m J hq hm
    hJ hJ2 Ks Kt (t := t) hC0 hG0 hkin hkin_nonneg hkin_bound hkin_homog hg hgb
    ?_ href
  exact tendsto_scalePressure_sub_of_markedPointLaw_eq q m Ks Kt (kin := kin) (g := g) hs ht

/-- **Identification from the numerical average of the block limits.**  If the
block scale pressures have limits `p_c` and the average of those limits equals
`p`, then the block average has limit `p`.  This is the exact numerical form of
the remaining identification input. -/
theorem tendsto_blockAverageScalePressure_of_blockwise_limit_eq
    (q m : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t p : ℝ}
    {pc : (Fin q → Fin m) → ℝ}
    (hlim : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 (pc c)))
    (hpc : (1 / (((m ^ q : ℕ) : ℝ))) * ∑ c : Fin q → Fin m, pc c = p) :
    Tendsto (blockAverageScalePressure q m Ks Kt kin g · t) atTop (𝓝 p) := by
  have h := tendsto_blockAverageScalePressure_of_blockwise_limit q m Ks Kt
    (t := t) (pc := pc) hlim
  rwa [hpc] at h


/-- **Necessity of the numerical identification.**  If the block limits `p_c`
exist, then every limit of the block average is the average of the block limits;
in particular the identification with `p` is exactly `(1 / m ^ q) * sum_c p_c = p`.
This is the exact remaining sub-gap at the level of limits. -/
theorem tendsto_blockAverageScalePressure_iff_blockwise_limit_eq
    (q m : ℕ)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ} {t p : ℝ}
    {pc : (Fin q → Fin m) → ℝ}
    (hlim : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 (pc c))) :
    Tendsto (blockAverageScalePressure q m Ks Kt kin g · t) atTop (𝓝 p) ↔
      (1 / (((m ^ q : ℕ) : ℝ))) * ∑ c : Fin q → Fin m, pc c = p := by
  constructor
  · intro h
    have hpc := tendsto_blockAverageScalePressure_of_blockwise_limit q m Ks Kt
      (t := t) (pc := pc) hlim
    have huniq := tendsto_nhds_unique h hpc
    exact huniq.symm
  · intro hpc
    exact tendsto_blockAverageScalePressure_of_blockwise_limit_eq q m Ks Kt
      (t := t) (pc := pc) hlim hpc

/-- **The `hupper`-shaped readout from the numerical block-limit average.**  If
the block limits `p_c` exist and their average equals `p`, then the reference
scale pressure is eventually bounded by `p + ε`.  This is the most general form
of the readout bound supplied by the block pressure identification. -/
theorem eventually_kernelMarkedScalePressure_le_of_blockwise_limit_eq
    (q m J : ℕ) [NeZero m] (hq : 4 < q) (hm : 0 < m) (hJ : m ≤ 2 ^ J)
    (hJ2 : 2 ^ J ≤ 2 * m)
    (Ks : Kernel (Fin q → ℝ) A) [IsMarkovKernel Ks]
    (Kt : Kernel (Fin q → ℝ) B) [IsMarkovKernel Kt]
    {C G t : ℝ} (hC0 : 0 ≤ C) (hG0 : 0 ≤ G)
    {kin : A → B → (Fin q → ℝ) → ℝ} {g : A → B → ℝ}
    (hkin : Measurable (Function.uncurry (fun p : A × B => kin p.1 p.2)))
    (hkin_nonneg : ∀ a b v, 0 ≤ kin a b v)
    (hkin_bound : ∀ a b v, |kin a b v| ≤ C * ∑ l, v l ^ 2)
    (hkin_homog : ∀ a b (c : ℝ), 0 ≤ c → ∀ v : Fin q → ℝ,
      kin a b (fun l => c * v l) = c ^ 2 * kin a b v)
    (hg : Measurable (Function.uncurry g)) (hgb : ∀ a b, |g a b| ≤ G)
    {p : ℝ} {pc : (Fin q → Fin m) → ℝ}
    (hlim : ∀ c : Fin q → Fin m,
      Tendsto (fun L : ℝ =>
        kernelMarkedScalePressure q A B (blockLocalKernel Ks c)
          (blockLocalKernel Kt c) kin g L t) atTop (𝓝 (pc c)))
    (hpc : (1 / (((m ^ q : ℕ) : ℝ))) * ∑ c : Fin q → Fin m, pc c = p) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ R : ℝ in atTop,
      kernelMarkedScalePressure q A B Ks Kt kin g R t ≤ p + ε := by
  have hlimit := tendsto_blockAverageScalePressure_of_blockwise_limit_eq q m Ks Kt
    (t := t) (pc := pc) hlim hpc
  refine eventually_kernelMarkedScalePressure_le_of_blockPressureLimit (q := q)
    (m := m) (J := J) hq hm hJ hJ2 Ks Kt (t := t) hC0 hG0 hkin hkin_nonneg
    hkin_bound hkin_homog hg hgb ?_
  simpa only [blockAverageScalePressure] using hlimit

end OTSelector.Reconstruction
