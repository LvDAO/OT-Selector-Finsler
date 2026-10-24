import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.AddTorsor
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.LocallyFinite
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.Order.Compact
import OTSelector.Analysis.Calculus.Whitney.Basic
import OTSelector.Analysis.Calculus.Whitney.Proofs.Boundary
import OTSelector.Analysis.Calculus.Whitney.Proofs.Cover
import OTSelector.Analysis.Calculus.Whitney.Proofs.Cutoff
import OTSelector.Analysis.Calculus.Whitney.Proofs.Hessian
import OTSelector.Analysis.Calculus.Whitney.Proofs.Partition

/-!
## Lemma skeleton

* **Conditions:** Finite-dimensional real normed domain, arbitrary real normed target, compact K, a Lipschitz prescribed continuous-linear-map field D and quadratic affine-remainder compatibility.
* **Objects:** A genuine global C1 extension smooth off K with uniformly bounded actual Hessian near K; then a compactly supported extension with globally Lipschitz actual derivative matching the full first jet.
* **Proof detail:** Construct the actual locally finite affine interpolation. Quadratic jet compatibility cancels inverse-square weight Hessian scale and inverse-radius first-derivative scale. Boundary gluing gives C1; a constructed compact cutoff and derivative gluing give global C1,1.

## Mathematical sources

* Aris Daniilidis; Mounir Haddou; Erwan Le Gruyer; Olivier Ley, *Explicit formulas for C1,1 Glaeser-Whitney extensions of 1-Taylor fields in Hilbert spaces (author manuscript)*, Introduction, equation (1.1), pp. 1–2; Section 3, Theorem 3.1, pp. 6–7.
  https://www.arisdaniilidis.at/DHLL.pdf#page=2
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 3, pp. 64–65, equations (3.1)–(3.2); Section 6, p. 66, equations (6.1)–(6.3).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=2
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Sections 7–10, pp. 67–69: smooth localization, complement decomposition, normalized weights (9.2), derivative scaling (10.1).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=5
* Hassler Whitney, *Analytic Extensions of Differentiable Functions Defined in Closed Sets, Transactions of the AMS 36(1), 63–89 (1934)*, Section 4, Theorem I, p. 65; Section 11, Lemma 2 and proof, pp. 69–71, equations (11.1)–(11.8).
  https://www.ams.org/journals/tran/1934-036-01/S0002-9947-1934-1501735-3/S0002-9947-1934-1501735-3.pdf#page=3
* Jiří Lebl, *Basic Analysis II: Introduction to Real Analysis, Volume II (version 6.3, 15 May 2026)*, Section 8.4.1, Lemma 8.4.1 and Proposition 8.4.2, pp. 46–47.
  https://www.jirka.org/ra/realanal2.pdf#page=46

**Relationship to the sources:** This proves a compact first-jet C1,1 extension in normed/vector-valued form. The scalar-Hilbert Glaeser–Whitney theorem supplies an exact compatibility comparison; the implementation uses the partition proof and claims no optimal derivative constant.
-/

/-!
# A constructed C1,1 extension of a compact Whitney first jet

The actual normalized Whitney affine interpolation extends a quadratic first jet with
Lipschitz derivative. It is globally C1, smooth off the compact set, and its actual
Hessian is bounded on the unit-distance neighborhood outside that set. A constructed
smooth cutoff and closed-set derivative gluing then yield a compactly supported extension
with a globally Lipschitz actual derivative, matching the original first jet.
-/

open Set Filter Metric Function
open scoped Topology ContDiff BigOperators NNReal

noncomputable section
namespace OTSelector.Geometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

local instance quantitativeHessianNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance quantitativeHessianNormedSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

/-- A compact quadratic Whitney first jet with Lipschitz derivative has a genuinely
constructed C1 extension, smooth off the compact set, with uniformly bounded actual
Hessian within unit distance of that set. -/
theorem exists_whitney_extension_bounded_hessian_near {K : Set E} (hK : IsCompact K)
    {f : E → F} {D : E → E →L[ℝ] F} {L : ℝ≥0}
    (hD : LipschitzOnWith L D K)
    (hquad : ∀ u ∈ K, ∀ v ∈ K,
      ‖f u - f v - D v (u - v)‖ ≤ (L : ℝ) * ‖u - v‖ ^ 2) :
    ∃ (G : E → F) (C : ℝ), 0 ≤ C ∧ ContDiff ℝ 1 G ∧ EqOn G f K ∧
      (∀ b ∈ K, HasFDerivAt G (D b) b) ∧ ContDiffOn ℝ ∞ G Kᶜ ∧
      ∀ x : E, x ∉ K → infDist x K < 1 →
        ‖fderiv ℝ (fderiv ℝ G) x‖ ≤ C := by
  classical
  have hWhitney : ∀ ε > 0, ∃ δ > 0, ∀ u ∈ K, ∀ v ∈ K, dist u v < δ →
      ‖f u - f v - D v (u - v)‖ ≤ ε * ‖u - v‖ := by
    intro ε hε
    refine ⟨ε / ((L : ℝ) + 1), by positivity, ?_⟩
    intro u hu v hv huv
    have hh : (L : ℝ) * ‖u - v‖ ≤ ε := by
      rw [dist_eq_norm] at huv
      have := (lt_div_iff₀ (by positivity : 0 < (L : ℝ) + 1)).mp huv
      nlinarith [norm_nonneg (u - v), L.coe_nonneg]
    exact (hquad u hu v hv).trans (by nlinarith [norm_nonneg (u - v)])
  by_cases hne : K.Nonempty
  · obtain ⟨C, A₁, A₂, hA₁, hA₂, hC, _, hsupp, hLF, hprops⟩ :=
      exists_whitney_partition_secondDerivative hK.isClosed hne
    let ψ : C → E → ℝ := whitneyPartitionWeight K C
    choose a ha hdist using fun c : C ↦ hK.exists_infDist_eq_dist hne (c : E)
    let G : E → F := fun x ↦ if x ∈ K then f x else
      ∑ᶠ c : C, ψ c x • whitneyAffineJet f D (a c) x
    have hGK : EqOn G f K := by intro x hx; simp [G, hx]
    have hlocalData (x : E) (hx : x ∉ K) :
        ∃ s : Finset C, G =ᶠ[𝓝 x] whitneyBlend s ψ f D a ∧
          (∀ c ∈ s, ContDiffAt ℝ ∞ (ψ c) x) ∧ (∀ c ∈ s, 0 ≤ ψ c x) ∧
          ((fun y ↦ ∑ c ∈ s, ψ c y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ)) ∧
          (∀ c ∈ s, a c ∈ K ∧ ‖x - a c‖ ≤ 2 * infDist x K) ∧
          (infDist x K < 1 →
            (∑ c ∈ s, ‖fderiv ℝ (ψ c) x‖) ≤ (16 * A₁) / infDist x K ∧
            (∑ c ∈ s, ‖fderiv ℝ (fderiv ℝ (ψ c)) x‖) ≤
              (256 * A₂) / (infDist x K) ^ 2) := by
      obtain ⟨s, hs, hout⟩ := exists_whitney_support_finset hK.isClosed hLF hx
      have hz : ∀ᶠ y in 𝓝 x, ∀ c ∉ s, ψ c y = 0 := by
        filter_upwards [hout] with y hy c hc
        apply notMem_support.mp
        exact fun h ↦ hy c hc (hsupp c (subset_tsupport _ h))
      have hzero (c : C) (hc : c ∉ s) : ψ c =ᶠ[𝓝 x] fun _ ↦ 0 :=
        hz.mono fun _ hy ↦ hy c hc
      have hgerm : G =ᶠ[𝓝 x] whitneyBlend s ψ f D a := by
        filter_upwards [hz, hK.isClosed.isOpen_compl.mem_nhds hx] with y hy hyK
        dsimp only [G, whitneyBlend]
        simp only [show ¬ y ∈ K from hyK, ↓reduceIte]
        apply finsum_eq_sum_of_support_subset
        intro c hc
        by_contra hcs
        exact hc (by
          change ψ c y • whitneyAffineJet f D (a c) y = 0
          rw [hy c hcs, zero_smul])
      have hone : (fun y ↦ ∑ c ∈ s, ψ c y) =ᶠ[𝓝 x] fun _ ↦ (1 : ℝ) := by
        filter_upwards [hz, hK.isClosed.isOpen_compl.mem_nhds hx] with y hy hyK
        have heq : (∑ᶠ c, ψ c y) = ∑ c ∈ s, ψ c y := by
          apply finsum_eq_sum_of_support_subset
          intro c hc
          by_contra hcs
          exact hc (hy c hcs)
        rw [← heq]
        exact (hprops y hyK).2.2.1
      refine ⟨s, hgerm, fun c _ ↦ (hprops x hx).2.2.2.1 c,
        fun c _ ↦ (hprops x hx).1 c, hone, ?_, ?_⟩
      · intro c hc
        refine ⟨ha c, ?_⟩
        have hd := mem_closedBall.mp (hs c hc)
        have hr : whitneyCoverRadius K c ≤ infDist (c : E) K / 16 := min_le_right _ _
        have hl := (infDist_comparable_on_whitneyCoverRadius_ball (hs c hc)).1
        have ht := dist_triangle x (c : E) (a c)
        rw [← hdist c] at ht
        rw [← dist_eq_norm]
        have hn := infDist_nonneg (x := (c : E)) (s := K)
        linarith
      · intro hsmall
        have hnorm₁ : support (fun c ↦ ‖fderiv ℝ (ψ c) x‖) ⊆ (s : Set C) := by
          intro c hc
          by_contra hcs
          have hd := (hzero c hcs).fderiv_eq (𝕜 := ℝ)
          exact hc (by
            change ‖fderiv ℝ (ψ c) x‖ = 0
            rw [hd, fderiv_const_apply, norm_zero])
        have hnorm₂ : support (fun c ↦ ‖fderiv ℝ (fderiv ℝ (ψ c)) x‖) ⊆
            (s : Set C) := by
          intro c hc
          by_contra hcs
          have hd := ((hzero c hcs).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
          have hh : fderiv ℝ (fderiv ℝ (ψ c)) x = 0 := by
            simpa only [fderiv_fun_const, fderiv_zero, Pi.zero_apply] using hd
          exact hc (by
            change ‖fderiv ℝ (fderiv ℝ (ψ c)) x‖ = 0
            rw [hh, norm_zero])
        have hr : whitneyCoverRadius K x = infDist x K / 16 := min_eq_right (by linarith)
        constructor
        · rw [← finsum_eq_sum_of_support_subset _ hnorm₁]
          have hh := (hprops x hx).2.2.2.2.2.2.1
          rw [hr] at hh
          convert hh using 1; ring
        · rw [← finsum_eq_sum_of_support_subset _ hnorm₂]
          have hh := (hprops x hx).2.2.2.2.2.2.2
          rw [hr] at hh
          convert hh using 1; ring
    have hlocal (x : E) (hx : x ∉ K) :
        HasWhitneyLocalBlend K ψ f D a G (16 * A₁) x := by
      obtain ⟨s, hgerm, hφ, hpos, hone, hanchor, hmass⟩ := hlocalData x hx
      exact ⟨s, hgerm, fun c hc ↦ (hφ c hc).of_le (by simp), hpos,
        hone, hanchor, fun hsmall ↦ (hmass hsmall).1⟩
    obtain ⟨hG, hDG⟩ := contDiff_whitney_of_local_blends hK (by positivity)
      hD.continuousOn hWhitney hGK hlocal
    have hGsmooth : ContDiffOn ℝ ∞ G Kᶜ := by
      intro x hx
      obtain ⟨s, hgerm, hφ, _⟩ := hlocalData x hx
      have hc : ContDiffAt ℝ ∞ (whitneyBlend s ψ f D a) x := by
        apply ContDiffAt.sum
        intro c hc
        apply (hφ c hc).smul
        exact contDiffAt_const.add ((D (a c)).contDiff.contDiffAt.comp x
          (contDiffAt_id.sub contDiffAt_const))
      exact (hc.congr_of_eventuallyEq hgerm).contDiffWithinAt
    refine ⟨G, 15 * (L : ℝ) * (256 * A₂) + 6 * (L : ℝ) * (16 * A₁),
      by positivity, hG, hGK, hDG, hGsmooth, ?_⟩
    intro x hx hsmall
    obtain ⟨b, hb, hbdist⟩ := hK.exists_infDist_eq_dist hne x
    have hr : 0 < infDist x K := (hK.isClosed.notMem_iff_infDist_pos hne).mp hx
    have hxb : ‖x - b‖ = infDist x K := by
      simpa only [dist_eq_norm] using hbdist.symm
    obtain ⟨s, hgerm, hφ, _, hone, hanchor, hmass⟩ := hlocalData x hx
    have hrem (c : C) (hc : c ∈ s) :
        ‖f (a c) - f b - D b (a c - b)‖ ≤ (L : ℝ) * ‖a c - b‖ ^ 2 :=
      hquad _ (hanchor c hc).1 b hb
    have hjet (c : C) (hc : c ∈ s) :
        ‖D (a c) - D b‖ ≤ (L : ℝ) * ‖a c - b‖ := by
      simpa only [dist_eq_norm] using hD.dist_le_mul (a c) (hanchor c hc).1 b hb
    rw [(hgerm.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]
    exact norm_hessian_whitneyBlend_boundary_le s ψ f D a hr L.coe_nonneg
      (fun c hc ↦ (hφ c hc).of_le (by simp)) hone hxb.le
      (fun c hc ↦ (hanchor c hc).2) hrem hjet (hmass hsmall).1 (hmass hsmall).2
  · have hempty : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ ↦ 0, 0, le_rfl, contDiff_const, ?_, ?_, contDiff_const.contDiffOn, ?_⟩
    · simp [hempty]
    · simp [hempty]
    · intro x _ _
      simp only [fderiv_fun_const, fderiv_zero, Pi.zero_apply, norm_zero, le_refl]


/-- A compact quadratic Whitney first jet with Lipschitz derivative extends to a
compactly supported global C1 map with a globally Lipschitz actual derivative. The
extension, smooth cutoff and Lipschitz constant are constructed from the original jet.
No given extension, cover, partition or derivative-bound assumption is required. -/
theorem exists_contDiff_one_lipschitz_fderiv_extension {K : Set E} (hK : IsCompact K)
    {f : E → F} {D : E → E →L[ℝ] F} {L : ℝ≥0}
    (hD : LipschitzOnWith L D K)
    (hquad : ∀ u ∈ K, ∀ v ∈ K,
      ‖f u - f v - D v (u - v)‖ ≤ (L : ℝ) * ‖u - v‖ ^ 2) :
    ∃ (H : E → F) (C : ℝ≥0), ContDiff ℝ 1 H ∧ HasCompactSupport H ∧
      ContDiffOn ℝ ∞ H Kᶜ ∧ LipschitzWith C (fderiv ℝ H) ∧ EqOn H f K ∧
      ∀ b ∈ K, HasFDerivAt H (D b) b := by
  obtain ⟨G, A, _, hG, hval, hder, hOff, hnear⟩ :=
    exists_whitney_extension_bounded_hessian_near hK hD hquad
  have htrace : LipschitzOnWith L (fderiv ℝ G) K := by
    intro x hx y hy
    rw [(hder x hx).fderiv, (hder y hy).fderiv]
    exact hD hx hy
  obtain ⟨η, _, _, _, _, hH, hsupport, hHOff, hvalue, hderiv, C, hLip⟩ :=
    exists_compact_cutoff_lipschitz_fderiv hK hG hOff htrace zero_lt_one hnear
  refine ⟨fun x ↦ η x • G x, C, hH, hsupport, hHOff, hLip, ?_, ?_⟩
  · exact fun b hb ↦ (hvalue hb).trans (hval hb)
  · intro b hb
    exact (hH.differentiable one_ne_zero b).hasFDerivAt.congr_fderiv
      ((hderiv hb).trans (hder b hb).fderiv)

end OTSelector.Geometry
