import OTSelector.Analysis.ODE.Flow.Basic
import OTSelector.Analysis.ODE.Flow.C2FlowGluing
import OTSelector.Analysis.ODE.Flow.C2FlowRestart
import OTSelector.Analysis.ODE.Flow.LocalC2
import OTSelector.Analysis.ODE.Flow.NonautonomousVariation
/-!
# Mathematical definitions and lemmas

This module contains original proof blocks from OTSelector.Geometry.CompactC2Flow.
Each source unit retains its original namespace, conditions, objects, proof
details and mathematical-source documentation.
-/

/-! Original source unit: `OTSelector.Geometry.CompactC2Flow`; the selected original proof blocks follow. -/
section

/-!
Conditions: An actual orbit segment is compact and local C2 restarts and uniqueness/transitivity hold on the stated domains.

Objects: One common C2 family along the whole orbit segment and its actual variational equation.

Proof detail: Use local restart relations, connectedness and finite compact covering to continue the parameterized family and glue it by uniqueness.

Sources: Gerald Teschl, Section 2.6, pp. 50–51, overlap uniqueness, equation (2.63), and Theorem 2.13 (unique maximal solution) (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=61); Gerald Teschl, Section 2.4, Theorem 2.10, equation (2.51), proof induction and Theorem 2.11, pp. 46–48 (https://www.mat.univie.ac.at/~gerald/ftp/book-ode/ode.pdf#page=57); Terence Tao, Sections 1.6.2 and 1.8.1, compactness by finite subcovers, pp. 78 and 101–102; Section 1.8.3, Proposition 1.8.10, pp. 107–108 (finite products) (https://terrytao.wordpress.com/wp-content/uploads/2012/12/gsm-117-tao3-epsilon1.pdf#page=110).
Relation: Compact parameterized continuation consequence of local ODE theory, with actual family/domain hypotheses.
-/

/-!
# C2 families along a compact orbit segment

Local smooth-field flows are restarted and glued along a given actual orbit.
Connectedness propagates the common initial neighborhood across any finite segment.
-/

open Set Filter Metric
open scoped Topology ContDiff NNReal

namespace OTSelector.Geometry.LocalFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private structure OrbitFamily (X : E → E) (U : Set E) (α : ℝ → E)
    (I : Set ℝ) (s t : ℝ) where
  B : Set E
  J : Set ℝ
  Ψ : E × ℝ → E
  openB : IsOpen B
  memB : α s ∈ B
  openJ : IsOpen J
  connJ : IsPreconnected J
  subJ : J ⊆ I
  memS : s ∈ J
  memT : t ∈ J
  smooth : ContDiffOn ℝ 2 Ψ (B ×ˢ J)
  range : MapsTo Ψ (B ×ˢ J) U
  ode : ∀ w ∈ B, ∀ u ∈ J, HasDerivAt (fun v ↦ Ψ (w, v)) (X (Ψ (w, u))) u
  initial : ∀ w ∈ B, Ψ (w, s) = w
  central : ∀ u ∈ J, Ψ (α s, u) = α u

private theorem orbitFamily_of_localFlow
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {α : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    (hα : ∀ t ∈ I, HasDerivAt α (X (α t)) t)
    {p : E} {r : ℝ≥0} {τ T : ℝ} {Φ : E × ℝ → E}
    (hΦ : IsLocalFlow (fun _ ↦ X) τ p r (τ - T) (τ + T) Φ) (hT : 0 < T)
    (hmap : MapsTo Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)) U)
    (hC2 : ContDiffOn ℝ 2 Φ (closedBall p r ×ˢ Icc (τ - T) (τ + T)))
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) (hp : α s ∈ ball p r)
    (hst : t ∈ Ioo (s - T) (s + T)) : Nonempty (OrbitFamily X U α I s t) := by
  obtain ⟨B, hB, hBs, _, _, hsm, hm, hsT, hi, ho, _⟩ :=
    hΦ.exists_c2Restart hT hmap hC2 isOpen_univ contDiffOn_id (mem_univ (α s)) hp s
  let Ψ : E × ℝ → E := fun q ↦ Φ (q.1, τ + (q.2 - s))
  let J := I ∩ Ioo (s - T) (s + T)
  have hJ : IsOpen J := hI.inter isOpen_Ioo
  have hJc : IsPreconnected J := (hc.ordConnected.inter ordConnected_Ioo).isPreconnected
  have hsub : B ×ˢ J ⊆ B ×ˢ Ioo (s - T) (s + T) :=
    prod_mono Subset.rfl inter_subset_right
  have hcent : EqOn (fun u ↦ Ψ (α s, u)) α J :=
    integralCurve_eqOn_of_contDiffOn hU hX hJ hJc
      (fun u hu ↦ hm ⟨hBs, hu.2⟩) (fun u hu ↦ ho (α s) hBs u hu.2)
      (fun u hu ↦ hα u hu.1) ⟨hs, hsT⟩ (hi (α s) hBs)
  exact ⟨{
    B := B, J := J, Ψ := Ψ, openB := hB, memB := hBs, openJ := hJ,
    connJ := hJc, subJ := inter_subset_left, memS := ⟨hs, hsT⟩, memT := ⟨ht, hst⟩,
    smooth := hsm.mono hsub, range := hm.mono hsub Subset.rfl,
    ode := fun w hw u hu ↦ ho w hw u hu.2, initial := hi, central := hcent }⟩

private theorem orbitFamily_local [FiniteDimensional ℝ E]
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {α : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    (hm : MapsTo α I U) (hα : ∀ t ∈ I, HasDerivAt α (X (α t)) t)
    (s : ℝ) (hs : s ∈ I) : ∀ᶠ t in 𝓝[I] s,
      Nonempty (OrbitFamily X U α I s t) ∧ Nonempty (OrbitFamily X U α I t s) := by
  obtain ⟨r, T, hr, hT, Φ, hΦ, hmap, hC2, _⟩ :=
    exists_c2Flow_in_open hU hX (hm hs) s
  have hp : α s ∈ ball (α s) (r : ℝ) := mem_ball_self (by exact_mod_cast hr)
  have ha : ContinuousAt α s := (hα s hs).continuousAt
  have hnear : ∀ᶠ t in 𝓝 s, α t ∈ ball (α s) (r : ℝ) :=
    ha.eventually (isOpen_ball.mem_nhds hp)
  have htnear : Ioo (s - T) (s + T) ∈ 𝓝 s := Ioo_mem_nhds (by linarith) (by linarith)
  filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
    (show ∀ᶠ t in 𝓝 s, t ∈ Ioo (s - T) (s + T) from htnear).filter_mono
      nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with t htp hts htI
  refine ⟨orbitFamily_of_localFlow hU hX hI hc hα hΦ hT hmap hC2 hs htI hp hts, ?_⟩
  apply orbitFamily_of_localFlow hU hX hI hc hα hΦ hT hmap hC2 htI hs htp
  constructor <;> linarith [hts.1, hts.2]

private theorem orbitFamily_trans
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {α : ℝ → E} {I : Set ℝ} {s y t : ℝ}
    (hf : Nonempty (OrbitFamily X U α I s y))
    (hg : Nonempty (OrbitFamily X U α I y t)) : Nonempty (OrbitFamily X U α I s t) := by
  obtain ⟨f⟩ := hf
  obtain ⟨g⟩ := hg
  let seed : E → E := fun w ↦ f.Ψ (w, y)
  have hseed : ContDiffOn ℝ 2 seed f.B :=
    f.smooth.comp (contDiffOn_id.prodMk contDiffOn_const) (fun w hw ↦ ⟨hw, f.memT⟩)
  let B := f.B ∩ seed ⁻¹' g.B
  have hB : IsOpen B := hseed.continuousOn.isOpen_inter_preimage f.openB g.openB
  have hBs : α s ∈ B := ⟨f.memB, by simpa [seed, f.central y f.memT] using g.memB⟩
  let Θ : E × ℝ → E := fun q ↦ g.Ψ (seed q.1, q.2)
  have hΘ : ContDiffOn ℝ 2 Θ (B ×ˢ g.J) :=
    g.smooth.comp
      (((hseed.mono inter_subset_left).comp contDiffOn_fst (fun _ hz ↦ hz.1)).prodMk
        contDiffOn_snd) (fun _ hz ↦ ⟨hz.1.2, hz.2⟩)
  have hΘmap : MapsTo Θ (B ×ˢ g.J) U := fun _ hz ↦ g.range ⟨hz.1.2, hz.2⟩
  have hΘode : ∀ w ∈ B, ∀ u ∈ g.J,
      HasDerivAt (fun v ↦ Θ (w, v)) (X (Θ (w, u))) u :=
    fun _ hw u hu ↦ g.ode _ hw.2 u hu
  have hsub : B ×ˢ f.J ⊆ f.B ×ˢ f.J := prod_mono inter_subset_left Subset.rfl
  obtain ⟨Γ, hΓ, hΓmap, hΓode, hleft, hright, _, _⟩ :=
    exists_glued_c2Family hU hX hB f.openJ g.openJ
      (f.connJ.ordConnected.inter g.connJ.ordConnected).isPreconnected
      (f.smooth.mono hsub) hΘ (f.range.mono hsub Subset.rfl) hΘmap
      (fun w hw u hu ↦ f.ode w hw.1 u hu) hΘode ⟨f.memT, g.memS⟩
      (fun w hw ↦ (g.initial (seed w) hw.2).symm)
  refine ⟨{
    B := B, J := f.J ∪ g.J, Ψ := Γ, openB := hB, memB := hBs,
    openJ := f.openJ.union g.openJ,
    connJ := f.connJ.union' ⟨y, f.memT, g.memS⟩ g.connJ,
    subJ := union_subset f.subJ g.subJ, memS := Or.inl f.memS, memT := Or.inr g.memT,
    smooth := hΓ, range := hΓmap, ode := hΓode,
    initial := ?_, central := ?_ }⟩
  · intro w hw
    exact (hleft ⟨hw, f.memS⟩).trans (f.initial w hw.1)
  · intro u hu
    rcases hu with hf | hg
    · exact (hleft ⟨hBs, hf⟩).trans (f.central u hf)
    · rw [hright ⟨hBs, hg⟩]
      change g.Ψ (f.Ψ (α s, y), u) = α u
      rw [f.central y f.memT]
      exact g.central u hg

private theorem orbitFamily_exists [FiniteDimensional ℝ E]
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {α : ℝ → E} {I : Set ℝ} (hI : IsOpen I) (hc : IsPreconnected I)
    (hm : MapsTo α I U) (hα : ∀ t ∈ I, HasDerivAt α (X (α t)) t)
    {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) : Nonempty (OrbitFamily X U α I s t) := by
  apply hc.induction₂' (fun s t ↦ Nonempty (OrbitFamily X U α I s t))
    (orbitFamily_local hU hX hI hc hm hα) ?_ hs ht
  intro s y t _ _ _ hf hg
  exact orbitFamily_trans hU hX hf hg

private theorem exists_open_interval_enlargement {I : Set ℝ} (hI : IsOpen I)
    {a b : ℝ} (hab : a ≤ b) (hsub : Icc a b ⊆ I) :
    ∃ ε : ℝ, 0 < ε ∧ Ioo (a - ε) (b + ε) ⊆ I := by
  obtain ⟨la, ua, ha, hIa⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hsub ⟨le_rfl, hab⟩))
  obtain ⟨lb, ub, hb, hIb⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds (hsub ⟨hab, le_rfl⟩))
  let ε := min (a - la) (ub - b)
  have he : 0 < ε := lt_min (sub_pos.mpr ha.1) (sub_pos.mpr hb.2)
  have hel : ε ≤ a - la := min_le_left _ _
  have her : ε ≤ ub - b := min_le_right _ _
  refine ⟨ε, he, ?_⟩
  intro t ht
  by_cases hta : t < a
  · exact hIa ⟨by linarith [ht.1], hta.trans ha.2⟩
  by_cases htb : b < t
  · exact hIb ⟨hb.1.trans htb, by linarith [ht.2]⟩
  exact hsub ⟨le_of_not_gt hta, le_of_not_gt htb⟩

/-- A smooth finite-dimensional field admits a genuine joint C2 family on a common
neighborhood of any compact segment of an actual orbit. Both the initial derivative
and the actual parameter-variation equation follow from the constructed family. -/
theorem exists_c2Family_along_compact_orbit [FiniteDimensional ℝ E]
    {X : E → E} {U : Set E} (hU : IsOpen U) (hX : ContDiffOn ℝ ∞ X U)
    {α : ℝ → E} {I : Set ℝ} (hI : IsOpen I)
    (hm : MapsTo α I U) (hα : ∀ t ∈ I, HasDerivAt α (X (α t)) t)
    {a b t₀ : ℝ} (hab : a ≤ b) (hseg : Icc a b ⊆ I) (ht₀ : t₀ ∈ Icc a b) :
    ∃ (r ε : ℝ), 0 < r ∧ 0 < ε ∧ Ioo (a - ε) (b + ε) ⊆ I ∧
      ∃ Φ : E × ℝ → E,
        ContDiffOn ℝ 2 Φ (ball (α t₀) r ×ˢ Ioo (a - ε) (b + ε)) ∧
        MapsTo Φ (ball (α t₀) r ×ˢ Ioo (a - ε) (b + ε)) U ∧
        (∀ w ∈ ball (α t₀) r, Φ (w, t₀) = w) ∧
        (∀ t ∈ Ioo (a - ε) (b + ε), Φ (α t₀, t) = α t) ∧
        (∀ w ∈ ball (α t₀) r, ∀ t ∈ Ioo (a - ε) (b + ε),
          HasDerivAt (fun s ↦ Φ (w, s)) (X (Φ (w, t))) t) ∧
        fderiv ℝ (fun w ↦ Φ (w, t₀)) (α t₀) = ContinuousLinearMap.id ℝ E ∧
        ∀ w ∈ ball (α t₀) r, ∀ t ∈ Ioo (a - ε) (b + ε), ∀ ξ : E,
          HasDerivAt (fun s ↦ fderiv ℝ (fun v ↦ Φ (v, s)) w ξ)
            (fderiv ℝ X (Φ (w, t)) (fderiv ℝ (fun v ↦ Φ (v, t)) w ξ)) t := by
  obtain ⟨ε₀, hε₀, hI₀⟩ := exists_open_interval_enlargement hI hab hseg
  let I₀ := Ioo (a - ε₀) (b + ε₀)
  have hsub₀ : Icc a b ⊆ I₀ := Icc_subset_Ioo (by linarith) (by linarith)
  obtain ⟨f⟩ := orbitFamily_exists hU hX isOpen_Ioo isPreconnected_Ioo
    (hm.mono hI₀ Subset.rfl) (fun t ht ↦ hα t (hI₀ ht))
    (hsub₀ ht₀) (hsub₀ ⟨le_rfl, hab⟩)
  obtain ⟨g⟩ := orbitFamily_exists hU hX isOpen_Ioo isPreconnected_Ioo
    (hm.mono hI₀ Subset.rfl) (fun t ht ↦ hα t (hI₀ ht))
    (hsub₀ ht₀) (hsub₀ ⟨hab, le_rfl⟩)
  let B := f.B ∩ g.B
  have hB : IsOpen B := f.openB.inter g.openB
  have hB₀ : α t₀ ∈ B := ⟨f.memB, g.memB⟩
  have hfsub : B ×ˢ f.J ⊆ f.B ×ˢ f.J := prod_mono inter_subset_left Subset.rfl
  have hgsub : B ×ˢ g.J ⊆ g.B ×ˢ g.J := prod_mono inter_subset_right Subset.rfl
  obtain ⟨Φ, hΦ, hΦmap, hΦode, hf, hg, _, _⟩ :=
    exists_glued_c2Family hU hX hB f.openJ g.openJ
      (f.connJ.ordConnected.inter g.connJ.ordConnected).isPreconnected
      (f.smooth.mono hfsub) (g.smooth.mono hgsub)
      (f.range.mono hfsub Subset.rfl) (g.range.mono hgsub Subset.rfl)
      (fun w hw t ht ↦ f.ode w hw.1 t ht) (fun w hw t ht ↦ g.ode w hw.2 t ht)
      ⟨f.memS, g.memS⟩ (fun w hw ↦ (f.initial w hw.1).trans (g.initial w hw.2).symm)
  have hJ : IsOpen (f.J ∪ g.J) := f.openJ.union g.openJ
  have hJc : IsPreconnected (f.J ∪ g.J) :=
    f.connJ.union' ⟨t₀, f.memS, g.memS⟩ g.connJ
  have hJsub : f.J ∪ g.J ⊆ I := (union_subset f.subJ g.subJ).trans hI₀
  have hsegJ : Icc a b ⊆ f.J ∪ g.J :=
    hJc.ordConnected.out (Or.inl f.memT) (Or.inr g.memT)
  obtain ⟨ε, hε, hεJ⟩ := exists_open_interval_enlargement hJ hab hsegJ
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp hB (α t₀) hB₀
  have hdom : ball (α t₀) r ×ˢ Ioo (a - ε) (b + ε) ⊆ B ×ˢ (f.J ∪ g.J) :=
    prod_mono hrB hεJ
  have hsm := hΦ.mono hdom
  have hinit (w : E) (hw : w ∈ ball (α t₀) r) : Φ (w, t₀) = w :=
    (hf ⟨hrB hw, f.memS⟩).trans (f.initial w (hrB hw).1)
  refine ⟨r, ε, hr, hε, hεJ.trans hJsub, Φ, hsm,
    hΦmap.mono hdom Subset.rfl, hinit, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rcases hεJ ht with ht | ht
    · exact (hf ⟨hB₀, ht⟩).trans (f.central t ht)
    · exact (hg ⟨hB₀, ht⟩).trans (g.central t ht)
  · intro w hw t ht
    exact hΦode w (hrB hw) t (hεJ ht)
  · have heq : (fun w ↦ Φ (w, t₀)) =ᶠ[𝓝 (α t₀)] id :=
      Filter.eventually_of_mem (ball_mem_nhds (α t₀) hr) hinit
    exact heq.fderiv_eq.trans (fderiv_id)
  · intro w hw t ht ξ
    exact hasDerivAt_parameterVariation_of_nonautonomousODE (X := fun _ ↦ X)
      (isOpen_ball.prod isOpen_Ioo) hsm
      (fun q hq ↦ hΦode q.1 (hrB hq.1) q.2 (hεJ hq.2)) ⟨hw, ht⟩
      ((hX.contDiffAt (hU.mem_nhds (hΦmap (hdom ⟨hw, ht⟩)))).differentiableAt
        (by simp)) ξ

end OTSelector.Geometry.LocalFlow

end
