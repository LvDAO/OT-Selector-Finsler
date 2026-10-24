import OTSelector.LinearAlgebra.RegraphedPositionKernel
import OTSelector.Geometry.Manifold.SameGraphInverse

/-!
# Actual focal isolation returns from graph time to original time

The same graph inverse preserves both the family label and the position derivative
kernel. Its injectivity prevents a distinct old time from returning to the central
graph time. Local regularity and Gauss normality therefore transfer punctured graph
position injectivity to punctured original-time position injectivity.
-/

open Set Filter
open scoped Topology

noncomputable section
namespace OTSelector.Geometry

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

omit [NormedSpace ℝ W] [FiniteDimensional ℝ W] in
/-- The actual clock of a genuine graph inverse sends punctured old-time neighborhoods
to punctured graph-time neighborhoods, without a global monotonicity assumption. -/
theorem curveGraphClock_tendsto_nhdsNE
    {γ : W × ℝ → E} (T : E ≃L[ℝ] (ℝ × V))
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ T (γ z)))
    {w₀ : W} {t₀ : ℝ} (hsource : (w₀, t₀) ∈ e.source)
    (hγ : ContinuousAt γ (w₀, t₀)) :
    Tendsto (fun t ↦ (T (γ (w₀, t))).1) (𝓝[≠] t₀)
      (𝓝[≠] (T (γ (w₀, t₀))).1) := by
  let a := fun t ↦ (T (γ (w₀, t))).1
  have hpath : ContinuousAt (fun t : ℝ ↦ (w₀, t)) t₀ :=
    continuousAt_const.prodMk continuousAt_id
  have hs : ∀ᶠ t in 𝓝 t₀, (w₀, t) ∈ e.source :=
    hpath.preimage_mem_nhds (e.open_source.mem_nhds hsource)
  have ha : ContinuousAt a t₀ := (T.continuousAt.comp hγ).fst.comp hpath
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨ha.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [nhdsWithin_le_nhds hs, self_mem_nhdsWithin] with t ht hne
  change a t ≠ a t₀
  intro heq
  have hem : e (w₀, t) = e (w₀, t₀) := by
    rw [he]
    exact Prod.ext rfl heq
  have ht_eq : t = t₀ := congrArg Prod.snd (e.injOn ht hsource hem)
  exact hne ht_eq

/-- Local genuine graph position injectivity away from its central time transfers to
the original position family, using the same inverse and actual normal covectors. -/
theorem curveGraphPosition_eventually_injective_original_time
    {γ : W × ℝ → E} (T : E ≃L[ℝ] (ℝ × V))
    {e : OpenPartialHomeomorph (W × ℝ) (W × ℝ)}
    (he : (e : W × ℝ → W × ℝ) = curveGraphCoordinateMap (fun z ↦ T (γ z)))
    {w₀ : W} {t₀ : ℝ} (hsource : (w₀, t₀) ∈ e.source)
    (hlocal : ∀ᶠ t in 𝓝 t₀,
      DifferentiableAt ℝ γ (w₀, t) ∧
      (T (fderiv ℝ γ (w₀, t) (0, 1))).1 ≠ 0 ∧
      ∃ p : E →L[ℝ] ℝ, p (fderiv ℝ γ (w₀, t) (0, 1)) ≠ 0 ∧
        ∀ u : W, p (fderiv ℝ (fun w ↦ γ (w, t)) w₀ u) = 0)
    (hgraph : ∀ᶠ r in 𝓝[≠] (T (γ (w₀, t₀))).1,
      Function.Injective (fderiv ℝ (fun w ↦
        (curveGraphPosition (fun z ↦ T (γ z)) e (w, r)).2) w₀)) :
    ∀ᶠ t in 𝓝[≠] t₀,
      Function.Injective (fderiv ℝ (fun w ↦ γ (w, t)) w₀) := by
  have hclock := curveGraphClock_tendsto_nhdsNE T he hsource
    hlocal.self_of_nhds.1.continuousAt
  have hpath : ContinuousAt (fun t : ℝ ↦ (w₀, t)) t₀ :=
    continuousAt_const.prodMk continuousAt_id
  have hs : ∀ᶠ t in 𝓝 t₀, (w₀, t) ∈ e.source :=
    hpath.preimage_mem_nhds (e.open_source.mem_nhds hsource)
  filter_upwards [hclock.eventually hgraph, nhdsWithin_le_nhds hlocal,
    nhdsWithin_le_nhds hs] with t hgraph_t hdata ht
  let q : W × ℝ := (w₀, (T (γ (w₀, t))).1)
  have heq : e (w₀, t) = q := by rw [he]; rfl
  have hq : q ∈ e.target := heq ▸ e.map_source ht
  have hinv : e.symm q = (w₀, t) := by rw [← heq]; exact e.left_inv ht
  have hγT : DifferentiableAt ℝ (fun z ↦ T (γ z)) (e.symm q) := by
    rw [hinv]
    exact T.differentiableAt.comp _ hdata.1
  have hDT : fderiv ℝ (fun z ↦ T (γ z)) (e.symm q) (0, 1) =
      T (fderiv ℝ γ (w₀, t) (0, 1)) := by
    rw [hinv]
    exact congrArg (fun D ↦ D (0, 1))
      (T.hasFDerivAt.comp (w₀, t) hdata.1.hasFDerivAt).fderiv
  have hv : (fderiv ℝ (fun z ↦ T (γ z)) (e.symm q) (0, 1)).1 ≠ 0 := by
    rw [hDT]
    exact hdata.2.1
  have hi := differentiableAt_curveGraphInverse_of_regular he hq hγT hv
  obtain ⟨p, hpv, hnormal⟩ := hdata.2.2
  have hkernel := curveGraphPosition_parameter_injective_iff T he hq
    (hinv.symm ▸ hdata.1) hi (by simpa only [hinv] using hdata.2.1) p
    (by simpa only [hinv] using hpv)
    (by simpa only [hinv, q] using hnormal)
  have hg : Function.Injective (fderiv ℝ (fun w ↦
      (curveGraphPosition (fun z ↦ T (γ z)) e (w, q.2)).2) q.1) := hgraph_t
  simpa only [hinv, q] using hkernel.mp hg

end OTSelector.Geometry
