import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
Generic closed-set Taylor-series summation.

This is a helper for the Seeley C^∞ extension. It does **not** construct the
Seeley series, glue cutoff jets, or identify boundary moments. Those remain the
Seeley worker's responsibility. The theorem takes genuine termwise
`HasFTaylorSeriesUpToOn` data and a summable uniform majorant of every Taylor
order, and returns the summed Taylor field on a convex set.

Global `contDiff_tsum` is not used: that theorem needs ambient `ContDiff`, which
is the wrong predicate on a closed half-ball. Differentiation is performed
*within* `s` by a convex mean-value estimate on finite tails, then passing to
the uniform limit. The same convex-segment argument is the engine behind
`hasFDerivWithinAt_closure_of_tendsto_fderiv`; applying it directly on `s`
avoids an interior-only `HasFDerivAt` detour.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Set Filter Asymptotics
open scoped Topology ContDiff

namespace LeeSmooth.WithinTaylorSums

universe u v w

variable {E : Type u} {F : Type v} {ι : Type w}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-! ## Coefficientwise summability -/

lemma summable_taylorCoeff
    (p : ι → E → FormalMultilinearSeries ℝ E F)
    {u : ι → ℝ} (hu : Summable u) {m : ℕ} {x : E}
    (hbound : ∀ i, ‖p i x m‖ ≤ u i) :
    Summable fun i : ι => p i x m :=
  Summable.of_norm_bounded hu hbound

omit [CompleteSpace F] in
lemma tsum_curryLeft_taylorCoeff
    (p : ι → FormalMultilinearSeries ℝ E F) {m : ℕ} :
    (∑' i : ι, p i m.succ).curryLeft = ∑' i : ι, (p i m.succ).curryLeft :=
  (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin m.succ => E) F).toContinuousLinearEquiv.map_tsum
    (L := SummationFilter.unconditional ι)

/-- Order-zero Taylor coefficients identify the summed function. -/
lemma tsum_curry0_of_hasFTaylorSeriesUpToOn {s : Set E}
    {f : ι → E → F} {p : ι → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ i, HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) (f i) (p i) s)
    {x : E} (hx : x ∈ s) :
    (∑' i : ι, p i x 0).curry0 = ∑' i : ι, f i x := by
  have hcoe (q : E [×0]→L[ℝ] F) :
      q.curry0 = continuousMultilinearCurryFin0 ℝ E F q :=
    (ContinuousMultilinearMap.curry0_apply q).trans
      (continuousMultilinearCurryFin0_apply q).symm
  have hmap :
      continuousMultilinearCurryFin0 ℝ E F (∑' i : ι, p i x 0) =
        ∑' i : ι, continuousMultilinearCurryFin0 ℝ E F (p i x 0) :=
    (continuousMultilinearCurryFin0 ℝ E F).toContinuousLinearEquiv.map_tsum
      (L := SummationFilter.unconditional ι) (f := fun i : ι => p i x 0)
  rw [hcoe, hmap]
  exact tsum_congr fun i => (hcoe (p i x 0)).symm.trans ((hp i).zero_eq x hx)

lemma tendstoUniformlyOn_tsum_taylorCoeff {s : Set E}
    (p : ι → E → FormalMultilinearSeries ℝ E F)
    {u : ι → ℝ} (hu : Summable u) {m : ℕ}
    (hbound : ∀ i x, x ∈ s → ‖p i x m‖ ≤ u i) :
    TendstoUniformlyOn (fun t : Finset ι => fun x => ∑ i ∈ t, p i x m)
      (fun x => ∑' i : ι, p i x m) atTop s :=
  tendstoUniformlyOn_tsum hu hbound

lemma continuousOn_tsum_taylorCoeff {s : Set E}
    {p : ι → E → FormalMultilinearSeries ℝ E F} {m : ℕ}
    (hcont : ∀ i, ContinuousOn (p i · m) s)
    {u : ι → ℝ} (hu : Summable u)
    (hbound : ∀ i x, x ∈ s → ‖p i x m‖ ≤ u i) :
    ContinuousOn (fun x => ∑' i : ι, p i x m) s :=
  continuousOn_tsum hcont hu hbound

/-! ## Within-derivative of a uniformly majorized series on a convex set -/

/-- Mean-value bound for a finite subsum of the complement of `t`. -/
private lemma norm_finset_compl_sub_le {s : Set E} (hs : Convex ℝ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u : ι → ℝ}
    (hf : ∀ i y, y ∈ s → HasFDerivWithinAt (f i) (f' i y) s y)
    (hu : Summable u) (hfu : ∀ i y, y ∈ s → ‖f' i y‖ ≤ u i)
    (t : Finset ι) (σ : Finset { i : ι // i ∉ t })
    {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖(∑ i ∈ σ, f i.1 y) - ∑ i ∈ σ, f i.1 x‖ ≤
      (∑' i : { i : ι // i ∉ t }, u i) * ‖y - x‖ := by
  classical
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i =>
    (norm_nonneg (f' i x)).trans (hfu i x hx)
  have hu_tail : Summable fun i : { i : ι // i ∉ t } => u i.1 := hu.subtype _
  let C : ℝ := ∑' i : { i : ι // i ∉ t }, u i
  have hder : ∀ z ∈ s,
      HasFDerivWithinAt (fun w => ∑ i ∈ σ, f i.1 w)
        (∑ i ∈ σ, f' i.1 z) s z :=
    fun z hz => HasFDerivWithinAt.fun_sum fun i _ => hf i.1 z hz
  have hbd : ∀ z ∈ s, ‖∑ i ∈ σ, f' i.1 z‖ ≤ C := by
    intro z hz
    have h1 : ‖∑ i ∈ σ, f' i.1 z‖ ≤ ∑ i ∈ σ, ‖f' i.1 z‖ := norm_sum_le _ _
    have h2 : ∑ i ∈ σ, ‖f' i.1 z‖ ≤ ∑ i ∈ σ, u i.1 :=
      Finset.sum_le_sum fun i _ => hfu i.1 z hz
    have h3 : ∑ i ∈ σ, u i.1 ≤ C :=
      hu_tail.sum_le_tsum σ fun i _ => hu_nonneg i.1
    exact h1.trans (h2.trans h3)
  simpa [C] using
    hs.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbd hx hy

/-- Infinite remainder of the series is Lipschitz on `s` with constant the tail of `u`. -/
private lemma norm_tsum_compl_sub_le {s : Set E} (hs : Convex ℝ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u : ι → ℝ}
    (hf : ∀ i y, y ∈ s → HasFDerivWithinAt (f i) (f' i y) s y)
    (hu : Summable u) (hfu : ∀ i y, y ∈ s → ‖f' i y‖ ≤ u i)
    (hsum : ∀ z, z ∈ s → Summable fun i => f i z)
    (t : Finset ι) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖(∑' i : { i : ι // i ∉ t }, f i y) -
        ∑' i : { i : ι // i ∉ t }, f i x‖ ≤
      (∑' i : { i : ι // i ∉ t }, u i) * ‖y - x‖ := by
  classical
  have hy_sum : Summable fun i : { i : ι // i ∉ t } => f i.1 y := (hsum y hy).subtype _
  have hx_sum : Summable fun i : { i : ι // i ∉ t } => f i.1 x := (hsum x hx).subtype _
  have htend :
      Tendsto (fun σ : Finset { i : ι // i ∉ t } =>
          (∑ i ∈ σ, f i.1 y) - ∑ i ∈ σ, f i.1 x)
        atTop (𝓝 ((∑' i : { i : ι // i ∉ t }, f i.1 y) -
          ∑' i : { i : ι // i ∉ t }, f i.1 x)) := by
    have hsub :
        Tendsto (fun σ : Finset { i : ι // i ∉ t } =>
            ∑ i ∈ σ, (f i.1 y - f i.1 x))
          atTop (𝓝 ((∑' i : { i : ι // i ∉ t }, f i.1 y) -
            ∑' i : { i : ι // i ∉ t }, f i.1 x)) :=
      hy_sum.hasSum.sub hx_sum.hasSum
    have heq :
        (fun σ : Finset { i : ι // i ∉ t } =>
            (∑ i ∈ σ, f i.1 y) - ∑ i ∈ σ, f i.1 x) =
          fun σ => ∑ i ∈ σ, (f i.1 y - f i.1 x) := by
      funext σ
      rw [← Finset.sum_sub_distrib]
    rwa [heq]
  have hnorm :
      Tendsto (fun σ : Finset { i : ι // i ∉ t } =>
          ‖(∑ i ∈ σ, f i.1 y) - ∑ i ∈ σ, f i.1 x‖)
        atTop (𝓝 ‖(∑' i : { i : ι // i ∉ t }, f i.1 y) -
          ∑' i : { i : ι // i ∉ t }, f i.1 x‖) :=
    tendsto_norm.comp htend
  exact le_of_tendsto hnorm <| Eventually.of_forall fun σ =>
    norm_finset_compl_sub_le hs hf hu hfu t σ hx hy

/-- Termwise Fréchet derivative within a convex set, under a summable uniform
majorant of the derivatives. The summed derivative is the sum of the derivatives.
This is the closed-set replacement for `hasFDerivAt_tsum`. -/
lemma hasFDerivWithinAt_tsum {s : Set E} (hs : Convex ℝ s) {x : E} (hx : x ∈ s)
    {f : ι → E → F} {f' : ι → E → E →L[ℝ] F} {u : ι → ℝ}
    (hf : ∀ i y, y ∈ s → HasFDerivWithinAt (f i) (f' i y) s y)
    (hu : Summable u) (hfu : ∀ i y, y ∈ s → ‖f' i y‖ ≤ u i)
    (hsum : ∀ y, y ∈ s → Summable fun i => f i y) :
    HasFDerivWithinAt (fun y => ∑' i, f i y) (∑' i, f' i x) s x := by
  classical
  have hu_nonneg : ∀ i, 0 ≤ u i := fun i =>
    (norm_nonneg (f' i x)).trans (hfu i x hx)
  have hf'x : Summable fun i => f' i x :=
    Summable.of_norm_bounded hu fun i => hfu i x hx
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε εpos
  have htail := tendsto_tsum_compl_atTop_zero u
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨t, ht⟩ : ∃ t : Finset ι, ∑' i : { i : ι // i ∉ t }, u i < ε / 3 := by
    have := (tendsto_order.1 htail).2 _ hε3
    exact this.exists
  set C : ℝ := ∑' i : { i : ι // i ∉ t }, u i
  have hC : C < ε / 3 := ht
  have hC_nonneg : 0 ≤ C := tsum_nonneg fun i => hu_nonneg i.1
  have hfin : HasFDerivWithinAt (fun y => ∑ i ∈ t, f i y)
      (∑ i ∈ t, f' i x) s x :=
    HasFDerivWithinAt.fun_sum fun i _ => hf i x hx
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff] at hfin
  have hfinε := hfin hε3
  have hx_mem : ∀ᶠ y in 𝓝[s] x, y ∈ s := self_mem_nhdsWithin
  filter_upwards [hfinε, hx_mem] with y hfin_y hy
  have hsum_split :
      (∑' i, f i y) - ∑' i, f i x - (∑' i, f' i x) (y - x) =
        ((∑ i ∈ t, f i y) - ∑ i ∈ t, f i x - (∑ i ∈ t, f' i x) (y - x)) +
          ((∑' i : { i : ι // i ∉ t }, f i y) -
            ∑' i : { i : ι // i ∉ t }, f i x -
              (∑' i : { i : ι // i ∉ t }, f' i x) (y - x)) := by
    have hy_eq :
        ∑' i, f i y = ∑ i ∈ t, f i y + ∑' i : { i : ι // i ∉ t }, f i y :=
      ((hsum y hy).sum_add_tsum_subtype_compl t).symm
    have hx_eq :
        ∑' i, f i x = ∑ i ∈ t, f i x + ∑' i : { i : ι // i ∉ t }, f i x :=
      ((hsum x hx).sum_add_tsum_subtype_compl t).symm
    have hf'_eq :
        ∑' i, f' i x =
          ∑ i ∈ t, f' i x + ∑' i : { i : ι // i ∉ t }, f' i x :=
      (hf'x.sum_add_tsum_subtype_compl t).symm
    rw [hy_eq, hx_eq, hf'_eq, add_apply]
    abel
  have hrem :
      ‖(∑' i : { i : ι // i ∉ t }, f i y) -
          ∑' i : { i : ι // i ∉ t }, f i x‖ ≤ C * ‖y - x‖ :=
    norm_tsum_compl_sub_le hs hf hu hfu hsum t hx hy
  have hψ : ‖(∑' i : { i : ι // i ∉ t }, f' i x) (y - x)‖ ≤ C * ‖y - x‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    have hu_tail : Summable fun i : { i : ι // i ∉ t } => u i.1 := hu.subtype _
    have hn :
        ‖∑' i : { i : ι // i ∉ t }, f' i x‖ ≤ C :=
      tsum_of_norm_bounded hu_tail.hasSum fun i => hfu i.1 x hx
    exact mul_le_mul_of_nonneg_right hn (norm_nonneg _)
  have hremψ :
      ‖(∑' i : { i : ι // i ∉ t }, f i y) -
          ∑' i : { i : ι // i ∉ t }, f i x -
            (∑' i : { i : ι // i ∉ t }, f' i x) (y - x)‖ ≤
        2 * C * ‖y - x‖ := by
    refine (norm_sub_le _ _).trans ?_
    have := add_le_add hrem hψ
    linarith
  have : ‖(∑' i, f i y) - ∑' i, f i x - (∑' i, f' i x) (y - x)‖ ≤
      (ε / 3 + 2 * C) * ‖y - x‖ := by
    rw [hsum_split]
    refine (norm_add_le _ _).trans ?_
    have := add_le_add hfin_y hremψ
    linarith
  refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  linarith

/-! ## Summation of Taylor fields -/

/-- The summed Taylor field of a series of `C^∞` fields on a convex set, under a
summable uniform majorant of every order.

Hypotheses (minimal for the conclusion):
* `Convex ℝ s`, so the mean-value inequality applies along segments in `s`;
* each term has a Taylor field of class `∞` *within* `s`;
* for every order `m`, a summable numerical majorant of `‖p i x m‖` uniform for
  `x ∈ s`;
* `CompleteSpace F`, so the coefficient spaces `E [×m]→L[ℝ] F` are complete and
  the series of fields converge.

Not assumed: openness of `s`, a global `ContDiff` extension, uniqueness of
derivatives, or the desired summed Taylor identity. Unique differentiability on
`s` follows from convexity plus nonempty interior when needed to identify the
field with `iteratedFDerivWithin`, and is recorded as a corollary. -/
theorem hasFTaylorSeriesUpToOn_tsum {s : Set E} (hs : Convex ℝ s)
    {f : ι → E → F} {p : ι → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ i, HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) (f i) (p i) s)
    {u : ℕ → ι → ℝ} (hu : ∀ m, Summable (u m))
    (hbound : ∀ m i x, x ∈ s → ‖p i x m‖ ≤ u m i) :
    HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) (fun x => ∑' i, f i x)
      (fun x m => ∑' i, p i x m) s := by
  refine (hasFTaylorSeriesUpToOn_top_iff' (N := ∞) le_rfl).2 ⟨?zero, ?fderiv⟩
  · intro x hx
    exact tsum_curry0_of_hasFTaylorSeriesUpToOn hp hx
  · intro m x hx
    have hterm : ∀ i y, y ∈ s →
        HasFDerivWithinAt (p i · m) (p i y m.succ).curryLeft s y :=
      fun i y hy =>
        (hp i).fderivWithin m
          (WithTop.coe_lt_coe.2 (WithTop.coe_lt_top m)) y hy
    have hsum : ∀ y, y ∈ s → Summable fun i => p i y m :=
      fun y hy => summable_taylorCoeff p (hu m) (fun i => hbound m i y hy)
    have hfu : ∀ i y, y ∈ s → ‖(p i y m.succ).curryLeft‖ ≤ u m.succ i := by
      intro i y hy
      simpa [ContinuousMultilinearMap.curryLeft_norm] using hbound m.succ i y hy
    have hdiff :=
      hasFDerivWithinAt_tsum hs hx hterm (hu m.succ) hfu hsum
    refine hdiff.congr_fderiv ?_
    exact (tsum_curryLeft_taylorCoeff (fun i => p i x) (m := m)).symm

/-- On a uniquely differentiable set the summed field is the iterated within
derivative of the summed function. Unique differentiability is not needed to
*construct* the field, only to identify it with `iteratedFDerivWithin`. -/
theorem iteratedFDerivWithin_tsum {s : Set E} (hs : Convex ℝ s)
    (huniq : UniqueDiffOn ℝ s)
    {f : ι → E → F} {p : ι → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ i, HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) (f i) (p i) s)
    {u : ℕ → ι → ℝ} (hu : ∀ m, Summable (u m))
    (hbound : ∀ m i x, x ∈ s → ‖p i x m‖ ≤ u m i)
    {x : E} (hx : x ∈ s) (m : ℕ) :
    iteratedFDerivWithin ℝ m (fun y => ∑' i, f i y) s x = ∑' i, p i x m :=
  ((hasFTaylorSeriesUpToOn_tsum hs hp hu hbound).eq_iteratedFDerivWithin_of_uniqueDiffOn
      (m := m) (le_of_lt (WithTop.coe_lt_coe.2 (WithTop.coe_lt_top m))) huniq hx).symm

/-- Convex sets with nonempty interior are uniquely differentiable, so the
identification corollary applies to a closed lower half-ball. -/
theorem iteratedFDerivWithin_tsum_of_interior {s : Set E} (hs : Convex ℝ s)
    (hint : (interior s).Nonempty)
    {f : ι → E → F} {p : ι → E → FormalMultilinearSeries ℝ E F}
    (hp : ∀ i, HasFTaylorSeriesUpToOn (∞ : ℕ∞ω) (f i) (p i) s)
    {u : ℕ → ι → ℝ} (hu : ∀ m, Summable (u m))
    (hbound : ∀ m i x, x ∈ s → ‖p i x m‖ ≤ u m i)
    {x : E} (hx : x ∈ s) (m : ℕ) :
    iteratedFDerivWithin ℝ m (fun y => ∑' i, f i y) s x = ∑' i, p i x m :=
  iteratedFDerivWithin_tsum hs (uniqueDiffOn_convex hs hint) hp hu hbound hx m

/-- Equality of term fields on a subset (e.g. the equatorial seam) is inherited
by the summed field. No extra identification is performed. -/
lemma tsum_taylorCoeff_eqOn {t : Set E} {m : ℕ}
    {p q : ι → E → FormalMultilinearSeries ℝ E F}
    (h : ∀ i, EqOn (p i · m) (q i · m) t) :
    EqOn (fun x => ∑' i, p i x m) (fun x => ∑' i, q i x m) t :=
  fun _ hx => tsum_congr fun i => h i hx

end LeeSmooth.WithinTaylorSums
