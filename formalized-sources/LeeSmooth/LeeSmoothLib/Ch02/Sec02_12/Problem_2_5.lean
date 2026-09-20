import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Instances.Real
import LeeSmoothLib.Ch01.Sec01_04.Example_1_23
-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

-- Lee's alternate smooth real line from Example 1.23 is `CubicRealLine`.

/-- Helper for Problem 2-5: the alternate real line is presented in this file by the cubic
embedding into the standard real line. -/
def cubic_real_line_embedding : CubicRealLine → ℝ :=
  cubicMap

/-- Helper for Problem 2-5: a smooth real-valued function on the standard line, viewed as a map
into the alternate smooth real line. -/
def std_to_cubic (f : ℝ → ℝ) : ℝ → CubicRealLine :=
  f

/-- Helper for Problem 2-5: a real-valued function on the alternate smooth real line, viewed as an
ordinary function on `ℝ`. -/
def cubic_to_std (f : ℝ → ℝ) : CubicRealLine → ℝ :=
  f

/-- Helper for Problem 2-5: the inverse cubic chart, viewed as a map from the standard line to the
alternate smooth real line. -/
noncomputable def cubic_chart_symm_to_cubic : ℝ → CubicRealLine :=
  cubicChart.symm

/-- Helper for Problem 2-5: the defining cubic embedding of the alternate real line is an open
embedding. -/
lemma cubic_real_line_embedding_isOpenEmbedding :
    Topology.IsOpenEmbedding cubic_real_line_embedding :=
  show Topology.IsOpenEmbedding cubicMap from cubicMap_isOpenEmbedding

/-- Helper for Problem 2-5: the alternate real line is nonempty. -/
local instance cubicRealLineNonempty : Nonempty CubicRealLine :=
  ⟨show CubicRealLine from (0 : ℝ)⟩

/-- Helper for Problem 2-5: inside this file, use the singleton cubic chart as the charted-space
structure on the alternate real line. -/
noncomputable local instance cubicRealLineChartedSpace : ChartedSpace ℝ CubicRealLine :=
  cubic_real_line_embedding_isOpenEmbedding.singletonChartedSpace

/-- Helper for Problem 2-5: the local singleton cubic chart defines a smooth manifold structure on
the alternate real line. -/
noncomputable local instance cubicRealLineIsManifold : IsManifold (𝓘(ℝ)) ∞ CubicRealLine :=
  cubic_real_line_embedding_isOpenEmbedding.isManifold_singleton (I := 𝓘(ℝ)) (n := ∞)

/-- Helper for Problem 2-5: the inverse cubic chart is a left inverse to the cubic map. -/
lemma cubicChart_symm_cubicMap_eq (x : ℝ) : cubicChart.symm (cubicMap x) = x := by
  -- Injectivity of the cubic map identifies the unique preimage of `x ^ 3`.
  apply cubicMap_isOpenEmbedding.injective
  simpa [cubicMap] using cubicChart_symm_cube_eq (cubicMap x)

/-- Problem 2-5 (1): every function `f : ℝ → ℝ` that is smooth in the usual sense is also smooth
as a map from the standard smooth real line to Lee's alternate smooth structure `\widetilde{ℝ}`
from Example 1.23. -/
theorem contMDiff_std_to_cubic_of_contDiff {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (std_to_cubic f) := by
  -- Compose `f` with the defining cubic embedding to reach the Euclidean model space.
  have hcomp : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞
      (cubic_real_line_embedding ∘ std_to_cubic f) := by
    -- The composite is the cubic polynomial applied to `f`, hence ordinarily smooth.
    rw [contMDiff_iff_contDiff]
    simpa [cubic_real_line_embedding, std_to_cubic, cubicMap, Function.comp] using!
      ((contDiff_id.pow (3 : ℕ)).comp hf)
  -- The open-embedding API lifts Euclidean smoothness back to manifold smoothness.
  exact ContMDiff.of_comp_isOpenEmbedding
    (h' := cubic_real_line_embedding_isOpenEmbedding) hcomp

/-- Helper for Problem 2-5: if every block of an ordered finpartition has size `3`, then the
ambient order is divisible by `3`. -/
lemma OrderedFinpartition.three_dvd_of_all_partSize_eq_three {n : ℕ} (c : OrderedFinpartition n)
    (hpart : ∀ j : Fin c.length, c.partSize j = 3) : 3 ∣ n := by
  -- Count the sigma-type parametrizing the blocks to recover the total order `n`.
  have hcard : ∑ j : Fin c.length, c.partSize j = n := by
    simpa only [Fintype.card_fin, Fintype.card_sigma] using Fintype.card_congr c.equivSigma
  refine ⟨c.length, ?_⟩
  calc
    n = ∑ j : Fin c.length, c.partSize j := by simpa using hcard.symm
    _ = ∑ _j : Fin c.length, 3 := by simp [hpart]
    _ = c.length * 3 := by simp
    _ = 3 * c.length := by ring

/-- Helper for Problem 2-5: after composing a smooth function with the cubic chart, every
iterated derivative at `0` of order not divisible by `3` vanishes. -/
lemma iteratedDeriv_comp_cubic_eq_zero_of_not_three_dvd {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n (g ∘ cubicMap) 0 = 0 := by
  intro n hn
  have hcubic : ContDiffAt ℝ ∞ cubicMap 0 := by
    -- The cubic map is an ordinary smooth polynomial map.
    simpa [cubicMap] using!
      ((contDiff_id.pow (3 : ℕ)) : ContDiff ℝ ∞ (fun x : ℝ ↦ x ^ (3 : ℕ))).contDiffAt
  have hnle : (n : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    exact_mod_cast (show (n : ℕ∞) ≤ (⊤ : ℕ∞) by exact le_top)
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition (x := 0) (i := n) hg.contDiffAt hcubic hnle]
  classical
  refine Finset.sum_eq_zero ?_
  intro c hc
  by_cases hprod : ∏ j, iteratedDeriv (c.partSize j) cubicMap 0 = 0
  · -- If the product of cubic derivatives vanishes, the whole Faà di Bruno term vanishes.
    simp [hprod]
  · -- Otherwise each block contributes a nonzero derivative, forcing all block sizes to be `3`.
    have hpart : ∀ j : Fin c.length, c.partSize j = 3 := by
      intro j
      have hfactor :
          iteratedDeriv (c.partSize j) cubicMap 0 ≠ 0 := by
        exact Finset.prod_ne_zero_iff.mp hprod j (Finset.mem_univ j)
      have hpow :
          iteratedDeriv (c.partSize j) cubicMap 0 =
            (if c.partSize j = 3 then ((3 : ℕ).factorial : ℝ) else 0) := by
        calc
          iteratedDeriv (c.partSize j) cubicMap 0
              = iteratedDeriv (c.partSize j) (fun x : ℝ ↦ x ^ (3 : ℕ)) 0 := by
                  rfl
          _ = (if c.partSize j = 3 then ((3 : ℕ).factorial : ℝ) else 0) := by
                simpa using
                  (iteratedDeriv_fun_pow_zero (𝕜 := ℝ) (n := c.partSize j) (m := 3))
      by_contra hj
      have hzero : iteratedDeriv (c.partSize j) cubicMap 0 = 0 := by
        rw [hpow, if_neg hj]
      exact hfactor hzero
    have hdiv : 3 ∣ n := c.three_dvd_of_all_partSize_eq_three hpart
    exact (hn hdiv).elim

/-- Helper for Problem 2-5: away from the origin, the inverse cubic chart is ordinarily smooth. -/
lemma contDiffAt_cubicChart_symm_of_ne_zero {y : ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ ∞ cubicChart.symm y := by
  -- The inverse function theorem applies because the derivative of `x ↦ x ^ 3` is nonzero away
  -- from the singular point.
  have hsymm_ne_zero : cubicChart.symm y ≠ 0 := by
    intro hzero
    apply hy
    simpa [hzero] using (cubicChart_symm_cube_eq y).symm
  have hderiv_ne_zero : (3 : ℝ) * cubicChart.symm y ^ (2 : ℕ) ≠ 0 := by
    refine mul_ne_zero (by norm_num) ?_
    exact pow_ne_zero 2 hsymm_ne_zero
  have hy_mem : y ∈ cubicChart.target := by
    rw [cubicChart_target_eq_univ]
    exact Set.mem_univ y
  have hderiv :
      HasDerivAt cubicChart ((3 : ℝ) * cubicChart.symm y ^ (2 : ℕ)) (cubicChart.symm y) := by
    -- The cubic chart has the same derivative as the polynomial `x ↦ x ^ 3`.
    simpa [cubicChart, cubicMap] using! hasDerivAt_pow 3 (cubicChart.symm y)
  have hcubic : ContDiffAt ℝ ∞ cubicChart (cubicChart.symm y) := by
    -- Ordinary polynomial smoothness controls the chart itself.
    simpa [cubicChart, cubicMap] using!
      ((contDiff_id.pow (3 : ℕ)) : ContDiff ℝ ∞ cubicChart).contDiffAt
  exact cubicChart.contDiffAt_symm_deriv hderiv_ne_zero hy_mem hderiv hcubic

/-- Helper for Problem 2-5: away from the origin, precomposing a smooth function with the inverse
cubic chart remains ordinarily smooth. -/
lemma contDiffAt_comp_cubicChart_symm_of_ne_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) {y : ℝ}
    (hy : y ≠ 0) : ContDiffAt ℝ ∞ (f ∘ cubicChart.symm) y := by
  -- Off the singular point, the cube-root chart is smooth, so ordinary composition applies.
  exact ContDiffAt.comp y hf.contDiffAt (contDiffAt_cubicChart_symm_of_ne_zero hy)

/-- Helper for Problem 2-5: the three reciprocal factors added between degrees `3m` and
`3(m+1)` combine with `((3m)!)⁻¹` to give `((3(m+1))!)⁻¹`. -/
lemma cubic_taylor_inverse_factorial_step (m : ℕ) :
    (((3 * m).factorial : ℝ)⁻¹) *
        ((((3 * m + 1 : ℕ) : ℝ)⁻¹) *
          ((((3 * m + 2 : ℕ) : ℝ)⁻¹) * (((3 * m + 3 : ℕ) : ℝ)⁻¹))) =
      (((3 * (m + 1)).factorial : ℝ)⁻¹) := by
  -- Expand `((3 * (m + 1))!)` three times so the denominator matches the three new reciprocal
  -- factors inserted between `3m` and `3(m + 1)`.
  have hfactorial :
      (((3 * (m + 1)).factorial : ℝ)) =
        (((3 * m).factorial : ℝ) * (((3 * m + 1 : ℕ) : ℝ) *
          (((3 * m + 2 : ℕ) : ℝ) * (((3 * m + 3 : ℕ) : ℝ))))) := by
    calc
      (((3 * (m + 1)).factorial : ℝ))
          = (((3 * m + 3).factorial : ℕ) : ℝ) := by
              congr 1
      _ = (((3 * m + 3 : ℕ) : ℝ) * (((3 * m + 2).factorial : ℕ) : ℝ)) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
      _ = (((3 * m + 3 : ℕ) : ℝ) * (((3 * m + 2 : ℕ) : ℝ) *
            (((3 * m + 1).factorial : ℕ) : ℝ))) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
      _ = (((3 * m + 3 : ℕ) : ℝ) * ((((3 * m + 2 : ℕ) : ℝ) *
            (((3 * m + 1 : ℕ) : ℝ) * (((3 * m).factorial : ℕ) : ℝ))))) := by
            rw [Nat.factorial_succ, Nat.cast_mul]
      _ = (((3 * m).factorial : ℝ) * (((3 * m + 1 : ℕ) : ℝ) *
            (((3 * m + 2 : ℕ) : ℝ) * (((3 * m + 3 : ℕ) : ℝ))))) := by
            ring_nf
  -- Inverting the explicit factorial factorization produces exactly the reciprocal chain on the
  -- left-hand side.
  simpa [mul_inv_rev, mul_assoc, mul_left_comm, mul_comm] using
    (congrArg Inv.inv hfactorial).symm

/-- Helper for Problem 2-5: Taylor polynomials at `0` compress to the terms whose degrees are
multiples of `3` when all other iterated derivatives vanish at `0`. -/
lemma taylorWithinEval_eq_cubic_polynomial_of_vanishing {f : ℝ → ℝ}
    (hvanish : ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n f 0 = 0) :
    ∀ m : ℕ, ∀ x : ℝ,
      taylorWithinEval f (3 * m) Set.univ 0 x =
        Finset.sum (Finset.range (m + 1)) fun j =>
          (iteratedDeriv (3 * j) f 0 / ((3 * j).factorial : ℝ)) * x ^ (3 * j) := by
  intro m
  induction m with
  | zero =>
      intro x
      simp
  | succ m ih =>
      intro x
      have hnot_one : ¬ 3 ∣ 3 * m + 1 := by omega
      have hnot_two : ¬ 3 ∣ 3 * m + 2 := by omega
      rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega, taylorWithinEval_succ]
      rw [show 3 * m + 2 = (3 * m + 1) + 1 by omega, taylorWithinEval_succ]
      rw [show 3 * m + 1 = 3 * m + 1 by rfl, taylorWithinEval_succ]
      simp only [iteratedDerivWithin_univ, sub_zero, hvanish _ hnot_one,
        hvanish _ hnot_two, smul_eq_mul, mul_zero, add_zero, ih x, Finset.sum_range_succ]
      have hfac :
          ((((3 * m + 1 + 1 + 1).factorial : ℕ) : ℝ)) =
            (((3 * m + 1 + 1 : ℕ) : ℝ) + 1) *
              (((3 * m + 1 + 1).factorial : ℕ) : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [← hfac]
      rw [show 3 * m + 1 + 1 + 1 = 3 * (m + 1) by omega]
      ring

/-- Helper for Problem 2-5: substituting the inverse cubic chart turns a polynomial in powers
`(cubicChart.symm y)^(3j)` into the corresponding ordinary polynomial in `y`. -/
lemma cubic_polynomial_comp_cubicChart_symm (a : ℕ → ℝ) :
    ∀ m : ℕ, ∀ y : ℝ,
      Finset.sum (Finset.range (m + 1)) (fun j => a j * (cubicChart.symm y) ^ (3 * j)) =
        Finset.sum (Finset.range (m + 1)) fun j => a j * y ^ j := by
  intro m y
  -- Rewrite each monomial through `(cubicChart.symm y)^3 = y`.
  refine Finset.sum_congr rfl ?_
  intro j hj
  rw [pow_mul, cubicChart_symm_cube_eq]

/-! The following private lemmas are a one-variable smooth-division argument.  They keep the
Taylor remainder quotient explicit, so no analyticity assumption is introduced. -/

private noncomputable def smoothTaylorQuotient : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => Function.update
      (fun x => (f x - taylorWithinEval f n Set.univ 0 x) / x ^ (n + 1)) 0
      (iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ))

private lemma smoothTaylorQuotient_factor (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    f x = taylorWithinEval f n Set.univ 0 x +
      x ^ (n + 1) * smoothTaylorQuotient (n + 1) f x := by
  by_cases hx : x = 0
  · subst x
    simp [smoothTaylorQuotient]
  · simp [smoothTaylorQuotient, hx]
    field_simp
    ring

private lemma continuous_smoothTaylorQuotient (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) : Continuous (smoothTaylorQuotient n f) := by
  rcases n with _ | n
  · simpa [smoothTaylorQuotient] using hf.continuous
  · rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x = 0
    · subst x
      rw [smoothTaylorQuotient, continuousAt_update_same]
      have hnle : (n + 1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
        exact_mod_cast (show (n + 1 : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
      have ht : Filter.Tendsto
          (fun x => (f x - taylorWithinEval f (n + 1) Set.univ 0 x) / x ^ (n + 1))
          (nhds 0) (nhds 0) := by
        simpa using Real.taylor_tendsto (n := n + 1) convex_univ (Set.mem_univ 0)
          (hf.of_le hnle).contDiffOn
      have hc : Filter.Tendsto
          (fun _x : ℝ => iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ))
          (nhdsWithin 0 {0}ᶜ)
          (nhds (iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ))) :=
        tendsto_const_nhds
      have hsum : Filter.Tendsto
          (fun x => (f x - taylorWithinEval f (n + 1) Set.univ 0 x) / x ^ (n + 1) +
            iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ))
          (nhdsWithin 0 {0}ᶜ)
          (nhds (iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ))) := by
        simpa only [zero_add] using (ht.mono_left nhdsWithin_le_nhds).add hc
      refine hsum.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      rw [taylorWithinEval_succ]
      simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
      field_simp
      rw [Nat.factorial_succ]
      push_cast
      ring
    · rw [smoothTaylorQuotient, continuousAt_update_of_ne hx]
      have hp : ContinuousAt (taylorWithinEval f n Set.univ 0) x := by
        rcases n with _ | n
        · rw [show taylorWithinEval f 0 Set.univ 0 = (fun _x : ℝ => f 0) by
              funext y
              exact taylor_within_zero_eval f Set.univ 0 y]
          exact continuousAt_const
        · exact (hasDerivAt_taylorWithinEval_succ f n).continuousAt
      exact (hf.continuous.continuousAt.sub hp).div
        (continuousAt_id.pow _) (pow_ne_zero _ hx)

private lemma smoothTaylorQuotient_step (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    smoothTaylorQuotient (n + 1) f x =
      iteratedDeriv (n + 1) f 0 / ((n + 1).factorial : ℝ) +
        x * smoothTaylorQuotient (n + 2) f x := by
  by_cases hx : x = 0
  · subst x
    simp [smoothTaylorQuotient]
  · simp only [smoothTaylorQuotient, Function.update_of_ne hx]
    rw [taylorWithinEval_succ]
    simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
    field_simp
    rw [Nat.factorial_succ]
    push_cast
    ring

private lemma hasDerivAt_smoothTaylorQuotient_zero (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    HasDerivAt (smoothTaylorQuotient (n + 1) f)
      (iteratedDeriv (n + 2) f 0 / ((n + 2).factorial : ℝ)) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hcont : Filter.Tendsto (smoothTaylorQuotient (n + 2) f) (nhds 0)
      (nhds (iteratedDeriv (n + 2) f 0 / ((n + 2).factorial : ℝ))) := by
    convert (continuous_smoothTaylorQuotient (n + 2) hf).continuousAt.tendsto using 1
    simp [smoothTaylorQuotient, Nat.add_assoc]
  refine (hcont.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  rw [slope]
  rw [smoothTaylorQuotient_step n f x]
  simp only [smoothTaylorQuotient, Function.update_self]
  simp [hx, vsub_eq_sub, smul_eq_mul]

private lemma hasDerivAt_smoothTaylorQuotient (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : ℝ) :
    HasDerivAt (smoothTaylorQuotient n f)
      (smoothTaylorQuotient n (deriv f) x -
        (n : ℝ) * smoothTaylorQuotient (n + 1) f x) x := by
  rcases n with _ | n
  · simpa [smoothTaylorQuotient] using
      (hf.differentiable (by simp)).differentiableAt.hasDerivAt
  · by_cases hx : x = 0
    · subst x
      refine (hasDerivAt_smoothTaylorQuotient_zero n hf).congr_deriv ?_
      simp only [smoothTaylorQuotient, Function.update_self]
      rw [← iteratedDeriv_succ']
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring
    · have heq : smoothTaylorQuotient (n + 1) f =ᶠ[nhds x]
          (fun y => (f y - taylorWithinEval f n Set.univ 0 y) / y ^ (n + 1)) := by
        filter_upwards [eventually_ne_nhds hx] with y hy
        simp [smoothTaylorQuotient, hy]
      have hfd : HasDerivAt f (deriv f x) x :=
        (hf.differentiable (by simp)).differentiableAt.hasDerivAt
      have hpow : HasDerivAt (fun y : ℝ => y ^ (n + 1))
          ((n + 1 : ℕ) * x ^ n) x := by
        simpa using hasDerivAt_pow (n + 1) x
      rcases n with _ | n
      · have ht : HasDerivAt (taylorWithinEval f 0 Set.univ 0) 0 x := by
          rw [show taylorWithinEval f 0 Set.univ 0 = (fun _y : ℝ => f 0) by
            funext y
            exact taylor_within_zero_eval f Set.univ 0 y]
          exact hasDerivAt_const x (f 0)
        refine (((hfd.sub ht).div hpow (pow_ne_zero _ hx)).congr_of_eventuallyEq heq).congr_deriv ?_
        simp only [smoothTaylorQuotient, Function.update_of_ne hx]
        rw [taylorWithinEval_succ]
        simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
        simp only [taylor_within_zero_eval]
        simp only [Pi.sub_apply]
        field_simp
        rw [taylor_within_zero_eval]
        rw [iteratedDeriv_one]
        ring
      · have ht : HasDerivAt (taylorWithinEval f (n + 1) Set.univ 0)
            (taylorWithinEval (deriv f) n Set.univ 0 x) x := by
          have h := hasDerivAt_taylorWithinEval_succ
            (s := Set.univ) (x₀ := 0) (x := x) f n
          rw [derivWithin_univ] at h
          exact h
        refine (((hfd.sub ht).div hpow (pow_ne_zero _ hx)).congr_of_eventuallyEq heq).congr_deriv ?_
        simp only [smoothTaylorQuotient, Function.update_of_ne hx]
        rw [taylorWithinEval_succ (deriv f) n, taylorWithinEval_succ f (n + 1)]
        simp only [iteratedDerivWithin_univ, sub_zero, smul_eq_mul, ← iteratedDeriv_succ']
        simp only [Pi.sub_apply]
        field_simp
        rw [Nat.factorial_succ]
        push_cast
        ring

private lemma contDiff_smoothTaylorQuotient (n : ℕ) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (smoothTaylorQuotient n f) := by
  rw [contDiff_infty]
  intro k
  induction k generalizing n f with
  | zero =>
      change ContDiff ℝ (0 : ℕ∞ω) (smoothTaylorQuotient n f)
      rw [contDiff_zero]
      exact continuous_smoothTaylorQuotient n hf
  | succ k ih =>
      change ContDiff ℝ ((k : ℕ∞ω) + 1) (smoothTaylorQuotient n f)
      rw [contDiff_succ_iff_deriv]
      have hdiff : Differentiable ℝ (smoothTaylorQuotient n f) := fun x =>
        (hasDerivAt_smoothTaylorQuotient n hf x).differentiableAt
      refine ⟨hdiff, by simp, ?_⟩
      have hderiv : deriv (smoothTaylorQuotient n f) = fun x =>
          smoothTaylorQuotient n (deriv f) x -
            (n : ℝ) * smoothTaylorQuotient (n + 1) f x := by
        funext x
        exact (hasDerivAt_smoothTaylorQuotient n hf x).deriv
      rw [hderiv]
      exact (ih n (contDiff_infty_iff_deriv.mp hf).2).sub
        (contDiff_const.mul (ih (n + 1) hf))

private noncomputable def cubicRootRemainder (m : ℕ) (q : ℝ → ℝ) (y : ℝ) : ℝ :=
  y ^ (m + 1) * q (cubicChart.symm y)

private noncomputable def cubicRootRemainderDeriv (m : ℕ) (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  (m + 1 : ℕ) * q x + (x / 3) * deriv q x

private lemma contDiff_cubicRootRemainderDeriv (m : ℕ) {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ ∞ (cubicRootRemainderDeriv m q) := by
  unfold cubicRootRemainderDeriv
  fun_prop

private lemma hasDerivAt_cubicRootRemainder_succ (m : ℕ) {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (y : ℝ) :
    HasDerivAt (cubicRootRemainder (m + 1) q)
      (cubicRootRemainder m (cubicRootRemainderDeriv (m + 1) q) y) y := by
  by_cases hy : y = 0
  · subst y
    rw [hasDerivAt_iff_tendsto_slope]
    have hzero_mem : (0 : ℝ) ∈ cubicChart.target := by
      rw [cubicChart_target_eq_univ]
      exact Set.mem_univ 0
    have hroot : Filter.Tendsto cubicChart.symm (nhds 0) (nhds 0) := by
      have h := cubicChart.symm.continuousAt hzero_mem
      change Filter.Tendsto cubicChart.symm (nhds 0) (nhds (cubicChart.symm 0)) at h
      simpa only [cubicChart_symm_zero] using h
    have hqroot : Filter.Tendsto (fun z => q (cubicChart.symm z)) (nhds 0) (nhds (q 0)) :=
      hq.continuous.continuousAt.tendsto.comp hroot
    have ht : Filter.Tendsto (fun z : ℝ => z ^ (m + 1) * q (cubicChart.symm z))
        (nhds 0) (nhds 0) := by
      convert (continuousAt_id.pow (m + 1)).tendsto.mul hqroot using 1 <;> simp
    suffices Filter.Tendsto (slope (cubicRootRemainder (m + 1) q) 0)
        (nhdsWithin 0 {0}ᶜ) (nhds 0) by
      simpa [cubicRootRemainder]
    refine (ht.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    simp [slope, cubicRootRemainder, cubicChart_symm_zero,
      vsub_eq_sub, smul_eq_mul]
    rw [pow_succ]
    field_simp
    rw [show m + 1 + 1 = m + 2 by omega, pow_add]
    ring
  · have hsymm_ne_zero : cubicChart.symm y ≠ 0 := by
      intro hzero
      apply hy
      simpa [hzero] using (cubicChart_symm_cube_eq y).symm
    have hy_mem : y ∈ cubicChart.target := by
      rw [cubicChart_target_eq_univ]
      exact Set.mem_univ y
    have hcubic : HasDerivAt cubicChart
        ((3 : ℝ) * cubicChart.symm y ^ (2 : ℕ)) (cubicChart.symm y) := by
      simpa [cubicChart, cubicMap] using! hasDerivAt_pow 3 (cubicChart.symm y)
    have hroot : HasDerivAt cubicChart.symm
        (((3 : ℝ) * cubicChart.symm y ^ (2 : ℕ))⁻¹) y :=
      cubicChart.hasDerivAt_symm hy_mem
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hsymm_ne_zero)) hcubic
    have hqroot : HasDerivAt (fun z => q (cubicChart.symm z))
        (deriv q (cubicChart.symm y) *
          (((3 : ℝ) * cubicChart.symm y ^ (2 : ℕ))⁻¹)) y := by
      exact (hq.differentiable (by simp)).differentiableAt.hasDerivAt.comp y hroot
    have hprod := (hasDerivAt_pow (m + 2) y).mul hqroot
    refine hprod.congr_deriv ?_
    simp only [cubicRootRemainder, cubicRootRemainderDeriv]
    rw [show m + 2 - 1 = m + 1 by omega]
    let x := cubicChart.symm y
    have hyx : y = x ^ 3 := by
      exact (cubicChart_symm_cube_eq y).symm
    change x ≠ 0 at hsymm_ne_zero
    rw [hyx]
    simp only [show x ^ 3 = cubicMap x by rfl, cubicChart_symm_cubicMap_eq]
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ]
    field_simp
    simp only [cubicMap]
    ring

private lemma contDiff_cubicRootRemainder (m : ℕ) {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) : ContDiff ℝ m (cubicRootRemainder m q) := by
  induction m generalizing q with
  | zero =>
      change ContDiff ℝ (0 : ℕ∞ω) (cubicRootRemainder 0 q)
      rw [contDiff_zero, continuous_iff_continuousAt]
      intro y
      have hy_mem : y ∈ cubicChart.target := by
        rw [cubicChart_target_eq_univ]
        exact Set.mem_univ y
      unfold cubicRootRemainder
      simp only [zero_add, pow_one]
      exact continuousAt_id.mul
        (hq.continuous.continuousAt.comp (cubicChart.symm.continuousAt hy_mem))
  | succ m ih =>
      change ContDiff ℝ ((m : ℕ∞ω) + 1) (cubicRootRemainder (m + 1) q)
      rw [contDiff_succ_iff_deriv]
      have hdiff : Differentiable ℝ (cubicRootRemainder (m + 1) q) := fun y =>
        (hasDerivAt_cubicRootRemainder_succ m hq y).differentiableAt
      refine ⟨hdiff, by simp, ?_⟩
      have hderiv : deriv (cubicRootRemainder (m + 1) q) =
          cubicRootRemainder m (cubicRootRemainderDeriv (m + 1) q) := by
        funext y
        exact (hasDerivAt_cubicRootRemainder_succ m hq y).deriv
      rw [hderiv]
      exact ih (contDiff_cubicRootRemainderDeriv (m + 1) hq)

/-- Helper for Problem 2-5: vanishing of the non-`3`-divisible derivatives of `f` at `0`
forces the Euclidean representative in the cubic source chart to be smooth. -/
lemma contDiff_comp_cubic_chart_symm_of_vanishing {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hvanish : ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n f 0 = 0) :
    ContDiff ℝ ∞ (cubic_to_std f ∘ cubic_chart_symm_to_cubic) := by
  have hall : ContDiff ℝ ∞ (fun y => f (cubicChart.symm y)) := by
    rw [contDiff_infty]
    intro m
    let a : ℕ → ℝ := fun j =>
      iteratedDeriv (3 * j) f 0 / ((3 * j).factorial : ℝ)
    let q : ℝ → ℝ := fun x =>
      x * smoothTaylorQuotient (3 * (m + 1) + 1) f x
    have hq : ContDiff ℝ ∞ q := by
      dsimp only [q]
      exact contDiff_id.mul (contDiff_smoothTaylorQuotient _ hf)
    have hp : ContDiff ℝ ∞
        (fun y => Finset.sum (Finset.range (m + 2)) fun j => a j * y ^ j) := by
      fun_prop
    have heq : (fun y => f (cubicChart.symm y)) = fun y =>
        (Finset.sum (Finset.range (m + 2)) fun j => a j * y ^ j) +
          cubicRootRemainder m q y := by
      funext y
      calc
        f (cubicChart.symm y) =
            taylorWithinEval f (3 * (m + 1)) Set.univ 0 (cubicChart.symm y) +
              (cubicChart.symm y) ^ (3 * (m + 1) + 1) *
                smoothTaylorQuotient (3 * (m + 1) + 1) f (cubicChart.symm y) :=
          smoothTaylorQuotient_factor f (3 * (m + 1)) (cubicChart.symm y)
        _ = (Finset.sum (Finset.range (m + 2)) fun j =>
              a j * (cubicChart.symm y) ^ (3 * j)) +
              (cubicChart.symm y) ^ (3 * (m + 1) + 1) *
                smoothTaylorQuotient (3 * (m + 1) + 1) f (cubicChart.symm y) := by
          rw [taylorWithinEval_eq_cubic_polynomial_of_vanishing hvanish (m + 1)]
        _ = (Finset.sum (Finset.range (m + 2)) fun j => a j * y ^ j) +
              cubicRootRemainder m q y := by
          rw [cubic_polynomial_comp_cubicChart_symm a (m + 1) y]
          unfold cubicRootRemainder q
          rw [pow_add, pow_mul, cubicChart_symm_cube_eq]
          rw [show m + 1 + 1 = m + 2 by omega]
          simp only [pow_one]
          ring
    rw [heq]
    have hmle : (m : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
      exact_mod_cast (show (m : ℕ∞) ≤ (⊤ : ℕ∞) from le_top)
    exact (hp.of_le hmle).add (contDiff_cubicRootRemainder m hq)
  change ContDiff ℝ ∞ (f ∘ cubicChart.symm)
  simpa only [Function.comp_def] using hall

/-- Problem 2-5 (2): for a function `f : ℝ → ℝ` that is smooth in the usual sense, smoothness as a
map from Lee's alternate smooth real line `\widetilde{ℝ}` to the standard smooth real line is
equivalent to vanishing of every derivative at `0` whose order is not a multiple of `3`. -/
theorem contMDiff_cubic_to_std_iff_iteratedDeriv_eq_zero {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ (cubic_to_std f) ↔
      ∀ n : ℕ, ¬ 3 ∣ n → iteratedDeriv n f 0 = 0 := by
  -- Route correction: lock the cubic singleton atlas locally, then pass between manifold
  -- smoothness and ordinary smoothness by composing with the inverse cubic chart.
  constructor
  · intro hmdiff n hn
    have hsymm : ContMDiff 𝓘(ℝ) 𝓘(ℝ) ∞ cubic_chart_symm_to_cubic := by
      -- The inverse of the defining open embedding is manifold-smooth on its image, which is all
      -- of `ℝ` because the cubic map is surjective.
      rw [← contMDiffOn_univ, ← cubicMap_surjective.range_eq]
      simpa [cubic_real_line_embedding, cubic_chart_symm_to_cubic, cubicChart] using
        (contMDiffOn_isOpenEmbedding_symm (I := 𝓘(ℝ))
          (h := cubic_real_line_embedding_isOpenEmbedding) (n := ∞))
    have hg : ContDiff ℝ ∞ (cubic_to_std f ∘ cubic_chart_symm_to_cubic) := by
      -- Composing the manifold-smooth map with the manifold-smooth inverse chart gives an
      -- ordinary smooth function on `ℝ`.
      simpa [contMDiff_iff_contDiff] using hmdiff.comp hsymm
    have hrewrite : ((cubic_to_std f ∘ cubic_chart_symm_to_cubic) ∘ cubicMap) = f := by
      -- The cubic chart inverse cancels the cubic map pointwise.
      funext x
      simp [cubic_to_std, cubic_chart_symm_to_cubic, Function.comp, cubicChart_symm_cubicMap_eq]
    -- Apply the Faà di Bruno vanishing lemma to the Euclidean representative.
    simpa [hrewrite] using
      iteratedDeriv_comp_cubic_eq_zero_of_not_three_dvd hg n hn
  · intro hvanish
    have hg : ContDiff ℝ ∞ (cubic_to_std f ∘ cubic_chart_symm_to_cubic) :=
      contDiff_comp_cubic_chart_symm_of_vanishing hf hvanish
    intro x
    -- Translate the manifold-smoothness claim to the Euclidean representative in the source
    -- cubic chart, where `hg` applies directly.
    rw [contMDiffAt_iff_source_of_mem_source (I := 𝓘(ℝ)) (I' := 𝓘(ℝ))
      (x := x) (x' := x) (f := cubic_to_std f) (mem_chart_source _ x)]
    simpa [cubic_to_std, cubic_chart_symm_to_cubic, cubic_real_line_embedding, Function.comp,
      extChartAt_coe, extChartAt_coe_symm, extChartAt_model_space_eq_id,
      Topology.IsOpenEmbedding.singletonChartedSpace_chartAt_eq,
      contMDiffWithinAt_iff_contDiffWithinAt] using!
      (hg.contDiffAt.contDiffWithinAt : ContDiffWithinAt ℝ ∞
        (cubic_to_std f ∘ cubic_chart_symm_to_cubic) Set.univ (cubic_real_line_embedding x))
