import Mathlib
import LeeSmoothLib.External.SardMoreira.ContDiffMoreiraHolder
import LeeSmoothLib.External.SardMoreira.ImplicitFunction
import LeeSmoothLib.External.SardMoreira.LinearAlgebra
import LeeSmoothLib.External.SardMoreira.ChartEstimates
import LeeSmoothLib.External.SardMoreira.WithRPowDist
import LeeSmoothLib.External.SardMoreira.OuterMeasureDeriv
import LeeSmoothLib.External.SardMoreira.ToMathlib.PR33029
import LeeSmoothLib.External.SardMoreira.ToMathlib.PR32993

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true

open scoped unitInterval NNReal Topology ENNReal Pointwise
open MeasureTheory Measure Metric

local notation "dim" => Module.finrank ℝ

-- TODO: generalize to semilinear maps
protected noncomputable def ContinuousLinearMap.finrank {R M N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    (f : M →L[R] N) : ℕ :=
  Module.finrank R f.range

theorem ContinuousLinearMap.finrank_comp_eq_left_of_surjective {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid P] [Module R P] [TopologicalSpace P]
    (g : N →L[R] P) {f : M →L[R] N} (hf : Function.Surjective f) :
    (g ∘L f).finrank = g.finrank := by
  -- Since $f$ is surjective, the image of $g \circ f$ is the same as the image of $g$.
  have h_range : (g.comp f).range = g.range :=
    SetLike.coe_injective <| hf.range_comp g
  rw [ContinuousLinearMap.finrank, ContinuousLinearMap.finrank, h_range]

theorem ContinuousLinearMap.finrank_comp_eq_right_of_injective {R M N P : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid P] [Module R P] [TopologicalSpace P]
    {g : N →L[R] P} (hg : Function.Injective g) (f : M →L[R] N) :
    (g ∘L f).finrank = f.finrank := by
  -- Since $g$ is injective, the range of $g \circ f$ is isomorphic to the range of $f$.
  have h_iso : (g.comp f).range ≃ₗ[R] f.range := by
    symm;
    refine' { Equiv.ofBijective ( fun x => ⟨ g x, by aesop ⟩ ) ⟨ fun x y hxy => _, fun x => _ ⟩ with .. } <;> aesop;
  exact h_iso.finrank_eq

@[simp]
theorem ContinuousLinearEquiv.finrank_comp_left {R M N N' : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid N'] [Module R N'] [TopologicalSpace N']
    (e : N ≃L[R] N') (f : M →L[R] N) : (e ∘L f : M →L[R] N').finrank = f.finrank := by
  apply ContinuousLinearMap.finrank_comp_eq_right_of_injective
  exact e.injective

@[simp]
theorem ContinuousLinearEquiv.finrank_comp_right {R M M' N : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [TopologicalSpace M]
    [AddCommMonoid N] [Module R N] [TopologicalSpace N]
    [AddCommMonoid M'] [Module R M'] [TopologicalSpace M']
    (f : M →L[R] N) (e : M' ≃L[R] M) : (f ∘L e : M' →L[R] N).finrank = f.finrank := by
  apply ContinuousLinearMap.finrank_comp_eq_left_of_surjective
  exact e.surjective

theorem LipschitzWith.hausdorffMeasure_image_null {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] {K : NNReal} {f : X → Y}
    (h : LipschitzWith K f) {d : ℝ} (hd : 0 ≤ d) {s : Set X} (hs : μH[d] s = 0) :
    μH[d] (f '' s) = 0 := by
  grw [← nonpos_iff_eq_zero, h.hausdorffMeasure_image_le hd, hs, mul_zero]

/-- Moreira's upper estimate on the Hausdorff dimension of the image of the set of points $x$
such that `fderiv ℝ f x` has rank at most `p < min n m`,
provided that `f` is a $$C^{k+(\alpha)}$$-map
from an `n`-dimensional space to an `m`-dimensional space.

Note that the estimate does not depend on `m`. -/
noncomputable def sardMoreiraBound (n k : ℕ) (α : I) (p : ℕ) : ℝ≥0 :=
  p + (n - p) / (k + ⟨α, α.2.1⟩)

theorem mul_sardMoreiraBound {n k p : ℕ} (hk : k ≠ 0) (hpn : p ≤ n) (α : I) :
    (k + α : ℝ) * sardMoreiraBound n k α p = (k + α) * p + (n - p) := by
  rw [sardMoreiraBound]
  have := α.2.1
  simp [field, @NNReal.coe_sub n p (mod_cast hpn), NNReal.coe_mk]
  change ((k : ℝ) + α) *
      ((p : ℝ) * ((k : ℝ) + α) + ((n : ℝ) - p)) =
    ((k : ℝ) + α) * (((k : ℝ) + α) * p + ((n : ℝ) - p))
  ring

theorem monotone_sardMoreiraBound (n : ℕ) {k : ℕ} (hk : k ≠ 0) (α : I) :
    Monotone (sardMoreiraBound n k α) := by
  apply monotone_nat_of_le_succ
  intro p
  rcases α with ⟨α, hα₀, hα₁⟩
  simp only [sardMoreiraBound, field]
  rw [← NNReal.coe_le_coe]
  push_cast [tsub_add_eq_tsub_tsub]
  grw [@NNReal.coe_sub_def _ 1, ← le_max_left, ← sub_nonneg]
  push_cast
  linarith only [hα₀, show (1 : ℝ) ≤ k by norm_cast; grind]

@[gcongr]
theorem sardMoreiraBound_le_sardMoreiraBound {m n k l p q : ℕ} (hl : l ≠ 0) (hmn : m ≤ n)
    (hlk : l ≤ k) (hpq : p ≤ q) (α : I) :
    sardMoreiraBound m k α p ≤ sardMoreiraBound n l α q := by
  grw [← monotone_sardMoreiraBound n hl α hpq]
  unfold sardMoreiraBound
  gcongr

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {k p : ℕ} {α : I}

namespace Moreira2001

theorem hausdorffMeasure_image_le_mul_aux {X : Type*} [MetricSpace X]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace X] [BorelSpace X]
    {f : E × F → X} {s : Set (E × F)} {n : ℕ} (hk : k ≠ 0) (hn : dim E + dim F ≤ n)
    {cE cF : ℝ≥0}
    (hcE : ∀ x ∈ s, ∀ᶠ y in 𝓝 (x, x), y.1.2 = y.2.2 → dist (f y.1) (f y.2) ≤ cE * dist y.1 y.2)
    (hcF : ∀ x ∈ s, ∀ᶠ y in 𝓝 x.2, dist (f (x.1, y)) (f x) ≤ cF * dist y x.2 ^ (k + α : ℝ)) :
    μH[sardMoreiraBound n k α (dim E)] (f '' s) ≤
      ((2 * (cE + cF)) ^ (sardMoreiraBound n k α (dim E) : ℝ) /
        (μH[dim E] (ball (0 : E) 1) * μH[dim F] (ball (0 : F) 1))) *
        μH[dim E].prod μH[dim F] s := by
  set C : ℝ≥0∞ := (2 * (cE + cF)) ^ (sardMoreiraBound n k α (dim E) : ℝ) /
    (μH[dim E] (ball (0 : E) 1) * μH[dim F] (ball (0 : F) 1))
  have hα₀ : 0 ≤ (α : ℝ) := α.2.1
  set β : ℝ := (k + α)⁻¹
  have hβinv : β⁻¹ = k + α := inv_inv _
  have hβ₀ : 0 < β := by positivity
  have hβ₁ : β ≤ 1 := by
    suffices (1 : ℝ) ≤ k + α by simpa [field]
    rw [← Nat.one_le_iff_ne_zero] at hk
    rify at hk
    linear_combination hk + hα₀
  set e : WithRPowDist E β hβ₀ hβ₁ × F → E × F := Prod.map WithRPowDist.val id
  have hec : Continuous e := by fun_prop
  set t : Set (WithRPowDist E β hβ₀ hβ₁ × F) := e ⁻¹' s
  set g : WithRPowDist E β hβ₀ hβ₁ × F → X := f ∘ e
  set μ : Measure (WithRPowDist E β hβ₀ hβ₁ × F) :=
    (μH[dim E].withRPowDist β hβ₀ hβ₁).prod μH[dim F]
  have hμ (s) : μ s = μH[dim E].prod μH[dim F] (Prod.map .mk id ⁻¹' s) := by
    simp only [μ]
    rw [withRPowDist, ← Measure.map_id (μ := μH[dim F]),
        map_prod_map _ _ WithRPowDist.measurable_mk measurable_id, Measure.map_id]
    exact MeasurableEquiv.map_apply (WithRPowDist.measurableEquiv.symm.prodCongr (.refl F)) s
  suffices μH[sardMoreiraBound n k α (dim E)] (g '' t) ≤ C * μ t by
    have he_surj : Function.Surjective e :=
      WithRPowDist.surjective_val.prodMap Function.surjective_id
    have himage : e '' t = s := Set.image_preimage_eq s he_surj
    have hpre : Prod.map WithRPowDist.mk id ⁻¹' t = s := by
      ext z
      change e (WithRPowDist.mk z.1, z.2) ∈ s ↔ z ∈ s
      simp [e]
    calc
      μH[sardMoreiraBound n k α (dim E)] (f '' s)
          = μH[sardMoreiraBound n k α (dim E)] (f '' (e '' t)) := by rw [himage]
      _ = μH[sardMoreiraBound n k α (dim E)] ((f ∘ e) '' t) := by rw [Set.image_comp]
      _ = μH[sardMoreiraBound n k α (dim E)] (g '' t) := rfl
      _ ≤ C * μ t := this
      _ = C * μH[dim E].prod μH[dim F] (Prod.map WithRPowDist.mk id ⁻¹' t) := by rw [hμ t]
      _ = C * μH[dim E].prod μH[dim F] s := by rw [hpre]
  apply hasudorffMeasure_image_le_mul (holderExp := k + α) (dimDom := (k + α) * dim E + dim F)
  case holderExp_pos => positivity
  case hμ_dim =>
    intro x r
    rw [← closedBall_prod_same, hμ, Set.preimage_prod_map_prod,
      WithRPowDist.preimage_mk_closedBall, Set.preimage_id, Measure.prod_prod,
      addHaar_closedBall, addHaar_closedBall, mul_mul_mul_comm, hβinv, ← Real.rpow_mul_natCast,
      ENNReal.rpow_add_of_nonneg, ← ENNReal.coe_rpow_of_nonneg]
    · norm_cast
    all_goals positivity
  case hμball₀ =>
    apply_rules [mul_ne_zero, IsOpen.measure_ne_zero, isOpen_ball] <;> simp
  case hμball => finiteness
  case hdim =>
    grw [mul_sardMoreiraBound hk (by grind), ← hn]
    simp
  case hdimDom => positivity
  case hsC => right; finiteness
  case h =>
    intro x hx ε hε
    have hec : Continuous e := by fun_prop
    replace hcE := (hec.prodMap hec).tendsto (x, x) |>.eventually <| hcE (e x) hx
    specialize hcF (e x) hx
    rw [Metric.eventually_nhds_iff_ball] at hcE hcF
    rcases hcE with ⟨rE, hrE₀, hrE⟩
    rcases hcF with ⟨rF, hrF₀, hrF⟩
    rw [eventually_nhdsWithin_iff]
    filter_upwards [ball_mem_nhds _ (lt_min hrE₀ hrF₀)] with y hy hyt
    grw [← le_self_add]
    rw [edist_nndist, edist_nndist, ← ENNReal.coe_rpow_of_nonneg _ (by positivity)]
    norm_cast
    rw [← NNReal.coe_le_coe]
    push_cast
    calc
      dist (g y) (g x) ≤ dist (g y) (g (x.1, y.2)) + dist (g (x.1, y.2)) (g x) :=
        dist_triangle ..
      _ ≤ cE * dist y.1 x.1 ^ (k + α : ℝ) + cF * dist y.2 x.2 ^ (k + α : ℝ) := by
        simp only [mem_ball, Prod.dist_eq, lt_inf_iff, sup_lt_iff] at hy
        gcongr
        · refine hrE (y, (x.1, y.2)) ?_ ?_ |>.trans_eq ?_
          · simp [Prod.dist_eq, hy]
          · simp [e]
          · simp (disch := positivity) [Prod.dist_eq, e, hβinv]
        · apply hrF
          simp [e, hy]
      _ ≤ (cE + cF) * dist y x ^ (k + α : ℝ) := by
        rw [add_mul]
        gcongr <;> simp [Prod.dist_eq]

variable (E F) in
noncomputable def boundCoeff (n k : ℕ) (α : I) : ℝ≥0∞ := by
  borelize E
  borelize F
  exact 4 ^ (sardMoreiraBound n k α (dim E) : ℝ) /
    (μH[dim E] (ball (0 : E) 1) * μH[dim F] (ball (0 : F) 1))

protected theorem hausdorffMeasure_image_le_mul {X : Type*} [MetricSpace X]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace X] [BorelSpace X]
    {f : E × F → X} {s : Set (E × F)} {n : ℕ} (hk : k ≠ 0) (hn : dim E + dim F ≤ n)
    {cE cF : ℝ≥0} (hcE₀ : cE ≠ 0) (hcF₀ : cF ≠ 0)
    (hcE : ∀ x ∈ s, ∀ᶠ y in 𝓝 (x, x), y.1.2 = y.2.2 → dist (f y.1) (f y.2) ≤ cE * dist y.1 y.2)
    (hcF : ∀ x ∈ s, ∀ᶠ y in 𝓝 x.2, dist (f (x.1, y)) (f x) ≤ cF * dist y x.2 ^ (k + α : ℝ)) :
    μH[sardMoreiraBound n k α (dim E)] (f '' s) ≤
      boundCoeff E F n k α * cE ^ dim E * cF ^ ((n - dim E) / (k + α) : ℝ) *
        (μH[dim E].prod μH[dim F] s) := by
  have := α.2.1
  set c := cF / cE
  set e : (E × F) ≃ₜ (E × F) := .prodCongr (.smulOfNeZero c (by positivity)) (.refl F)
  set t := e ⁻¹' s
  set g : E × F → X := f ∘ e
  have hcE' : ∀ x ∈ t, ∀ᶠ y in 𝓝 (x, x), y.1.2 = y.2.2 →
      dist (g y.1) (g y.2) ≤ ↑(cE * c) * dist y.1 y.2 := by
    intro x hx
    specialize hcE (e x) hx
    refine ((map_continuous e).prodMap (map_continuous e)).tendsto (x, x)
      |>.eventually hcE |>.mono fun y hy hy_eq ↦ ?_
    refine (hy hy_eq).trans_eq ?_
    simp [e, NNReal.smul_def, Prod.map, dist_smul₀, hy_eq, mul_assoc]
    simp [Prod.dist_eq, hy_eq]
  have hcF' : ∀ x ∈ t, ∀ᶠ y in 𝓝 x.2, dist (g (x.1, y)) (g x) ≤ cF * dist y x.2 ^ (k + α : ℝ) := by
    intro x hx
    exact hcF (e x) hx
  have hgt : g '' t = f '' s := by simp only [t, g, Set.image_comp, e.image_preimage]
  rw [← hgt]
  refine hausdorffMeasure_image_le_mul_aux hk hn hcE' hcF' |>.trans_eq ?_
  have : μH[dim E].prod μH[dim F] t = μH[dim E].prod μH[dim F] s / c ^ dim E := by
    have : μH[dim E].prod μH[dim F] = (c ^ dim E • μH[dim E].prod μH[dim F]).map e := by
      refine Measure.prod_eq fun s t hs ht ↦ ?_
      rw [e.measurableEmbedding.map_apply, Measure.coe_nnreal_smul_apply]
      simp (disch := first | positivity | finiteness)
        [e, Set.preimage_prod_map_prod, Set.preimage_smul₀,
          ← ENNReal.inv_pow, mul_assoc, ENNReal.mul_inv_cancel_left]
    conv_rhs => rw [this]
    rw [e.measurableEmbedding.map_apply, Measure.coe_nnreal_smul_apply, ENNReal.coe_pow,
      mul_div_assoc, ENNReal.mul_div_cancel]
    · positivity
    · finiteness
  simp (disch := positivity) only [this, ← mul_assoc, c, mul_div_cancel₀, ← two_mul]
  rw [← mul_div_assoc, ENNReal.mul_div_right_comm, ENNReal.div_right_comm, boundCoeff]
  congr 1
  norm_num1
  rw [← ENNReal.mul_div_right_comm, ← ENNReal.mul_div_right_comm]
  borelize E; borelize F
  congr 1
  rw [← ENNReal.coe_pow, div_pow, ENNReal.coe_div, ENNReal.coe_pow, ENNReal.coe_pow,
    ENNReal.mul_rpow_of_nonneg, mul_div_assoc, mul_assoc]
  · congr 1
    rw [← ENNReal.div_mul, ← ENNReal.rpow_natCast, ← ENNReal.rpow_sub, mul_comm]
    · congr 2
      have : (dim E : ℝ≥0) ≤ n := by grw [← hn]; simp
      simp [sardMoreiraBound, NNReal.coe_sub this]
      change ((n : ℝ) - dim E) / ((k : ℝ) + α) =
        ((n : ℝ) - dim E) / ((k : ℝ) + α)
      rfl
    · positivity
    · finiteness
    · left; positivity
    · left; finiteness
  · positivity
  · positivity

theorem hausdorffMeasure_image_null_of_isBigO {X : Type*} [MetricSpace X]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace X] [BorelSpace X]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → X} {s : Set (E × F)} {n : ℕ} {cE : NNReal} (hk : k ≠ 0)
    (hn : dim E + dim F ≤ n)
    (hcE : ∀ x ∈ s, ∀ᶠ y in 𝓝 (x, x), y.1.2 = y.2.2 → dist (f y.1) (f y.2) ≤ cE * dist y.1 y.2)
    (h_isBigO : ∀ x ∈ s,
      (fun y ↦ dist (f (x.1, y)) (f x)) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)))
    (hs : μH[dim E].prod μH[dim F] s = 0) :
    μH[sardMoreiraBound n k α (dim E)] (f '' s) = 0 := by
  wlog H : ∃ cF : ℝ≥0, 0 < cF ∧ ∀ x ∈ s, ∀ᶠ y in 𝓝 x.2,
    dist (f (x.1, y)) (f x) ≤ cF * (dist y x.2) ^ (k + α : ℝ) generalizing s
  · set t : ℕ → Set (E × F) := fun N ↦
      {x ∈ s | ∀ᶠ y in 𝓝 x.2, dist (f (x.1, y)) (f x) ≤ (N + 1) * (dist y x.2) ^ (k + α : ℝ)}
    rw [← nonpos_iff_eq_zero]
    calc μH[sardMoreiraBound n k α (dim E)] (f '' s)
      _ ≤ μH[sardMoreiraBound n k α (dim E)] (f '' ⋃ N, t N) := by
        gcongr
        intro x hx
        rcases (h_isBigO x hx).exists_nonneg with ⟨C, hC₀, hC⟩
        rcases exists_nat_gt C with ⟨N, hN⟩
        refine Set.mem_iUnion_of_mem N ?_
        use hx
        rw [Asymptotics.IsBigOWith_def] at hC
        refine hC.mono fun y hy ↦ ?_
        rw [Real.norm_of_nonneg (by positivity)] at hy
        grw [hy, dist_eq_norm_sub, hN, Real.norm_of_nonneg (by positivity)]
        gcongr
        simp
      _ ≤ ∑' N, μH[sardMoreiraBound n k α (dim E)] (f '' t N) := by
        grw [Set.image_iUnion, measure_iUnion_le]
      _ = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro N
        apply this
        · exact fun x hx ↦ hcE x hx.1
        · exact fun x hx ↦ h_isBigO x hx.1
        · exact measure_mono_null (Set.sep_subset _ _) hs
        · exact ⟨N + 1, by positivity, fun x hx ↦ mod_cast hx.2⟩
  rcases H with ⟨cF, hcF₀, hcF⟩
  wlog hcE₀ : cE ≠ 0 generalizing cE
  · refine @this (cE + 1) (fun x hx ↦ ?_) (by positivity)
    grw [← le_self_add]
    exact hcE x hx
  simpa [hs] using Moreira2001.hausdorffMeasure_image_le_mul hk hn hcE₀ hcF₀.ne' hcE hcF

theorem hausdorffMeasure_image_null_of_isLittleO {X : Type*} [MetricSpace X]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace X] [BorelSpace X]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → X} {s : Set (E × F)} {n : ℕ} {cE : NNReal} (hk : k ≠ 0) (hnp : dim E < n)
    (hn : dim E + dim F ≤ n)
    (hcE : ∀ x ∈ s, ∀ᶠ y in 𝓝 (x, x), y.1.2 = y.2.2 → dist (f y.1) (f y.2) ≤ cE * dist y.1 y.2)
    (h_isLittleO : ∀ x ∈ s, (fun y ↦ dist (f (x.1, y)) (f x)) =o[𝓝 x.2]
      (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ))) :
    μH[sardMoreiraBound n k α (dim E)] (f '' s) = 0 := by
  wlog H : ∃ N : ℕ, s ⊆ ball 0 N generalizing s
  · rw [← nonpos_iff_eq_zero]
    calc μH[sardMoreiraBound n k α (dim E)] (f '' s)
      _ = μH[sardMoreiraBound n k α (dim E)] (f '' ⋃ N : ℕ, s ∩ ball 0 N) := by
        rw [← Set.inter_iUnion, iUnion_ball_nat, Set.inter_univ]
      _ ≤ ∑' N : ℕ, μH[sardMoreiraBound n k α (dim E)] (f '' (s ∩ ball 0 N)) := by
        rw [Set.image_iUnion]
        apply measure_iUnion_le
      _ = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro N
        apply this
        · exact fun x hx ↦ hcE x hx.1
        · exact fun x hx ↦ h_isLittleO x hx.1
        · exact ⟨N, Set.inter_subset_right⟩
  rcases H with ⟨N, hN⟩
  wlog hcE₀ : cE ≠ 0 generalizing cE
  · refine @this (cE + 1) (fun x hx ↦ ?_) (by positivity)
    grw [← le_self_add]
    exact hcE x hx
  have Hbound : ∀ cF : ℝ≥0, cF ≠ 0 →
      μH[sardMoreiraBound n k α (dim E)] (f '' s) ≤
        boundCoeff E F n k α * cE ^ dim E * cF ^ ((n - dim E) / (k + α) : ℝ) *
          (μH[dim E].prod μH[dim F] s) := by
    intro cF hcF₀
    apply Moreira2001.hausdorffMeasure_image_le_mul hk hn hcE₀ hcF₀ hcE
    intro x hx
    simp (disch := positivity) only [Asymptotics.isLittleO_iff, ← dist_eq_norm_sub,
      Real.norm_of_nonneg] at h_isLittleO
    exact h_isLittleO x hx (by positivity)
  suffices
      Filter.Tendsto
        (fun cF : ℝ≥0 ↦ boundCoeff E F n k α * cE ^ dim E * cF ^ ((n - dim E) / (k + α) : ℝ) *
          (μH[dim E].prod μH[dim F] s))
        (𝓝[≠] 0) (𝓝 0) by
    rw [← nonpos_iff_eq_zero]
    exact ge_of_tendsto this <| eventually_mem_nhdsWithin.mono Hbound
  refine Filter.Tendsto.mono_left ?_ nhdsWithin_le_nhds
  apply Continuous.tendsto'
  · have : (μH[dim E].prod μH[dim F]) s ≠ ⊤ := by
      grw [← lt_top_iff_ne_top, hN]
      exact measure_ball_lt_top
    have : boundCoeff E F n k α * cE ^ dim E ≠ ⊤ := by
      rw [boundCoeff]
      apply_rules [ENNReal.mul_ne_top, ENNReal.div_ne_top, ENNReal.inv_ne_top.mpr,
        ENNReal.rpow_ne_top_of_nonneg, mul_ne_zero, IsOpen.measure_ne_zero, isOpen_ball,
        ENNReal.pow_ne_top]
      · positivity
      · simp
      · simp
      · simp
      · simp
    fun_prop (disch := assumption)
  · suffices (0 : ℝ) < (n - dim E) / (k + α) by simp [this]
    refine div_pos (sub_pos_of_lt <| mod_cast hnp) ?_
    have := α.2.1; positivity

theorem hausdorffMeasure_image_piProd_fst_null_of_isBigO_isLittleO
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    [MeasurableSpace G] [BorelSpace G]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → G} {s : Set (E × F)} {n : ℕ} (hk : k ≠ 0) (hnp : dim E < n)
    (hn : dim E + dim F ≤ n)
    (h_contDiff : ∀ x ∈ s, ContDiffAt ℝ 1 f x)
    (h_isBigO : ∀ x ∈ s, (fun y ↦ f (x.1, y) - f x) =O[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ)))
    (h_isLittleO : ∀ᵐ x ∂(μH[dim E].prod μH[dim F]), x ∈ s →
      (fun y ↦ f (x.1, y) - f x) =o[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ))) :
    μH[sardMoreiraBound n k α (dim E)] (Function.prod Prod.fst f '' s) = 0 := by
  set g := Function.prod Prod.fst f
  set d := sardMoreiraBound n k α (dim E)
  have hgf (x y) : dist (g x) (g y) = max (‖x.1 - y.1‖) (‖f x - f y‖) := by
    simp [g, dist_eq_norm_sub]
  wlog H : ∃ cE : ℝ≥0, cE ≠ 0 ∧ ∀ x ∈ s,
    ∀ᶠ y in 𝓝 (x, x), y.1.2 = y.2.2 → dist (g y.1) (g y.2) ≤ cE * dist y.1 y.2 generalizing s
  · set t : ℕ → Set (E × F) := fun N ↦
      {x | ∀ᶠ y in 𝓝 (x, x), y.1.2 = y.2.2 → dist (g y.1) (g y.2) ≤ (N + 1) * dist y.1 y.2}
    rw [← nonpos_iff_eq_zero]
    calc
      μH[d] (g '' s) ≤ μH[d] (g '' ⋃ N, s ∩ t N) := by
        gcongr
        intro x hx
        rcases (h_contDiff x hx).hasStrictFDerivAt (by simp) |>.isBigO_sub.bound with ⟨C, hC⟩
        rcases exists_nat_gt C with ⟨N, hN⟩
        refine Set.mem_iUnion_of_mem N ⟨hx, ?_⟩
        refine hC.mono fun y hy hy_eq ↦ ?_
        grw [hgf, hy, max_le_iff, hN, dist_eq_norm_sub]
        constructor
        · grw [← le_add_of_nonneg_left]
          · simp [Prod.norm_def]
          · positivity
        · gcongr
          simp
      _ ≤ ∑' N, μH[d] (g '' (s ∩ t N)) := by
        simp only [Set.image_iUnion]
        apply measure_iUnion_le
      _ = 0 := by
        rw [ENNReal.tsum_eq_zero]
        intro N
        apply this
        · exact fun x hx ↦ h_contDiff x hx.1
        · exact fun x hx ↦ h_isBigO x hx.1
        · grw [Set.inter_subset_left]
          exact h_isLittleO
        · exact ⟨N + 1, by positivity, fun x hx ↦ hx.2⟩
  rcases H with ⟨cE, hcE₀, hcE⟩
  set t : Set (E × F) :=
    {x | (fun y ↦ g (x.1, y) - g x) =o[𝓝 x.2] (fun y ↦ ‖y - x.2‖ ^ (k + α : ℝ))}
  have ht : μH[d] (g '' (s ∩ t)) = 0 :=
    hausdorffMeasure_image_null_of_isLittleO hk hnp hn (fun x hx ↦ hcE x hx.1) fun x hx ↦ by
      simpa [t, dist_eq_norm_sub] using hx.2
  have ht' : μH[d] (g '' (s \ t)) = 0 := by
    apply hausdorffMeasure_image_null_of_isBigO hk hn (fun x hx ↦ hcE x hx.1)
    · intro x hx
      refine .trans ?_ (h_isBigO x hx.1)
      refine .of_norm_norm ?_
      simp only [← dist_eq_norm_sub, hgf]
      simp [Asymptotics.isBigO_refl]
    · refine measure_mono_null ?_ h_isLittleO
      rintro x ⟨hxs, hxt⟩ hxs'
      specialize hxs' hxs
      apply hxt
      refine Asymptotics.IsBigO.trans_isLittleO ?_ hxs'
      refine .of_norm_norm ?_
      simp only [← dist_eq_norm_sub, hgf]
      simp [Asymptotics.isBigO_refl]
  rw [← Set.inter_union_diff s t, Set.image_union]
  exact measure_union_null ht ht'

theorem hausdorffMeasure_image_piProd_fst_null_of_fderiv_comp_inr_zero
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
    [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → G} {s : Set (E × F)} (hf : ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x) (hk : k ≠ 0)
    (hs : ∀ x ∈ s, fderiv ℝ f x ∘L .inr ℝ E F = 0) :
    μH[sardMoreiraBound (dim E + dim F) k α (dim E)]
      (Function.prod Prod.fst f '' s) = 0 := by
  rcases Nat.exists_add_one_eq.mpr (pos_iff_ne_zero.mpr hk) with ⟨k, rfl⟩
  suffices ∀ ψ ∈ (Atlas.main k α s).charts,
      μH[sardMoreiraBound (dim E + dim F) (k + 1) α (dim E)]
        ((Function.prod Prod.fst f ∘ ψ) '' ψ.set) = 0 by
    rw [← measure_biUnion_null_iff] at this
    · refine measure_mono_null ?_ this
      simp only [Set.image_comp, ← Set.image_iUnion₂]
      gcongr
      refine (Atlas.main k α s).subset_biUnion_isLargeAt.trans ?_
      gcongr
      apply Set.sep_subset
    · apply Atlas.countable
  intro ψ hψ
  set g := Function.prod Prod.fst (f ∘ ψ)
  suffices μH[sardMoreiraBound (dim E + dim F) (k + 1) α (dim E)] (g '' ψ.set) = 0 by
    simpa [g] using this
  apply hausdorffMeasure_image_piProd_fst_null_of_isBigO_isLittleO
  · simp
  · simp [Module.finrank_pos]
  · grw [ψ.finrank_le]
  · intro x hx
    refine .comp _ ?_ (ψ.contDiffAt hx)
    exact hf _ (ψ.mapsTo hx) |>.contDiffAt.of_le (by simp)
  · intro x hx
    push_cast
    apply Atlas.isBigO_main_sub_of_fderiv_zero_right hψ hx
    · filter_upwards [eventually_mem_nhdsWithin] with x hx using hf _ hx
    · filter_upwards [eventually_mem_nhdsWithin] using hs
  · push_cast
    filter_upwards [Besicovitch.ae_tendsto_measure_sectr_inter_closedBall_div
      (μH[dim E]) (μH[dim ψ.Dom]) (measurableSet_closure (s := ψ.set))] with x hx hψx
    apply Atlas.isLittleO_main_sub_of_fderiv_zero_right hψ hψx
    · filter_upwards [eventually_mem_nhdsWithin] with y hy using hf _ hy
    · filter_upwards [eventually_mem_nhdsWithin] using hs
    · convert hx using 1
      · ext r
        simp [Set.preimage]
      · simp [Set.indicator_of_mem (subset_closure hψx)]

theorem hausdorffMeasure_image_piProd_fst_null_of_finrank_eq
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace G] [BorelSpace G]
    [Nontrivial F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E × F → G} {s : Set (E × F)} (hf : ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x) (hk : k ≠ 0)
    (hs : ∀ x ∈ s, dim (fderiv ℝ (Function.prod Prod.fst f) x).range = dim E) :
    μH[sardMoreiraBound (dim E + dim F) k α (dim E)]
      (Function.prod Prod.fst f '' s) = 0 := by
  apply hausdorffMeasure_image_piProd_fst_null_of_fderiv_comp_inr_zero hf hk
  intro x hx
  rw [← ContinuousLinearMap.coe_inj, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.coe_inr, ContinuousLinearMap.toLinearMap_zero,
    ← LinearMap.finrank_range_prod_fst_iff_comp_inr_eq_zero, ← hs x hx]
  suffices fderiv ℝ (Function.prod Prod.fst f) x = .prod (.fst ℝ E F) (fderiv ℝ f x) by
    -- TODO: introduce&use `ContinuousLinearMap.rank`/`ContinuousLinearMap.finrank`?
    generalize H : fderiv ℝ (Function.prod Prod.fst f) x = f'
    rw [H] at this
    subst f'
    rfl
  unfold Function.prod
  rw [DifferentiableAt.fderiv_prodMk (by fun_prop), fderiv_fst]
  exact hf _ hx |>.differentiableAt hk

theorem hausdorffMeasure_image_nhdsWithin_null_of_finrank_eq
    [CompleteSpace F] [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < dim E) (hk : k ≠ 0) {f : E → F} {s : Set E}
    (hf : ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x)
    (hs : ∀ x ∈ s, (fderiv ℝ f x).finrank = p) {a : E} (ha : a ∈ s) :
    ∃ t ∈ 𝓝[s] a, μH[sardMoreiraBound (dim E) k α p] (f '' t) = 0 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by grind)
  obtain ⟨Ker, Range, Coker, eDom, eCod, hfin₁, hfin₂, hdimKer, hdimRange, haeDom, hinv,
      hcdmh, hfst⟩ :
      ∃ (Ker : Submodule ℝ E) (Range Coker : Submodule ℝ F)
        (eDom : OpenPartialHomeomorph E (Range × Ker)) (eCod : F ≃L[ℝ] (Range × Coker)),
        FiniteDimensional ℝ Ker ∧ FiniteDimensional ℝ Range ∧
        dim Ker = dim E - p ∧ dim Range = p ∧ a ∈ eDom.source ∧
        (fderiv ℝ eDom a).IsInvertible ∧
        (∀ x ∈ s, ContDiffMoreiraHolderAt k α eDom x) ∧
        (∀ x, (eDom x).1 = (eCod (f x)).1) := by
    have hker : (fderiv ℝ f a).ker.ClosedComplemented := .of_finiteDimensional _
    have hrange : (fderiv ℝ f a).range.ClosedComplemented := .of_finiteDimensional _
    use (fderiv ℝ f a).ker, (fderiv ℝ f a).range, hrange.choose.ker
    have hdf := (hf a ha).contDiffAt.hasStrictFDerivAt (by simpa [Nat.one_le_iff_ne_zero])
    set eDom := hdf.implicitToOpenPartialHomeomorphOfComplementedKerRange _ _ hker hrange
    refine ⟨eDom,
      .equivOfRightInverse hrange.choose (Submodule.subtypeL _) hrange.choose_spec,
      inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← (fderiv ℝ f a).finrank_range_add_finrank_ker, ← hs a ha, ContinuousLinearMap.finrank,
        Nat.add_sub_cancel_left]
    · exact hs a ha
    · simp [eDom]
    · simpa [eDom] using
        hdf.isInvertible_fderiv_implicitToOpenPartialHomeomorphOfComplementedKerRange
          hker hrange
    · intro x hx
      rw [hdf.coe_implicitToOpenPartialHomeomorphOfComplementedKerRange hker hrange]
      exact .prodMk (.comp (ContinuousLinearMap.contDiffMoreiraHolderAt _) (hf x hx) hk)
        (ContinuousLinearMap.contDiffMoreiraHolderAt _)
    · intro x
      simp [eDom]
  have : Nontrivial Ker := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    grind
  set g : (Range × Ker) → Coker := fun x ↦ (eCod <| f <| eDom.symm x).2
  set t := eDom.target ∩ eDom.symm ⁻¹' {x ∈ s | (fderiv ℝ eDom x).IsInvertible}
  have hgt : ∀ x ∈ t, ContDiffMoreiraHolderAt k α g x := by
    intro x hx
    refine .comp .snd (eCod.contDiffMoreiraHolderAt.comp (.comp ?_ ?_ hk) hk) hk
    · exact hf _ hx.2.1
    · exact eDom.contDiffMoreiraHolderAt_symm hx.1 hx.2.2 (hcdmh _ hx.2.1)
  have hg_eqOn : eDom.target.EqOn (Function.prod Prod.fst g) (eCod ∘ f ∘ eDom.symm) := by
    intro x hx
    ext <;> simp [← hfst, hx, g]
  have hgdim : ∀ x ∈ t, (fderiv ℝ (Function.prod Prod.fst g) x).finrank = dim Range := by
    intro x hx
    have hd : DifferentiableAt ℝ eDom.symm x :=
      eDom.contDiffMoreiraHolderAt_symm hx.1 hx.2.2 (hcdmh _ hx.2.1) |>.differentiableAt hk
    rw [hdimRange, hg_eqOn.eventuallyEq_of_mem (eDom.open_target.mem_nhds hx.1) |>.fderiv_eq,
      fderiv_comp, eCod.fderiv, eCod.finrank_comp_left, fderiv_comp,
      ContinuousLinearMap.finrank_comp_eq_left_of_surjective, hs _ hx.2.1]
    · exact eDom.surjective_fderiv_symm hx.1 hx.2.2
    · exact hf _ hx.2.1 |>.differentiableAt hk
    · exact hd
    · exact eCod.differentiableAt
    · exact hf _ hx.2.1 |>.differentiableAt hk |>.comp _ hd
  refine ⟨eDom.symm '' t, ?_, ?_⟩
  · convert_to eDom.symm '' t ∈ Filter.map eDom.symm (𝓝[t] (eDom a))
    · rw [eDom.nhdsWithin_target_inter (eDom.mapsTo haeDom),
        eDom.symm.map_nhdsWithin_preimage_eq (eDom.mapsTo haeDom),
        Set.setOf_and, eDom.leftInvOn haeDom, Set.setOf_mem_eq, nhdsWithin_inter_of_mem']
      apply mem_nhdsWithin_of_mem_nhds
      exact (hcdmh _ ha).contDiffAt.eventually_isInvertible_fderiv hinv (by positivity)
    · exact Filter.image_mem_map self_mem_nhdsWithin
  · have := hausdorffMeasure_image_piProd_fst_null_of_finrank_eq hgt hk hgdim
    rw [hdimKer, hdimRange, Nat.add_sub_cancel' hp_dom.le] at this
    convert (eCod.symm.lipschitz.hausdorffMeasure_image_null (by positivity) this) using 2
    rw [Set.image_image, Set.image_image]
    apply Set.EqOn.image_eq
    intro x hx
    simp only [hg_eqOn hx.1, Function.comp_apply, eCod.symm_apply_apply]

theorem hausdorffMeasure_image_null_of_finrank_eq [MeasurableSpace F] [BorelSpace F]
    [CompleteSpace F] (hp_dom : p < dim E) (hk : k ≠ 0) {f : E → F} {s : Set E}
    (hf : ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x)
    (hs : ∀ x ∈ s, dim (fderiv ℝ f x).range = p) :
    μH[sardMoreiraBound (dim E) k α p] (f '' s) = 0 := by
  have : FiniteDimensional ℝ E := .of_finrank_pos (by grind)
  rw [← coe_toOuterMeasure, ← OuterMeasure.comap_apply]
  refine measure_null_of_locally_null _ fun x hx ↦ ?_
  apply hausdorffMeasure_image_nhdsWithin_null_of_finrank_eq <;> assumption

end Moreira2001

open UniformSpace in
theorem hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le
    [MeasurableSpace F] [BorelSpace F]
    (hp_dom : p < dim E) (hk : k ≠ 0) {f : E → F} {s : Set E}
    (hf : ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x)
    (hs : ∀ x ∈ s, dim (fderiv ℝ f x).range ≤ p) :
    μH[sardMoreiraBound (dim E) k α p] (f '' s) = 0 := by
  wlog hF : CompleteSpace F generalizing F
  · borelize (Completion F)
    set e : F →ₗᵢ[ℝ] Completion F := Completion.toComplₗᵢ
    rw [← e.isometry.hausdorffMeasure_image, Set.image_image]
    apply this
    · exact fun x hx ↦ (hf x hx).continuousLinearMap_comp e.toContinuousLinearMap
    · intro x hx
      grw [fderiv_comp', ← hs x hx]
      · change dim (LinearMap.range ((fderiv ℝ e (f x)).toLinearMap ∘ₗ
          (fderiv ℝ f x).toLinearMap)) ≤ _
        rw [LinearMap.range_comp, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj]
        simp [LinearMap.domRestrict, e, Function.Injective,
          show fderiv ℝ (↑) (f x) = e.toContinuousLinearMap from e.toContinuousLinearMap.fderiv]
      · exact e.toContinuousLinearMap.differentiableAt
      · exact (hf x hx).differentiableAt hk
    · infer_instance
    · left; positivity
  -- Apply the Moreira2001 theorem to each of the sets where the rank is exactly `p' ≤ p`.
  have h_apply : ∀ p' ≤ p,
      μH[sardMoreiraBound (dim E) k α p'] (f '' {x ∈ s | dim (fderiv ℝ f x).range = p'}) = 0 := by
    intro p' hp'
    apply Moreira2001.hausdorffMeasure_image_null_of_finrank_eq
    · grind
    · exact hk
    · exact fun x hx ↦ hf x hx.1
    · simp
  -- Since $s$ is the union of the sets where the rank is exactly $p'$ for $p' \leq p$,
  -- we can use the countable subadditivity of the Hausdorff measure.
  have h_union : f '' s = ⋃ p' ≤ p, f '' {x ∈ s | dim (fderiv ℝ f x).range = p'} := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨fun ⟨x, hx, hx'⟩ ↦ ⟨_, hs x hx, x, ⟨hx, rfl⟩, hx'⟩,
      fun ⟨i, hi, x, hx, hx'⟩ ↦ ⟨x, hx.1, hx'⟩⟩
  simp only [h_union, measure_iUnion_null_iff]
  intro p' hp'
  rw [← nonpos_iff_eq_zero, ← h_apply p' hp']
  apply hausdorffMeasure_mono
  exact monotone_sardMoreiraBound _ hk _ hp'

theorem dimH_image_le_sardMoreiraBound_of_finrank_le
    (hp_dom : p < dim E) (hk : k ≠ 0) {f : E → F} {s : Set E}
    (hf : ∀ x ∈ s, ContDiffMoreiraHolderAt k α f x)
    (hs : ∀ x ∈ s, dim (fderiv ℝ f x).range ≤ p) :
    dimH (f '' s) ≤ sardMoreiraBound (dim E) k α p := by
  borelize F
  apply dimH_le_of_hausdorffMeasure_ne_top
  simp [hausdorffMeasure_sardMoreiraBound_image_null_of_finrank_le hp_dom hk hf hs]

open scoped ContDiff

/-- Rank drop for a real linear map into a positive-dimensional space is equivalent to
`finrank (range) ≤ dim F - 1`. -/
theorem finrank_range_le_sub_one_of_not_surjective
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {A : E →L[ℝ] F}
    (hA : ¬ Function.Surjective A) :
    dim A.range ≤ dim F - 1 := by
  have hne : A.range ≠ ⊤ := by
    intro htop
    exact hA (LinearMap.range_eq_top.mp htop)
  have hlt : dim A.range < dim F := Submodule.finrank_lt hne
  exact Nat.le_sub_one_of_lt hlt

/-- Moreira's bound with source dimension `m`, order `m + 1` and rank cap `n - 1` is strictly
less than the target dimension `n`, provided `1 ≤ n ≤ m`. -/
theorem sardMoreiraBound_succ_subOne_lt
    {m n : ℕ} (hn : 1 ≤ n) (hle : n ≤ m) (α : I) :
    sardMoreiraBound m (m + 1) α (n - 1) < n := by
  have hk : m + 1 ≠ 0 := Nat.succ_ne_zero m
  have hp : n - 1 ≤ m := (Nat.sub_le n 1).trans hle
  have hα : 0 ≤ (α : ℝ) := α.2.1
  have hpos : (0 : ℝ) < ↑(m + 1) + α := by positivity
  rw [← NNReal.coe_lt_coe]
  set B := sardMoreiraBound m (m + 1) α (n - 1)
  have hmul := mul_sardMoreiraBound hk hp α
  have hcmp : (↑(m + 1) + α) * (B : ℝ) < (↑(m + 1) + α) * n := by
    have hn1 : (1 : ℝ) ≤ n := mod_cast hn
    have hnm : (n : ℝ) ≤ m := mod_cast hle
    have hnpred : ((n - 1 : ℕ) : ℝ) = n - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    have hm1 : ((m + 1 : ℕ) : ℝ) = m + 1 := Nat.cast_succ m
    rw [hmul, hnpred, hm1]
    ring_nf
    linarith
  exact (mul_lt_mul_iff_of_pos_left hpos).1 hcmp

/-- Additive Haar measure vanishes on a set of Hausdorff dimension strictly below the ambient
finite dimension. -/
theorem addHaar_eq_zero_of_dimH_lt_finrank
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (μ : Measure F) [μ.IsAddHaarMeasure] {s : Set F}
    (hdim : dimH s < dim F) : μ s = 0 := by
  have hμH :
      μH[(dim F : ℝ)] s = 0 := by
    simpa using
      hausdorffMeasure_of_dimH_lt (d := (dim F : ℝ≥0)) (s := s) (by simpa using hdim)
  rw [Measure.isAddLeftInvariant_eq_smul μ (μH[(dim F : ℝ)])]
  simp [hμH]

/-- Ordinary Sard's theorem on an arbitrary subset of a `C^∞` map between finite-dimensional
real normed spaces: the image of the critical set has additive Haar measure zero.

This is the ambient/`ContDiffAt` form. It does not claim a `ContDiffWithinAt` statement on a
proper closed model range (half-spaces, corners) without an extension or restriction argument. -/
theorem addHaar_image_critical_eq_zero
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {s : Set E}
    (hf : ∀ x ∈ s, ContDiffAt ℝ ∞ f x)
    (hcrit : ∀ x ∈ s, ¬ Function.Surjective (fderiv ℝ f x))
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (f '' s) = 0 := by
  by_cases hF : dim F = 0
  · have hs : s = ∅ := by
      ext x
      constructor
      · intro hx
        have : Subsingleton F := (Module.finrank_zero_iff (R := ℝ)).1 hF
        have : Function.Surjective (fderiv ℝ f x) := fun y => ⟨0, Subsingleton.elim _ _⟩
        exact (hcrit x hx this).elim
      · simp
    simp [hs]
  have hFpos : 1 ≤ dim F := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hF)
  let k : ℕ := dim E + 1
  have hk : k ≠ 0 := Nat.succ_ne_zero _
  have hk_lt : (k : WithTop ℕ∞) < (∞ : WithTop ℕ∞) :=
    WithTop.coe_lt_coe.2 (ENat.coe_lt_top k)
  let Crit : Set E := {x ∈ s | ¬ Function.Surjective (fderiv ℝ f x)}
  have hCrit : Crit = s := by
    ext x
    constructor
    · intro hx
      exact hx.1
    · intro hx
      exact ⟨hx, hcrit x hx⟩
  rw [← hCrit]
  by_cases hdim : dim E < dim F
  · have hC1 : ∀ x ∈ Crit, ContDiffAt ℝ 1 f x := fun x hx => (hf x hx.1).of_le (by simp)
    have hloc :
        ∀ x ∈ Crit, ∃ C : ℝ≥0, ∃ t ∈ 𝓝[Crit] x, LipschitzOnWith C f t := by
      intro x hx
      obtain ⟨C, u, hu, hLip⟩ := (hC1 x hx).exists_lipschitzOnWith
      refine ⟨C, Crit ∩ u, inter_mem_nhdsWithin _ hu, hLip.mono Set.inter_subset_right⟩
    have hdimImage : dimH (f '' Crit) < dim F := by
      calc
        dimH (f '' Crit) ≤ dimH Crit := dimH_image_le_of_locally_lipschitzOn hloc
        _ ≤ dimH (Set.univ : Set E) := dimH_mono (Set.subset_univ _)
        _ = dim E := Real.dimH_univ_eq_finrank E
        _ < dim F := Nat.cast_lt.mpr hdim
    exact addHaar_eq_zero_of_dimH_lt_finrank μ hdimImage
  have hle : dim F ≤ dim E := Nat.le_of_not_gt hdim
  have hp_dom : dim F - 1 < dim E := by
    have : dim F - 1 ≤ dim E - 1 := Nat.sub_le_sub_right hle 1
    have hEpos : 1 ≤ dim E := le_trans hFpos hle
    calc
      dim F - 1 ≤ dim E - 1 := this
      _ < dim E := Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hEpos)
  have hholder : ∀ x ∈ Crit, ContDiffMoreiraHolderAt k 0 f x :=
    fun x hx => (hf x hx.1).contDiffMoreiraHolderAt hk_lt 0
  have hrank : ∀ x ∈ Crit, dim (fderiv ℝ f x).range ≤ dim F - 1 :=
    fun x hx => finrank_range_le_sub_one_of_not_surjective hx.2
  have hdimImage : dimH (f '' Crit) < dim F := by
    have hleBound :
        dimH (f '' Crit) ≤ sardMoreiraBound (dim E) k 0 (dim F - 1) :=
      dimH_image_le_sardMoreiraBound_of_finrank_le hp_dom hk hholder hrank
    exact hleBound.trans_lt <| by
      exact_mod_cast sardMoreiraBound_succ_subOne_lt hFpos hle (0 : I)
  exact addHaar_eq_zero_of_dimH_lt_finrank μ hdimImage

/-- Ordinary Sard for a globally `C^∞` map. -/
theorem addHaar_image_critical_eq_zero_of_contDiff
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (f '' {x | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  addHaar_image_critical_eq_zero (fun x _ => hf.contDiffAt) (fun _ hx => hx) μ

/-- Ordinary Sard for a `C^∞` map on an open set. This is the form used by chartwise
Euclidean reductions on the interior of a model range. -/
theorem addHaar_image_critical_eq_zero_of_contDiffOn
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    {f : E → F} {U : Set E} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (μ : Measure F) [μ.IsAddHaarMeasure] :
    μ (f '' {x ∈ U | ¬ Function.Surjective (fderiv ℝ f x)}) = 0 :=
  addHaar_image_critical_eq_zero
    (fun x hx => (hf x hx.1).contDiffAt (hU.mem_nhds hx.1))
    (fun _ hx => hx.2) μ
