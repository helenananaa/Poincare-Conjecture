import LeeSmoothLib.Ch01.Sec01_06.SeeleyCoefficientData
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Normed.Group.Tannery

/-!
Analysis of the cutoff-weighted Seeley series on a closed lower half-ball.

The g15 off-boundary jet that ignored the cutoff (and all of its derivatives) is false:
already at order `0`, with `f = 1` and a pole deep enough that every cutoff vanishes, the
series is `0` while the uncut combination is `∑ a_j = 1`. This file constructs the actual
Leibniz Taylor field of each cutoff-weighted reflected term, proves uniform derivative
bounds, sums the series, identifies boundary jets from the scalar moment identities, and
glues to the upper field.
-/

noncomputable section

open Set Filter Metric Function
open scoped Topology ContDiff InnerProductSpace

namespace LeeSmooth.SeeleyExtension

universe v
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable {n : ℕ} [NeZero n]

/-! ## Local geometry of the scaled cutoff and the geometric reflection -/

/-- Linear functional implementing the cutoff argument `-2^j z₀ / ε`. -/
def seeleyCutoffCLM (j : ℕ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
  (-((2 : ℝ) ^ j) / ε) • EuclideanSpace.proj (0 : Fin n)

lemma seeleyCutoffCLM_apply (j : ℕ) (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    seeleyCutoffCLM (n := n) j ε z = -((2 : ℝ) ^ j) * z 0 / ε := by
  simp [seeleyCutoffCLM, div_eq_inv_mul, mul_assoc]

/-- Spatial cutoff `z ↦ χ(-2^j z₀ / ε)`. -/
def seeleyCutoffOnSpace (j : ℕ) (ε : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun z => seeleyCutoff (seeleyCutoffCLM (n := n) j ε z)

lemma seeleyCutoffOnSpace_eq (j : ℕ) (ε : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    seeleyCutoffOnSpace (n := n) j ε z =
      seeleyCutoff (-((2 : ℝ) ^ j) * z 0 / ε) := by
  simp [seeleyCutoffOnSpace, seeleyCutoffCLM_apply]

/-- Closed lower half-ball used as the domain of the Seeley series. -/
def seeleyLowerHalfBall (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  closedBall x (d / 4) ∩ closedLowerHalfSpace (n := n)

lemma isClosed_seeleyLowerHalfBall (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    IsClosed (seeleyLowerHalfBall (n := n) x d) :=
  isClosed_closedBall.inter isClosed_closedLowerHalfSpace

lemma convex_seeleyLowerHalfBall (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) :
    Convex ℝ (seeleyLowerHalfBall (n := n) x d) :=
  (convex_closedBall x (d / 4)).inter convex_closedLowerHalfSpace

/-- The closed region on which the `j`-th cutoff may be nonzero. -/
def seeleyTermSupport (j : ℕ) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z : EuclideanSpace ℝ (Fin n) | seeleyCutoffCLM (n := n) j ε z ≤ 2}

lemma isClosed_seeleyTermSupport (j : ℕ) (ε : ℝ) :
    IsClosed (seeleyTermSupport (n := n) j ε) :=
  isClosed_Iic.preimage (seeleyCutoffCLM (n := n) j ε).continuous

lemma convex_seeleyTermSupport (j : ℕ) (ε : ℝ) :
    Convex ℝ (seeleyTermSupport (n := n) j ε) := by
  apply convex_halfSpace_le
  refine ⟨?_, ?_⟩
  · intro x y; simp [seeleyCutoffCLM, mul_add]
  · intro c x; simp [seeleyCutoffCLM, smul_eq_mul, mul_left_comm]

/-- The closed region on which the `j`-th cutoff vanishes identically. -/
def seeleyTermZero (j : ℕ) (ε : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {z : EuclideanSpace ℝ (Fin n) | 2 ≤ seeleyCutoffCLM (n := n) j ε z}

lemma isClosed_seeleyTermZero (j : ℕ) (ε : ℝ) :
    IsClosed (seeleyTermZero (n := n) j ε) :=
  isClosed_Ici.preimage (seeleyCutoffCLM (n := n) j ε).continuous

lemma seeleyCutoffOnSpace_eq_zero_of_mem_zero {j : ℕ} {ε : ℝ}
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ seeleyTermZero (n := n) j ε) :
    seeleyCutoffOnSpace (n := n) j ε z = 0 :=
  seeleyCutoff_eq_zero hz

lemma seeleyCutoffOnSpace_eq_one_of_le {j : ℕ} {ε : ℝ}
    {z : EuclideanSpace ℝ (Fin n)} (hz : seeleyCutoffCLM (n := n) j ε z ≤ 1) :
    seeleyCutoffOnSpace (n := n) j ε z = 1 :=
  seeleyCutoff_eq_one hz

lemma seeleyTermSupport_union_zero (j : ℕ) (ε : ℝ) :
    seeleyTermSupport (n := n) j ε ∪ seeleyTermZero (n := n) j ε = univ := by
  ext z
  simp [seeleyTermSupport, seeleyTermZero, le_total]

omit [NeZero n] in
lemma norm_apply_le_euclidean (z : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    |z i| ≤ ‖z‖ := by
  simpa [Real.norm_eq_abs] using PiLp.norm_apply_le z i

lemma opNorm_proj_le_one :
    ‖(EuclideanSpace.proj (0 : Fin n) : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => by
    simpa using norm_apply_le_euclidean (n := n) z 0

lemma opNorm_seeleyCutoffCLM_le (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ‖seeleyCutoffCLM (n := n) j ε‖ ≤ (2 : ℝ) ^ j / ε := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have harg : seeleyCutoffCLM (n := n) j ε z = (-((2 : ℝ) ^ j) / ε) * z 0 := by
    simp [seeleyCutoffCLM]
  rw [harg, norm_mul, Real.norm_eq_abs, abs_div, abs_neg,
    abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j), abs_of_pos hε]
  gcongr
  simpa [Real.norm_eq_abs] using norm_apply_le_euclidean (n := n) z 0

omit [NeZero n] in
lemma euclidean_norm_sq (z : EuclideanSpace ℝ (Fin n)) :
    ‖z‖ ^ 2 = ∑ i : Fin n, z i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, starRingEnd_apply, sq]

lemma seeleyReflectionMap_apply_of_ne {j : ℕ} {z : EuclideanSpace ℝ (Fin n)}
    {i : Fin n} (hi : i ≠ 0) :
    seeleyReflectionMap j z i = z i := by
  simp [seeleyReflectionMap_apply, normalProjection, tangentialProjection,
    EuclideanSpace.single, hi]

lemma opNorm_normalProjection_le :
    ‖normalProjection (n := n)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => by
    simp only [normalProjection_apply, norm_smul, PiLp.norm_single, Real.norm_eq_abs, norm_one,
      mul_one]
    rw [one_mul]
    exact norm_apply_le_euclidean (n := n) z 0

lemma opNorm_tangentialProjection_le :
    ‖tangentialProjection (n := n)‖ ≤ 2 := by
  have hsub : tangentialProjection (n := n) =
      ContinuousLinearMap.id ℝ _ - normalProjection := rfl
  rw [hsub]
  calc
    ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)) - normalProjection‖
        ≤ ‖ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ +
            ‖normalProjection (n := n)‖ :=
          norm_sub_le _ _
    _ ≤ 1 + 1 := by
          gcongr
          · exact ContinuousLinearMap.norm_id_le
          · exact opNorm_normalProjection_le (n := n)
    _ = 2 := by norm_num

lemma opNorm_seeleyReflectionMap_le (j : ℕ) :
    ‖seeleyReflectionMap (n := n) j‖ ≤ (2 : ℝ) ^ j + 2 := by
  calc
    ‖seeleyReflectionMap (n := n) j‖
        ≤ ‖seeleyNode j • normalProjection (n := n)‖ + ‖tangentialProjection (n := n)‖ :=
          norm_add_le _ _
    _ ≤ ‖seeleyNode j‖ * ‖normalProjection (n := n)‖ + 2 := by
          gcongr
          · exact ContinuousLinearMap.opNorm_smul_le _ _
          · exact opNorm_tangentialProjection_le (n := n)
    _ ≤ (2 : ℝ) ^ j * 1 + 2 := by
          have : ‖seeleyNode j‖ = (2 : ℝ) ^ j := by simp [seeleyNode]
          rw [this]
          gcongr
          exact opNorm_normalProjection_le (n := n)
    _ = (2 : ℝ) ^ j + 2 := by ring

lemma opNorm_seeleyReflectionMap_le_two_pow_succ (j : ℕ) :
    ‖seeleyReflectionMap (n := n) j‖ ≤ (2 : ℝ) ^ (j + 2) := by
  have h := opNorm_seeleyReflectionMap_le (n := n) j
  have : (2 : ℝ) ^ j + 2 ≤ (2 : ℝ) ^ (j + 2) := by
    have hj : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hpow : (2 : ℝ) ^ (j + 2) = 4 * (2 : ℝ) ^ j := by
      rw [pow_add]; ring
    nlinarith
  exact h.trans this

/-- On the cutoff support inside the lower half-ball, every reflected sample lands in the
original closed upper slice. -/
lemma seeleyReflectionMap_mem_closedBall
    {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x z : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    (hzT : z ∈ seeleyLowerHalfBall (n := n) x d)
    {j : ℕ} (hsupp : z ∈ seeleyTermSupport (n := n) j ε) :
    seeleyReflectionMap j z ∈ closedBall x d ∩ closedUpperHalfSpace (n := n) := by
  have hzball : dist z x ≤ d / 4 := hzT.1
  have hzlow : z 0 ≤ 0 := hzT.2
  have harg : -((2 : ℝ) ^ j) * z 0 / ε ≤ 2 := by
    simpa [seeleyTermSupport, seeleyCutoffCLM_apply] using hsupp
  have hnorm : (2 : ℝ) ^ j * (-z 0) ≤ 2 * ε := by
    have := (div_le_iff₀ hε).1 harg
    linarith
  have hz0refl : 0 ≤ seeleyReflectionMap j z 0 := by
    rw [seeleyReflectionMap_apply_zero, seeleyNode]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]
  have hR0 : |seeleyReflectionMap j z 0 - x 0| = (2 : ℝ) ^ j * (-z 0) := by
    rw [seeleyReflectionMap_apply_zero, hx0, sub_zero, seeleyNode, abs_mul, abs_neg,
      abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) j), abs_of_nonpos hzlow]
  have hsq :
      ‖seeleyReflectionMap j z - x‖ ^ 2 =
        (seeleyReflectionMap j z 0 - x 0) ^ 2 +
          ∑ i ∈ Finset.univ.erase (0 : Fin n), (z i - x i) ^ 2 := by
    rw [euclidean_norm_sq, ← Finset.add_sum_erase _
      (fun i => (seeleyReflectionMap j z - x) i ^ 2) (Finset.mem_univ (0 : Fin n))]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi0 : i ≠ 0 := (Finset.mem_erase.mp hi).1
    simp [seeleyReflectionMap_apply_of_ne hi0]
  have htle :
      ∑ i ∈ Finset.univ.erase (0 : Fin n), (z i - x i) ^ 2 ≤ ‖z - x‖ ^ 2 := by
    rw [euclidean_norm_sq (z - x),
      ← Finset.add_sum_erase _ (fun i => (z - x) i ^ 2) (Finset.mem_univ (0 : Fin n))]
    have hpt : ∀ i, (z - x) i = z i - x i := fun i => by simp
    simp [hpt]
    nlinarith [sq_nonneg (z 0 - x 0)]
  have hnle : |seeleyReflectionMap j z 0 - x 0| ≤ 2 * ε := by
    simpa [hR0] using hnorm
  have hdist : ‖seeleyReflectionMap j z - x‖ ^ 2 ≤ (2 * ε) ^ 2 + (d / 4) ^ 2 := by
    have hzdist : ‖z - x‖ ≤ d / 4 := by simpa [dist_eq_norm] using hzball
    have hsqz : ‖z - x‖ ^ 2 ≤ (d / 4) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hzdist 2
    have hsqn : (seeleyReflectionMap j z 0 - x 0) ^ 2 ≤ (2 * ε) ^ 2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hnle 2
    calc
      ‖seeleyReflectionMap j z - x‖ ^ 2
          = (seeleyReflectionMap j z 0 - x 0) ^ 2 +
              ∑ i ∈ Finset.univ.erase (0 : Fin n), (z i - x i) ^ 2 := hsq
      _ ≤ (2 * ε) ^ 2 + ‖z - x‖ ^ 2 := by
            gcongr
      _ ≤ (2 * ε) ^ 2 + (d / 4) ^ 2 := by gcongr
  have : ‖seeleyReflectionMap j z - x‖ ≤ d := by
    have hnonneg : 0 ≤ ‖seeleyReflectionMap j z - x‖ := norm_nonneg _
    nlinarith [hdist, hεd]
  exact ⟨by simpa [dist_eq_norm] using this, hz0refl⟩

/-! ## Cutoff derivatives: vanishing off `(1,2)` and a uniform bound -/

lemma seeleyCutoff_eqOn_one : EqOn seeleyCutoff (fun _ => (1 : ℝ)) (Iic 1) :=
  fun _ ht => seeleyCutoff_eq_one ht

lemma seeleyCutoff_eqOn_zero : EqOn seeleyCutoff (fun _ => (0 : ℝ)) (Ici 2) :=
  fun _ ht => seeleyCutoff_eq_zero ht

lemma seeleyCutoff_iteratedDeriv_eq_zero_of_lt_one {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t < 1) :
    iteratedDeriv m seeleyCutoff t = 0 := by
  have h : seeleyCutoff =ᶠ[𝓝 t] fun _ : ℝ => (1 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact seeleyCutoff_eq_one (le_of_lt hs)
  have hF := (h.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
  have hconst : iteratedDeriv m (fun _ : ℝ => (1 : ℝ)) t = 0 := by
    rw [iteratedDeriv_const]
    simp [show m ≠ 0 from (Nat.pos_iff_ne_zero.mp hm)]
  simpa [iteratedDeriv, hF] using hconst

lemma seeleyCutoff_iteratedDeriv_eq_zero_of_gt_two {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 2 < t) :
    iteratedDeriv m seeleyCutoff t = 0 := by
  have h : seeleyCutoff =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact seeleyCutoff_eq_zero (le_of_lt hs)
  have hF := (h.iteratedFDeriv (𝕜 := ℝ) m).eq_of_nhds
  have hconst : iteratedDeriv m (fun _ : ℝ => (0 : ℝ)) t = 0 := iteratedDeriv_fun_const_zero
  simpa [iteratedDeriv, hF] using hconst

lemma seeleyCutoff_contDiff_infty : ContDiff ℝ ∞ seeleyCutoff :=
  seeleyCutoff_contDiff

lemma seeleyCutoff_iteratedDeriv_eq_zero_of_le_one {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : t ≤ 1) :
    iteratedDeriv m seeleyCutoff t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact seeleyCutoff_iteratedDeriv_eq_zero_of_lt_one hm ht
  · have hc : Continuous (iteratedDeriv m seeleyCutoff) :=
      (seeleyCutoff_contDiff (m := m)).continuous_iteratedDeriv m le_rfl
    have hlim : Tendsto (iteratedDeriv m seeleyCutoff) (𝓝[<] 1) (𝓝 0) := by
      apply tendsto_nhdsWithin_congr
        (fun t' ht' => (seeleyCutoff_iteratedDeriv_eq_zero_of_lt_one hm ht').symm)
      exact tendsto_const_nhds
    have hval : Tendsto (iteratedDeriv m seeleyCutoff) (𝓝[<] 1)
        (𝓝 (iteratedDeriv m seeleyCutoff 1)) :=
      (hc.tendsto 1).mono_left inf_le_left
    exact tendsto_nhds_unique hval hlim

lemma seeleyCutoff_iteratedDeriv_eq_zero_of_ge_two {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 2 ≤ t) :
    iteratedDeriv m seeleyCutoff t = 0 := by
  rcases lt_or_eq_of_le ht with ht | rfl
  · exact seeleyCutoff_iteratedDeriv_eq_zero_of_gt_two hm ht
  · have hc : Continuous (iteratedDeriv m seeleyCutoff) :=
      (seeleyCutoff_contDiff (m := m)).continuous_iteratedDeriv m le_rfl
    have hlim : Tendsto (iteratedDeriv m seeleyCutoff) (𝓝[>] 2) (𝓝 0) := by
      apply tendsto_nhdsWithin_congr
        (fun t' ht' => (seeleyCutoff_iteratedDeriv_eq_zero_of_gt_two hm ht').symm)
      exact tendsto_const_nhds
    have hval : Tendsto (iteratedDeriv m seeleyCutoff) (𝓝[>] 2)
        (𝓝 (iteratedDeriv m seeleyCutoff 2)) :=
      (hc.tendsto 2).mono_left inf_le_left
    exact tendsto_nhds_unique hval hlim

/-- Every iterated derivative of the cutoff is globally bounded. -/
lemma seeleyCutoff_iteratedDeriv_bounded (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |iteratedDeriv m seeleyCutoff t| ≤ C := by
  have hc : Continuous (iteratedDeriv m seeleyCutoff) :=
    (seeleyCutoff_contDiff (m := m)).continuous_iteratedDeriv m le_rfl
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, zero_le_one, fun t => ?_⟩
    have h01 : 0 ≤ seeleyCutoff t := seeleyCutoff_nonneg t
    have hle : seeleyCutoff t ≤ 1 := seeleyCutoff_le_one t
    simpa [iteratedDeriv_zero, abs_of_nonneg h01] using hle
  · obtain ⟨b, hb⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨b, (norm_nonneg (iteratedDeriv m seeleyCutoff 1)).trans
      (hb 1 ⟨le_rfl, by norm_num⟩), fun t => ?_⟩
    by_cases ht : t ∈ Icc (1 : ℝ) 2
    · exact hb t ht
    · have : iteratedDeriv m seeleyCutoff t = 0 := by
        rw [mem_Icc, not_and_or, not_le, not_le] at ht
        rcases ht with ht1 | ht2
        · exact seeleyCutoff_iteratedDeriv_eq_zero_of_lt_one hm ht1
        · exact seeleyCutoff_iteratedDeriv_eq_zero_of_gt_two hm ht2
      simpa [this] using (norm_nonneg (iteratedDeriv m seeleyCutoff 1)).trans
        (hb 1 ⟨le_rfl, by norm_num⟩)

/-! ## Zero Taylor field and cutoff-on-space Taylor field -/

lemma hasFTaylorSeriesUpToOn_zero
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) (∞ : ℕ∞ω)
      (fun _ : EuclideanSpace ℝ (Fin n) => (0 : F))
      (fun _ (_ : ℕ) =>
        (0 : ContinuousMultilinearMap ℝ
          (fun _ : Fin _ => EuclideanSpace ℝ (Fin n)) F)) s where
  zero_eq := by intro x hx; simp
  fderivWithin := by
    intro m hm x hx
    change HasFDerivWithinAt
      (fun _ : EuclideanSpace ℝ (Fin n) =>
        (0 : EuclideanSpace ℝ (Fin n) [×m]→L[ℝ] F))
      0 s x
    exact hasFDerivWithinAt_const (𝕜 := ℝ)
      (c := (0 : EuclideanSpace ℝ (Fin n) [×m]→L[ℝ] F)) x s
  cont := fun _ _ => continuousOn_const

lemma seeleyCutoffOnSpace_hasFTaylorSeriesUpToOn (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    HasFTaylorSeriesUpToOn ∞ (seeleyCutoffOnSpace (n := n) j ε)
      (fun z m =>
        (ftaylorSeries ℝ seeleyCutoff (seeleyCutoffCLM (n := n) j ε z) m).compContinuousLinearMap
          fun _ => seeleyCutoffCLM (n := n) j ε)
      univ := by
  have hχ : HasFTaylorSeriesUpTo ∞ seeleyCutoff (ftaylorSeries ℝ seeleyCutoff) :=
    seeleyCutoff_contDiff_infty.ftaylorSeries
  exact (hχ.hasFTaylorSeriesUpToOn univ).compContinuousLinearMap
    (seeleyCutoffCLM (n := n) j ε)

/-! ## Parameterized cutoff-weighted terms -/

/-- Seeley summand with a general coefficient sequence. -/
def seeleyTermWith (a : ℕ → ℝ) (j : ℕ) (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → F) (z : EuclideanSpace ℝ (Fin n)) : F :=
  a j • seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z)

lemma seeleyTermWith_eq_seeleyTerm (j : ℕ) (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → F) (z : EuclideanSpace ℝ (Fin n)) :
    seeleyTermWith seeleyCoeff j ε f z = seeleyTerm j ε f z := by
  simp [seeleyTermWith, seeleyTerm, seeleyCutoffOnSpace_eq]

lemma seeleyTermWith_eq_zero_of_mem_zero (a : ℕ → ℝ) {j : ℕ} {ε : ℝ}
    (f : EuclideanSpace ℝ (Fin n) → F) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ seeleyTermZero (n := n) j ε) :
    seeleyTermWith a j ε f z = 0 := by
  simp [seeleyTermWith, seeleyCutoffOnSpace_eq_zero_of_mem_zero hz]

/-! ## Unique differentiability of the support slice -/

lemma uniqueDiffOn_lower_inter_support
    {x : EuclideanSpace ℝ (Fin n)} {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    (hx0 : x 0 = 0) (j : ℕ) :
    UniqueDiffOn ℝ
      (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε) := by
  apply uniqueDiffOn_convex
    ((convex_seeleyLowerHalfBall (n := n) x d).inter (convex_seeleyTermSupport (n := n) j ε))
  let δ : ℝ := min (d / 8) (ε / (2 : ℝ) ^ (j + 1))
  have hδ : 0 < δ :=
    lt_min (by linarith) (div_pos hε (pow_pos (by norm_num : (0 : ℝ) < 2) _))
  let y : EuclideanSpace ℝ (Fin n) := x - δ • EuclideanSpace.single 0 (1 : ℝ)
  have hy0 : y 0 = -δ := by
    simp [y, hx0]
  have hyball : y ∈ ball x (d / 4) := by
    rw [mem_ball, dist_eq_norm]
    simp [y, norm_smul, PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hδ]
    have : δ ≤ d / 8 := min_le_left _ _
    linarith
  have hylow : y 0 < 0 := by
    simpa [hy0] using neg_lt_zero.2 hδ
  have hyarg : seeleyCutoffCLM (n := n) j ε y < 2 := by
    rw [seeleyCutoffCLM_apply, hy0]
    have hrew : -((2 : ℝ) ^ j) * (-δ) / ε = (2 : ℝ) ^ j * δ / ε := by ring
    rw [hrew]
    have hδε : δ ≤ ε / (2 : ℝ) ^ (j + 1) := min_le_right _ _
    have hle : (2 : ℝ) ^ j * δ / ε ≤ 1 / 2 := by
      have hmul : (2 : ℝ) ^ j * δ ≤ (2 : ℝ) ^ j * (ε / (2 : ℝ) ^ (j + 1)) := by
        gcongr
      have heq : (2 : ℝ) ^ j * (ε / (2 : ℝ) ^ (j + 1)) = ε / 2 := by
        rw [pow_succ]
        field_simp
      rw [div_le_iff₀ hε]
      nlinarith [hmul, heq, hε]
    linarith
  let U : Set (EuclideanSpace ℝ (Fin n)) :=
    ball x (d / 4) ∩ {z | z 0 < 0} ∩ {z | seeleyCutoffCLM (n := n) j ε z < 2}
  have hUopen : IsOpen U :=
    (isOpen_ball.inter
      (isOpen_Iio.preimage (EuclideanSpace.proj (0 : Fin n)).continuous)).inter
      (isOpen_Iio.preimage (seeleyCutoffCLM (n := n) j ε).continuous)
  have hUsub : U ⊆ seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε := by
    intro z hz
    have hzball : z ∈ closedBall x (d / 4) := ball_subset_closedBall hz.1.1
    have hzlow : z 0 ≤ 0 := le_of_lt hz.1.2
    have hzχ : seeleyCutoffCLM (n := n) j ε z ≤ 2 := le_of_lt hz.2
    exact ⟨⟨hzball, hzlow⟩, hzχ⟩
  exact ⟨y, mem_interior.2 ⟨U, hUsub, hUopen, ⟨⟨hyball, hylow⟩, hyarg⟩⟩⟩

/-- Leibniz Taylor field of one cutoff-weighted reflected term on its support slice. -/
lemma seeleyTermWith_hasFTaylorSeriesUpToOn_support
    (a : ℕ → ℝ) (j : ℕ) {d ε : ℝ} (hd : 0 < d) (hε : 0 < ε)
    {x : EuclideanSpace ℝ (Fin n)} (hx0 : x 0 = 0)
    (hεd : (d / 4) ^ 2 + (2 * ε) ^ 2 ≤ d ^ 2)
    {f : EuclideanSpace ℝ (Fin n) → F}
    {p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F}
    (hp : HasFTaylorSeriesUpToOn ∞ f p
      (closedBall x d ∩ closedUpperHalfSpace (n := n))) :
    HasFTaylorSeriesUpToOn ∞
      (fun z => seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z))
      (fun z =>
        (ftaylorSeries ℝ (fun q : ℝ × F => q.1 • q.2)
          (seeleyCutoffOnSpace (n := n) j ε z,
            f (seeleyReflectionMap j z))).taylorComp
          (fun k =>
            ((ftaylorSeries ℝ seeleyCutoff
                (seeleyCutoffCLM (n := n) j ε z) k).compContinuousLinearMap
                fun _ => seeleyCutoffCLM (n := n) j ε).prod
              ((p (seeleyReflectionMap j z) k).compContinuousLinearMap
                fun _ => seeleyReflectionMap (n := n) j)))
      (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε) := by
  have hsupp :
      seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε ⊆
        seeleyReflectionMap j ⁻¹' (closedBall x d ∩ closedUpperHalfSpace (n := n)) := by
    intro z hz
    exact seeleyReflectionMap_mem_closedBall hd hε hx0 hεd hz.1 hz.2
  have hfR :=
    (hp.compContinuousLinearMap (seeleyReflectionMap (n := n) j)).mono hsupp
  have hχ :=
    (seeleyCutoffOnSpace_hasFTaylorSeriesUpToOn (n := n) j hε).mono
      (subset_univ
        (s := seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε))
  have hsmul :
      HasFTaylorSeriesUpToOn ∞ (fun q : ℝ × F => q.1 • q.2)
        (ftaylorSeries ℝ (fun q : ℝ × F => q.1 • q.2)) univ :=
    (contDiff_smul (n := ∞) (𝕜 := ℝ) (𝕜' := ℝ)).ftaylorSeries.hasFTaylorSeriesUpToOn univ
  exact hsmul.comp (hχ.prodMk hfR) (fun _ _ => mem_univ _)

/-- The `j`-th cutoff-weighted term, as a function of the closed lower half-ball, agrees with
the Leibniz product on the support and with `0` on the vanishing region. -/
lemma seeleyTermWith_eqOn_support (a : ℕ → ℝ) (j : ℕ) (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → F) :
    EqOn (seeleyTermWith a j ε f)
      (fun z => a j • seeleyCutoffOnSpace (n := n) j ε z • f (seeleyReflectionMap j z))
      (seeleyTermSupport (n := n) j ε) := fun _ _ => rfl

lemma seeleyTermWith_eqOn_zero_slice (a : ℕ → ℝ) (j : ℕ) (ε : ℝ)
    (f : EuclideanSpace ℝ (Fin n) → F)
    {x : EuclideanSpace ℝ (Fin n)} {d : ℝ} :
    EqOn (seeleyTermWith a j ε f) (fun _ => 0)
      (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermZero (n := n) j ε) :=
  fun z hz => seeleyTermWith_eq_zero_of_mem_zero a f hz.2

/-- Cover of the lower half-ball by the `j`-th support and vanishing slices. -/
lemma seeleyLowerHalfBall_eq_support_union_zero
    (x : EuclideanSpace ℝ (Fin n)) (d : ℝ) (j : ℕ) (ε : ℝ) :
    seeleyLowerHalfBall (n := n) x d =
      (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermSupport (n := n) j ε) ∪
        (seeleyLowerHalfBall (n := n) x d ∩ seeleyTermZero (n := n) j ε) := by
  rw [← inter_union_distrib_left, seeleyTermSupport_union_zero, inter_univ]

/-- Parameterized scalar hypotheses used by the series/gluing theorem. These are the
two identities owned by `SeeleyMoments` for the concrete coefficients `seeleyCoeff`. -/
def SeeleyCoeffSummable (a : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, Summable fun j : ℕ => |a j| * (2 : ℝ) ^ (j * m)

def SeeleyMomentIdentities (a : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, HasSum (fun j : ℕ => a j * seeleyNode j ^ m) 1

end LeeSmooth.SeeleyExtension
