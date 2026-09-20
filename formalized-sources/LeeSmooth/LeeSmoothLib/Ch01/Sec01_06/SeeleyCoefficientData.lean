import LeeSmoothLib.Ch01.Sec01_06.SeeleyExtension

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecificLimits.Basic

/-! Verified coefficient and cutoff data only. No infinite extension theorem is assumed. -/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace LeeSmooth.SeeleyExtension

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## Geometric Seeley nodes and finite Lagrange coefficients -/

/-- Geometric interpolation nodes `-2^j`. -/
def seeleyNode (j : ℕ) : ℝ := -((2 : ℝ) ^ j)

lemma seeleyNode_lt_zero (j : ℕ) : seeleyNode j < 0 := by
  simp [seeleyNode]

lemma seeleyNode_injective : Function.Injective seeleyNode := by
  intro i j hij
  simp only [seeleyNode, neg_inj] at hij
  have hijN : (2 : ℕ) ^ i = (2 : ℕ) ^ j := by exact_mod_cast hij
  exact Nat.pow_right_injective Nat.one_lt_two hijN

lemma seeleyNode_fin_injective (N : ℕ) :
    Function.Injective (fun j : Fin N ↦ seeleyNode (j : ℕ)) :=
  seeleyNode_injective.comp Fin.val_injective

/-- Finite Lagrange coefficients for the nodes `-2^0, …, -2^{N-1}`, evaluated at `1`. -/
def seeleyCoeffFinite (N : ℕ) (j : Fin N) : ℝ :=
  (Lagrange.basis Finset.univ (fun i : Fin N ↦ seeleyNode (i : ℕ)) j).eval 1

/-- The finite geometric interpolants match every moment of order strictly less than `N`. -/
lemma sum_seeleyCoeffFinite_mul_node_pow (N m : ℕ) (hm : m < N) :
    ∑ j : Fin N, seeleyCoeffFinite N j * seeleyNode (j : ℕ) ^ m = 1 := by
  let P : Polynomial ℝ := Polynomial.X ^ m
  have hdeg : P.degree < (Finset.univ : Finset (Fin N)).card := by
    rw [show (Finset.univ : Finset (Fin N)).card = N by simp]
    simp only [P, Polynomial.degree_X_pow]
    exact_mod_cast hm
  have hinterp := Lagrange.eq_interpolate
    (s := (Finset.univ : Finset (Fin N)))
    (v := fun i : Fin N ↦ seeleyNode (i : ℕ)) (f := P)
    (seeleyNode_fin_injective N).injOn hdeg
  have heval := congrArg (Polynomial.eval (1 : ℝ)) hinterp
  symm
  simpa [P, seeleyCoeffFinite, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, mul_comm] using heval

/-- Finite coefficients as a function of `ℕ`, vanishing for `j ≥ N`. -/
def seeleyCoeffFiniteNat (N j : ℕ) : ℝ :=
  if h : j < N then seeleyCoeffFinite N ⟨j, h⟩ else 0

lemma sum_seeleyCoeffFiniteNat_mul_node_pow (N m : ℕ) (hm : m < N) :
    ∑ j ∈ Finset.range N, seeleyCoeffFiniteNat N j * seeleyNode j ^ m = 1 := by
  have h := sum_seeleyCoeffFinite_mul_node_pow N m hm
  rw [Finset.sum_range]
  simpa [seeleyCoeffFiniteNat] using h

/-! ## Infinite tail product and Seeley coefficients -/

/-- One-step tail factor in the infinite product for the `j`-th Seeley coefficient. -/
def seeleyTailFactor (j k : ℕ) : ℝ :=
  (1 - seeleyNode (k + j + 1)) / (seeleyNode j - seeleyNode (k + j + 1))

lemma seeleyTailFactor_eq (j k : ℕ) :
    seeleyTailFactor j k =
      (1 + (2 : ℝ) ^ (k + j + 1)) / ((2 : ℝ) ^ (k + j + 1) - (2 : ℝ) ^ j) := by
  unfold seeleyTailFactor seeleyNode
  ring

lemma seeleyTailFactor_den_pos (j k : ℕ) :
    0 < (2 : ℝ) ^ (k + j + 1) - (2 : ℝ) ^ j := by
  have : (2 : ℝ) ^ j < (2 : ℝ) ^ (k + j + 1) :=
    pow_lt_pow_right₀ (by norm_num : (1 : ℝ) < 2) (by omega)
  linarith

lemma seeleyTailFactor_pos (j k : ℕ) : 0 < seeleyTailFactor j k := by
  rw [seeleyTailFactor_eq]
  have hden := seeleyTailFactor_den_pos j k
  positivity

lemma seeleyTailFactor_one_lt (j k : ℕ) : 1 < seeleyTailFactor j k := by
  rw [seeleyTailFactor_eq, lt_div_iff₀ (seeleyTailFactor_den_pos j k), one_mul]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) j]

lemma seeleyTailFactor_sub_one_eq (j k : ℕ) :
    seeleyTailFactor j k - 1 =
      (1 + (2 : ℝ) ^ j) / ((2 : ℝ) ^ (k + j + 1) - (2 : ℝ) ^ j) := by
  rw [seeleyTailFactor_eq]
  have hden := (seeleyTailFactor_den_pos j k).ne'
  rw [div_sub_one hden]
  ring

lemma seeleyTailFactor_sub_one_le (j k : ℕ) :
    seeleyTailFactor j k - 1 ≤ (2 : ℝ) * ((1 : ℝ) / 2) ^ k := by
  have hden := seeleyTailFactor_den_pos j k
  have hpowle : (2 : ℝ) ^ (k + j) ≤ (2 : ℝ) ^ (k + j + 1) - (2 : ℝ) ^ j := by
    have hsplit : (2 : ℝ) ^ (k + j + 1) - (2 : ℝ) ^ (k + j) = (2 : ℝ) ^ (k + j) := by
      rw [pow_succ]
      ring
    have : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ (k + j) :=
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_add_left _ _)
    linarith
  have hnum : 1 + (2 : ℝ) ^ j ≤ 2 * (2 : ℝ) ^ j := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  rw [seeleyTailFactor_sub_one_eq]
  calc
    (1 + (2 : ℝ) ^ j) / ((2 : ℝ) ^ (k + j + 1) - (2 : ℝ) ^ j)
        ≤ (2 * (2 : ℝ) ^ j) / ((2 : ℝ) ^ (k + j + 1) - (2 : ℝ) ^ j) := by
          gcongr
    _ ≤ (2 * (2 : ℝ) ^ j) / (2 : ℝ) ^ (k + j) := by
          gcongr
    _ = 2 / (2 : ℝ) ^ k := by
          rw [pow_add]
          field_simp
    _ = 2 * ((1 : ℝ) / 2) ^ k := by
          simp [div_eq_mul_inv, inv_pow]

lemma seeleyTailFactor_le_one_add (j k : ℕ) :
    seeleyTailFactor j k ≤ 1 + (2 : ℝ) * ((1 : ℝ) / 2) ^ k := by
  linarith [seeleyTailFactor_sub_one_le j k]

lemma summable_seeleyTailFactor_sub_one (j : ℕ) :
    Summable fun k : ℕ ↦ seeleyTailFactor j k - 1 :=
  (summable_geometric_two.mul_left (2 : ℝ)).of_nonneg_of_le
    (fun k ↦ le_of_lt (sub_pos.mpr (seeleyTailFactor_one_lt j k)))
    (fun k ↦ seeleyTailFactor_sub_one_le j k)

lemma multipliable_seeleyTailFactor (j : ℕ) : Multipliable (seeleyTailFactor j) := by
  have h := Real.multipliable_one_add_of_summable (summable_seeleyTailFactor_sub_one j)
  exact h.congr fun k ↦ by ring

/-- The `j`-th Seeley coefficient: finite Lagrange head times the convergent tail product. -/
def seeleyCoeff (j : ℕ) : ℝ :=
  seeleyCoeffFinite (j + 1) ⟨j, Nat.lt_succ_self j⟩ * ∏' k, seeleyTailFactor j k

lemma seeleyTailFactor_tprod_nonneg (j : ℕ) : 0 ≤ ∏' k, seeleyTailFactor j k := by
  have hpos : ∀ k, 0 < seeleyTailFactor j k := seeleyTailFactor_pos j
  have htend := (multipliable_seeleyTailFactor j).hasProd.tendsto_prod_nat
  have hprod : ∀ N, 0 ≤ ∏ k ∈ Finset.range N, seeleyTailFactor j k :=
    fun N ↦ Finset.prod_nonneg fun k _ ↦ (hpos k).le
  exact ge_of_tendsto htend (Eventually.of_forall hprod)

/-- Geometric finite reflection reproduces the identity moments through order `m < N`. -/
lemma seeley_weighted_multilinear (N m : ℕ) (hm : m < N)
    (M : E [×m]→L[ℝ] F) (u v : Fin m → E) :
    (∑ j : Fin N, seeleyCoeffFinite N j •
      M (fun i ↦ seeleyNode (j : ℕ) • u i + v i)) =
      M (fun i ↦ u i + v i) := by
  exact weighted_multilinear_add_eq m (fun j : Fin N ↦ seeleyCoeffFinite N j)
    (fun j ↦ seeleyNode (j : ℕ))
    (fun q hq ↦ sum_seeleyCoeffFinite_mul_node_pow N q (hq.trans_lt hm)) M u v

/-! ## Smooth cutoff identically `1` near `0` and vanishing for large positive arguments -/

/-- `seeleyCutoff t = 1` for `t ≤ 1` and `seeleyCutoff t = 0` for `t ≥ 2`. -/
def seeleyCutoff (t : ℝ) : ℝ := Real.smoothTransition (2 - t)

lemma seeleyCutoff_eq_one {t : ℝ} (ht : t ≤ 1) : seeleyCutoff t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma seeleyCutoff_eq_zero {t : ℝ} (ht : 2 ≤ t) : seeleyCutoff t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma seeleyCutoff_nonneg (t : ℝ) : 0 ≤ seeleyCutoff t :=
  Real.smoothTransition.nonneg _

lemma seeleyCutoff_le_one (t : ℝ) : seeleyCutoff t ≤ 1 :=
  Real.smoothTransition.le_one _

lemma seeleyCutoff_contDiff {m : ℕ∞} : ContDiff ℝ m seeleyCutoff :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)

lemma seeleyCutoff_eq_zero_of_large {j : ℕ} {ε t : ℝ} (hε : 0 < ε)
    (_ht : t < 0) (hj : (2 : ℝ) * ε ≤ (2 : ℝ) ^ j * (-t)) :
    seeleyCutoff (-((2 : ℝ) ^ j) * t / ε) = 0 := by
  apply seeleyCutoff_eq_zero
  have : 2 ≤ -((2 : ℝ) ^ j) * t / ε := by
    rw [le_div_iff₀ hε]
    linarith
  exact this

lemma seeleyCutoff_eq_one_of_small {j : ℕ} {ε t : ℝ} (hε : 0 < ε)
    (_ht : t ≤ 0) (hj : (2 : ℝ) ^ j * (-t) ≤ ε) :
    seeleyCutoff (-((2 : ℝ) ^ j) * t / ε) = 1 := by
  apply seeleyCutoff_eq_one
  have hε0 : 0 < ε := hε
  have : -((2 : ℝ) ^ j) * t / ε ≤ 1 := by
    rw [div_le_one hε0]
    linarith
  exact this

/-! ## Geometric reflection maps -/

variable {n : ℕ} [NeZero n]

/-- Linear map that multiplies the normal coordinate by `-2^j` and fixes the tangential plane. -/
def seeleyReflectionMap (j : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  seeleyNode j • normalProjection + tangentialProjection

lemma seeleyReflectionMap_apply (j : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    seeleyReflectionMap j z =
      seeleyNode j • normalProjection z + tangentialProjection z :=
  rfl

lemma seeleyReflectionMap_apply_zero (j : ℕ) (z : EuclideanSpace ℝ (Fin n)) :
    seeleyReflectionMap j z 0 = seeleyNode j * z 0 := by
  simp [seeleyReflectionMap, tangentialProjection, normalProjection]

lemma seeleyReflectionMap_of_normal_eq_zero (j : ℕ)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z 0 = 0) :
    seeleyReflectionMap j z = z := by
  rw [seeleyReflectionMap_apply]
  simp [normalProjection_apply, hz, tangentialProjection]

/-! ## Closed lower half-space, unique differentiability -/

def closedLowerHalfSpace : Set (EuclideanSpace ℝ (Fin n)) := {z | z 0 ≤ 0}

lemma isClosed_closedLowerHalfSpace : IsClosed (closedLowerHalfSpace (n := n)) := by
  change IsClosed ((EuclideanSpace.proj (i := (0 : Fin n))) ⁻¹' Set.Iic 0)
  exact isClosed_Iic.preimage (EuclideanSpace.proj (i := (0 : Fin n))).continuous

lemma convex_closedLowerHalfSpace : Convex ℝ (closedLowerHalfSpace (n := n)) := by
  apply convex_halfSpace_le
  exact
    { map_add := fun x y ↦ by simp
      map_smul := fun c x ↦ by simp }

lemma uniqueDiffOn_closedBall_inter_closedLowerHalfSpace
    {x : EuclideanSpace ℝ (Fin n)} {d : ℝ} (hd : 0 < d) (hx0 : x 0 = 0) :
    UniqueDiffOn ℝ (Metric.closedBall x d ∩ closedLowerHalfSpace (n := n)) := by
  apply uniqueDiffOn_convex
    ((convex_closedBall x d).inter convex_closedLowerHalfSpace)
  refine ⟨x - (d / 2) • EuclideanSpace.single 0 (1 : ℝ), ?_⟩
  rw [interior_inter, interior_closedBall x hd.ne']
  constructor
  · have hsub :
        x - (d / 2) • EuclideanSpace.single 0 (1 : ℝ) - x =
          -((d / 2) • EuclideanSpace.single 0 (1 : ℝ)) := by
      abel
    rw [Metric.mem_ball, dist_eq_norm, hsub, norm_neg, norm_smul, PiLp.norm_single]
    simp [Real.norm_eq_abs, abs_of_pos hd]
    linarith
  · rw [mem_interior]
    refine ⟨{z : EuclideanSpace ℝ (Fin n) | z 0 < 0}, ?_, ?_, ?_⟩
    · intro z hz
      change z 0 ≤ 0
      exact le_of_lt hz
    · change IsOpen ((EuclideanSpace.proj (i := (0 : Fin n))) ⁻¹' Set.Iio 0)
      exact isOpen_Iio.preimage (EuclideanSpace.proj (i := (0 : Fin n))).continuous
    · change x 0 - (d / 2) * (EuclideanSpace.single 0 (1 : ℝ)) 0 < 0
      simpa [hx0] using neg_lt_zero.2 (half_pos hd)

/-! ## Seeley terms and the lower-half series -/

variable [CompleteSpace F]

/-- One summand of the Seeley formula. -/
def seeleyTerm (j : ℕ) (ε : ℝ) (f : EuclideanSpace ℝ (Fin n) → F)
    (z : EuclideanSpace ℝ (Fin n)) : F :=
  seeleyCoeff j • seeleyCutoff (-((2 : ℝ) ^ j) * z 0 / ε) • f (seeleyReflectionMap j z)

/-- The Seeley series used on the open lower half-space. -/
def seeleyLower (ε : ℝ) (f : EuclideanSpace ℝ (Fin n) → F)
    (z : EuclideanSpace ℝ (Fin n)) : F :=
  ∑' j : ℕ, seeleyTerm j ε f z

/-- Ambient piecewise extension: original function on the closed upper half, Seeley series below. -/
def seeleyExtension (ε : ℝ) (S : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → F) : EuclideanSpace ℝ (Fin n) → F :=
  closedPiecewise S f (seeleyLower ε f)

lemma seeleyExtension_eqOn_upper (ε : ℝ) {S : Set (EuclideanSpace ℝ (Fin n))}
    (f : EuclideanSpace ℝ (Fin n) → F) :
    EqOn (seeleyExtension ε S f) f S := fun _ hz ↦ closedPiecewise_of_mem hz

/-- At a boundary point the geometric reflection maps are the identity, so every
Seeley term reduces to a scalar multiple of `f`. -/
lemma seeleyTerm_of_normal_eq_zero (j : ℕ) {ε : ℝ} (_hε : 0 < ε)
    (f : EuclideanSpace ℝ (Fin n) → F) {z : EuclideanSpace ℝ (Fin n)}
    (hz : z 0 = 0) :
    seeleyTerm j ε f z = seeleyCoeff j • f z := by
  unfold seeleyTerm
  have hχ : seeleyCutoff (-((2 : ℝ) ^ j) * z 0 / ε) = 1 := by
    rw [hz]
    simp [seeleyCutoff_eq_one]
  rw [hχ, seeleyReflectionMap_of_normal_eq_zero j hz, one_smul]

/-- Geometric finite reflection of order `N-1` as a finite Seeley combination without cutoff. -/
def geometricFiniteReflectionExtension (N : ℕ)
    (f : EuclideanSpace ℝ (Fin n) → F) : EuclideanSpace ℝ (Fin n) → F :=
  fun z ↦ ∑ j : Fin N, seeleyCoeffFinite N j • f (seeleyReflectionMap j z)

lemma geometricFiniteReflection_taylor_jet_eq (N m : ℕ) (hm : m < N)
    (p : EuclideanSpace ℝ (Fin n) →
      FormalMultilinearSeries ℝ (EuclideanSpace ℝ (Fin n)) F)
    {z : EuclideanSpace ℝ (Fin n)} (hz : z 0 = 0) :
    (∑ j : Fin N, seeleyCoeffFinite N j •
      (p (seeleyReflectionMap j z) m).compContinuousLinearMap
        (fun _ ↦ seeleyReflectionMap j)) = p z m := by
  apply ContinuousMultilinearMap.ext
  intro w
  simp_rw [ContinuousMultilinearMap.sum_apply,
    ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    seeleyReflectionMap_of_normal_eq_zero _ hz,
    seeleyReflectionMap_apply]
  convert seeley_weighted_multilinear N m hm (p z m)
    (fun i ↦ normalProjection (w i)) (fun i ↦ tangentialProjection (w i)) using 1
  exact congrArg (p z m) (funext fun i ↦ (normal_add_tangential (w i)).symm)

/-! ## The local `C^∞` extension theorem -/


end LeeSmooth.SeeleyExtension
