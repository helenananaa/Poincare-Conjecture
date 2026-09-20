/-
This module bridges the Brouwer simplex fixed-point theorem copied from
math-xmum/Brouwer at commit 7556f9adcc89f81aa758ddeff4f0dcfeb2d99cda.
The copied proof is distributed under the MIT license in `BROUWER_LICENSE`.

The bridge itself transports the simplex theorem to closed unit balls.  It is
kept in the same external directory so that the provenance boundary remains
explicit.
-/

import LeeSmoothLib.External.Brouwer.Brouwer

open Classical
open Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace LeeSmooth.External.Brouwer

/-- Radial clipping to the closed unit ball. -/
def radialClip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (x : V) : V :=
  (max 1 ‖x‖)⁻¹ • x

lemma continuous_radialClip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Continuous (radialClip : V → V) := by
  unfold radialClip
  apply Continuous.smul
  · exact (continuous_const.max continuous_norm).inv₀ fun x ↦ by
      exact ne_of_gt (zero_lt_one.trans_le (le_max_left 1 ‖x‖))
  · exact continuous_id

lemma radialClip_mem_closedBall {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (x : V) : radialClip x ∈ closedBall (0 : V) 1 := by
  rw [mem_closedBall_zero_iff]
  rw [radialClip, norm_smul_of_nonneg]
  · exact inv_mul_le_one_of_le₀ (le_max_right 1 ‖x‖)
      (zero_le_one.trans (le_max_left 1 ‖x‖))
  · exact inv_nonneg.mpr (zero_le_one.trans (le_max_left 1 ‖x‖))

lemma radialClip_eq_self {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {x : V} (hx : x ∈ closedBall (0 : V) 1) : radialClip x = x := by
  rw [mem_closedBall_zero_iff] at hx
  simp [radialClip, max_eq_left hx]

private abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

private def simplexEncode (n : ℕ) (hn : 0 < n)
    (x : closedBall (0 : Euc n) 1) : stdSimplex ℝ (Fin (n + 1)) := by
  let d : ℝ := 2 * (n : ℝ)
  let q : Fin n → ℝ := fun i ↦ (x.1 i + 1) / d
  have hd : 0 < d := by positivity
  have hxcoord : ∀ i, -1 ≤ x.1 i ∧ x.1 i ≤ 1 := by
    intro i
    have hi : |x.1 i| ≤ 1 := by
      calc
        |x.1 i| = ‖x.1 i‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖x.1‖ := PiLp.norm_apply_le x.1 i
        _ ≤ 1 := mem_closedBall_zero_iff.mp x.2
    exact (abs_le.mp hi)
  have hq_nonneg : ∀ i, 0 ≤ q i := by
    intro i
    exact div_nonneg (by linarith [(hxcoord i).1]) hd.le
  have hsumx : ∑ i, x.1 i ≤ (n : ℝ) := by
    calc
      ∑ i, x.1 i ≤ ∑ _i : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ ↦ (hxcoord i).2
      _ = (n : ℝ) := by simp
  have hsumq : ∑ i, q i ≤ 1 := by
    dsimp [q, d]
    rw [← Finset.sum_div]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [div_le_iff₀ hd]
    linarith
  exact ⟨Fin.snoc q (1 - ∑ i, q i), by
    constructor
    · intro i
      refine Fin.lastCases (by simpa using sub_nonneg.mpr hsumq) (fun j ↦ ?_) i
      simpa using hq_nonneg j
    · simp [Fin.sum_univ_castSucc]⟩

private def simplexDecode (n : ℕ) (y : stdSimplex ℝ (Fin (n + 1))) : Euc n :=
  WithLp.toLp 2 fun i ↦ 2 * (n : ℝ) * y.1 i.castSucc - 1

private lemma continuous_simplexEncode (n : ℕ) (hn : 0 < n) :
    Continuous (simplexEncode n hn) := by
  apply Continuous.subtype_mk
  apply Continuous.finSnoc
  · fun_prop
  · fun_prop

private lemma continuous_simplexDecode (n : ℕ) : Continuous (simplexDecode n) := by
  unfold simplexDecode
  apply (PiLp.continuous_toLp (2 : ℝ≥0∞) (fun _ : Fin n ↦ ℝ)).comp
  exact continuous_pi fun i ↦
    (continuous_const.mul ((continuous_apply i.castSucc).comp continuous_subtype_val)).sub
      continuous_const

private lemma simplexDecode_encode (n : ℕ) (hn : 0 < n)
    (x : closedBall (0 : Euc n) 1) : simplexDecode n (simplexEncode n hn x) = x.1 := by
  ext i
  simp only [simplexDecode, simplexEncode, PiLp.toLp_apply, Fin.snoc_castSucc]
  field_simp
  ring

private theorem closedBall_fixedPoint_euclidean (n : ℕ) (hn : 0 < n) (f : Euc n → Euc n)
    (hf : ContinuousOn f (closedBall 0 1))
    (hmap : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : Euc n) 1, f x = x := by
  let ballMap : closedBall (0 : Euc n) 1 → closedBall (0 : Euc n) 1 :=
    hmap.restrict f (closedBall 0 1) (closedBall 0 1)
  have hballMap : Continuous ballMap := hf.mapsToRestrict hmap

  let retractToBall : stdSimplex ℝ (Fin (n + 1)) → closedBall (0 : Euc n) 1 :=
    fun y ↦ ⟨radialClip (simplexDecode n y), radialClip_mem_closedBall _⟩
  have hretract : Continuous retractToBall := by
    apply Continuous.subtype_mk
    exact continuous_radialClip.comp (continuous_simplexDecode n)

  let simplexMap : stdSimplex ℝ (Fin (n + 1)) → stdSimplex ℝ (Fin (n + 1)) :=
    fun y ↦ simplexEncode n hn (ballMap (retractToBall y))
  have hsimplexMap : Continuous simplexMap :=
    (continuous_simplexEncode n hn).comp (hballMap.comp hretract)

  let p : PNat := ⟨n + 1, Nat.succ_pos n⟩
  obtain ⟨y, hy⟩ := _root_.Brouwer (n := p) simplexMap hsimplexMap
  let x : closedBall (0 : Euc n) 1 := retractToBall y
  have hdecode : f x.1 = simplexDecode n y := by
    have h := congrArg (simplexDecode n) hy
    change simplexDecode n (simplexEncode n hn (ballMap x)) = simplexDecode n y at h
    simpa only [simplexDecode_encode, ballMap, MapsTo.val_restrict_apply] using h
  have hdecode_mem : simplexDecode n y ∈ closedBall (0 : Euc n) 1 := by
    rw [← hdecode]
    exact hmap x.2
  refine ⟨x.1, x.2, ?_⟩
  change f x.1 = radialClip (simplexDecode n y)
  exact hdecode.trans (radialClip_eq_self hdecode_mem).symm

/--
Brouwer fixed-point theorem for the closed unit ball of a finite-dimensional real
inner-product space, transported from the genuine standard-simplex proof.
-/
theorem closedBall_fixedPoint
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → E)
    (hf : ContinuousOn f (closedBall 0 1))
    (hmap : MapsTo f (closedBall 0 1) (closedBall 0 1)) :
    ∃ x ∈ closedBall (0 : E) 1, f x = x := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have hzero : ∀ x : E, x = 0 := finrank_zero_iff_forall_zero.mp hdim
    exact ⟨0, by simp, hzero (f 0)⟩
  · let b := (stdOrthonormalBasis ℝ E).repr
    let g : Euc (Module.finrank ℝ E) → Euc (Module.finrank ℝ E) :=
      fun z ↦ b (f (b.symm z))
    have hsymm_map : MapsTo b.symm (closedBall 0 1) (closedBall 0 1) := by
      intro z hz
      simpa only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map] using hz
    have hg : ContinuousOn g (closedBall 0 1) := by
      exact b.continuous.comp_continuousOn'
        (hf.comp' b.symm.continuous.continuousOn hsymm_map)
    have hgmap : MapsTo g (closedBall 0 1) (closedBall 0 1) := by
      intro z hz
      change b (f (b.symm z)) ∈ closedBall 0 1
      simp only [mem_closedBall_zero_iff, LinearIsometryEquiv.norm_map]
      exact mem_closedBall_zero_iff.mp (hmap (hsymm_map hz))
    obtain ⟨z, hz, hfix⟩ := closedBall_fixedPoint_euclidean
      (Module.finrank ℝ E) (Nat.pos_of_ne_zero hdim) g hg hgmap
    refine ⟨b.symm z, hsymm_map hz, ?_⟩
    apply b.injective
    simpa [g] using hfix

end LeeSmooth.External.Brouwer
