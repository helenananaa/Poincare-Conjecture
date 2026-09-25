import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.AffineRightInverseFixedPoint
import PoincareConjecture.ParallelImplementation.AffineInverseQuadraticGradient
import PoincareConjecture.ParallelImplementation.AffineInverseHessianNonlinearity
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.InitialBackgroundSmallness
open PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open scoped Topology BigOperators BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance standardGroup0 : NormedAddCommGroup (E3 →L[ℝ] E3) := inferInstance
local instance standardSpace0 : NormedSpace ℝ (E3 →L[ℝ] E3) := inferInstance
local instance standardGroup1 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance standardSpace1 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance standardGroup2 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace2 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup3 : NormedAddCommGroup ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace3 : NormedSpace ℝ ((E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup4 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace4 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardGroup5 : NormedAddCommGroup ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
local instance standardSpace5 : NormedSpace ℝ ((E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E3) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] (E3 →L[ℝ] E6) →L[ℝ] E6) := inferInstance
theorem exists_background_and_time_bounds
    (alpha C W : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) (hC : 0 < C) (hW : 0 ≤ W) :

    ∃ epsilon delta : ℝ, 0 < epsilon ∧ epsilon ≤ 1 ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ T : ℝ, 0 < T → T ≤ delta →
      let R : ℝ := 4*C
      let p : ℝ := 3*(T+8*T^(1-alpha/2))
      let q : ℝ := 3*Real.sqrt T+16*T^((1-alpha)/2)
      let K : ℝ := 72*epsilon+216*p*epsilon+432*p*R+
        384*W*p*(epsilon+q*R)^2+64*W*q*(epsilon+q*R)
      epsilon+p*R ≤ 1/2 ∧ C*K ≤ 1/2 ∧
        C*(1+3*epsilon+(72+32*W)*epsilon^2+K*R) ≤ R :=
/- SWARM_PROOF_BEGIN -/
by
  have hpExpPos : 0 < 1 - alpha / 2 := by linarith
  have hqExpPos : 0 < (1 - alpha) / 2 := by linarith
  have hpExp : 0 ≤ 1 - alpha / 2 := hpExpPos.le
  have hqExp : 0 ≤ (1 - alpha) / 2 := hqExpPos.le
  let D : ℝ := 72 + 32 * W
  have hDpos : 0 < D := by dsimp [D]; nlinarith [hW]
  have hDnonneg : 0 ≤ D := hDpos.le
  let B : ℝ := 12 + 576 * (C + 1) + 2 * Real.sqrt D
  have hBpos : 0 < B := by dsimp [B]; positivity
  have hB12 : 12 ≤ B := by
    dsimp [B]
    have hs : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    nlinarith [hC]
  have hBC : 576 * (C + 1) ≤ B := by
    dsimp [B]
    have hs : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    nlinarith
  have hBD : 2 * Real.sqrt D ≤ B := by
    dsimp [B]
    have hs : 0 ≤ Real.sqrt D := Real.sqrt_nonneg D
    nlinarith [hC]
  let epsilon : ℝ := 1 / B
  have hepspos : 0 < epsilon := by dsimp [epsilon]; exact one_div_pos.mpr hBpos
  have heps12 : epsilon ≤ 1 / 12 := by
    dsimp [epsilon]
    exact one_div_le_one_div_of_le (by norm_num) hB12
  have hepsC : epsilon ≤ 1 / (576 * (C + 1)) := by
    dsimp [epsilon]
    exact one_div_le_one_div_of_le (by positivity) hBC
  have hepsB : epsilon * B = 1 := by
    dsimp [epsilon]
    field_simp [ne_of_gt hBpos]
  have hscaled_nonneg : 0 ≤ (2 * Real.sqrt D) * epsilon := by positivity
  have hscaled_le : (2 * Real.sqrt D) * epsilon ≤ 1 := by
    calc
      (2 * Real.sqrt D) * epsilon ≤ B * epsilon := mul_le_mul_of_nonneg_right hBD hepspos.le
      _ = 1 := by simpa [mul_comm] using hepsB
  have hscaled_sq : ((2 * Real.sqrt D) * epsilon) ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hscaled_nonneg (by norm_num)).2 hscaled_le
  have hquad : D * epsilon ^ 2 ≤ 1 / 4 := by
    nlinarith [hscaled_sq, Real.sq_sqrt hDnonneg]
  have hCeps : C * epsilon ≤ 1 / 576 := by
    calc
      C * epsilon ≤ C * (1 / (576 * (C + 1))) :=
        mul_le_mul_of_nonneg_left hepsC hC.le
      _ = C / (576 * (C + 1)) := by ring
      _ ≤ 1 / 576 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hC]

  let pfun : ℝ → ℝ := fun t => 3 * (t + 8 * t ^ (1 - alpha / 2))
  let qfun : ℝ → ℝ := fun t => 3 * Real.sqrt t + 16 * t ^ ((1 - alpha) / 2)
  have hpcont : Continuous pfun := by
    dsimp [pfun]
    exact continuous_const.mul
      (continuous_id.add (continuous_const.mul (Real.continuous_rpow_const hpExp)))
  have hqcont : Continuous qfun := by
    dsimp [qfun]
    exact (continuous_const.mul Real.continuous_sqrt).add
      (continuous_const.mul (Real.continuous_rpow_const hqExp))
  have hbcont : Continuous (fun t : ℝ => epsilon + qfun t * (4 * C)) :=
    continuous_const.add (hqcont.mul continuous_const)
  have hbsqcont : Continuous (fun t : ℝ => (epsilon + qfun t * (4 * C)) ^ 2) := by
    convert hbcont.mul hbcont using 1 <;> ext t <;> simp [pow_two]
  let kfun : ℝ → ℝ := fun t =>
    72 * epsilon + 216 * pfun t * epsilon + 432 * pfun t * (4 * C) +
      384 * W * pfun t * (epsilon + qfun t * (4 * C)) ^ 2 +
      64 * W * qfun t * (epsilon + qfun t * (4 * C))
  have h72cont : Continuous (fun _ : ℝ => 72 * epsilon) := continuous_const
  have h216cont : Continuous (fun t : ℝ => 216 * pfun t * epsilon) := by
    exact ((continuous_const : Continuous (fun _ : ℝ => (216 : ℝ))).mul hpcont).mul
      (continuous_const : Continuous (fun _ : ℝ => epsilon))
  have h432cont : Continuous (fun t : ℝ => 432 * pfun t * (4 * C)) := by
    exact ((continuous_const : Continuous (fun _ : ℝ => (432 : ℝ))).mul hpcont).mul
      (continuous_const : Continuous (fun _ : ℝ => 4 * C))
  have h384cont : Continuous (fun t : ℝ => 384 * W * pfun t * (epsilon + qfun t * (4 * C)) ^ 2) := by
    exact ((continuous_const : Continuous (fun _ : ℝ => 384 * W)).mul hpcont).mul hbsqcont
  have h64cont : Continuous (fun t : ℝ => 64 * W * qfun t * (epsilon + qfun t * (4 * C))) := by
    exact ((continuous_const : Continuous (fun _ : ℝ => 64 * W)).mul hqcont).mul hbcont
  have hkcont : Continuous kfun := by
    dsimp [kfun]
    exact (((h72cont.add h216cont).add h432cont).add h384cont).add h64cont
  let f1 : ℝ → ℝ := fun t => epsilon + pfun t * (4 * C)
  let f2 : ℝ → ℝ := fun t => C * kfun t
  let f3 : ℝ → ℝ := fun t =>
    C * (1 + 3 * epsilon + D * epsilon ^ 2 + kfun t * (4 * C))
  have hf1cont : Continuous f1 := by
    dsimp [f1]
    exact continuous_const.add (hpcont.mul continuous_const)
  have hf2cont : Continuous f2 := by
    dsimp [f2]
    exact continuous_const.mul hkcont
  have hf3cont : Continuous f3 := by
    dsimp [f3]
    exact continuous_const.mul
      ((continuous_const.add (continuous_const.mul continuous_const)).add
        (hkcont.mul continuous_const))

  have hp0 : pfun 0 = 0 := by
    simp [pfun, ne_of_gt hpExpPos]
  have hq0 : qfun 0 = 0 := by
    simp [qfun, ne_of_gt hqExpPos]
  have hk0 : kfun 0 = 72 * epsilon := by simp [kfun, hp0, hq0]
  have hf10 : f1 0 = epsilon := by simp [f1, hp0]
  have hf20 : f2 0 = C * (72 * epsilon) := by simp [f2, hk0]
  have hf30 : f3 0 = C * (1 + 3 * epsilon + D * epsilon ^ 2 + (72 * epsilon) * (4 * C)) := by
    simp [f3, hk0]
  have hf1zero : f1 0 < 1 / 2 := by rw [hf10]; nlinarith [heps12]
  have hf2zero : f2 0 < 1 / 2 := by rw [hf20]; nlinarith [hCeps]
  have hbase3 : 1 + 3 * epsilon + D * epsilon ^ 2 + (72 * epsilon) * (4 * C) < 4 := by
    nlinarith [heps12, hquad, hCeps]
  have hf3zero : f3 0 < 4 * C := by
    rw [hf30]
    simpa [mul_comm] using (mul_lt_mul_of_pos_left hbase3 hC)

  have h1ev : ∀ᶠ t in 𝓝 (0 : ℝ), f1 t < 1 / 2 :=
    hf1cont.continuousAt.eventually (isOpen_Iio.mem_nhds hf1zero)
  have h2ev : ∀ᶠ t in 𝓝 (0 : ℝ), f2 t < 1 / 2 :=
    hf2cont.continuousAt.eventually (isOpen_Iio.mem_nhds hf2zero)
  have h3ev : ∀ᶠ t in 𝓝 (0 : ℝ), f3 t < 4 * C :=
    hf3cont.continuousAt.eventually (isOpen_Iio.mem_nhds hf3zero)
  obtain ⟨d1, hd1pos, hd1⟩ := Metric.eventually_nhds_iff.mp h1ev
  obtain ⟨d2, hd2pos, hd2⟩ := Metric.eventually_nhds_iff.mp h2ev
  obtain ⟨d3, hd3pos, hd3⟩ := Metric.eventually_nhds_iff.mp h3ev
  let m : ℝ := min 1 (min d1 (min d2 d3))
  let delta : ℝ := m / 2
  have hmpos : 0 < m := by dsimp [m]; positivity
  have hm1 : m ≤ d1 := by
    dsimp [m]
    exact le_trans (min_le_right 1 _) (min_le_left d1 _)
  have hm2 : m ≤ d2 := by
    dsimp [m]
    exact le_trans (min_le_right 1 _) <| le_trans (min_le_right d1 _) (min_le_left d2 d3)
  have hm3 : m ≤ d3 := by
    dsimp [m]
    exact le_trans (min_le_right 1 _) <| le_trans (min_le_right d1 _) (min_le_right d2 d3)
  have hdelta_pos : 0 < delta := by dsimp [delta]; positivity
  have hdelta_one : delta ≤ 1 := by
    dsimp [delta, m]
    have hle : min 1 (min d1 (min d2 d3)) ≤ 1 := min_le_left _ _
    nlinarith [hd1pos, hd2pos, hd3pos]
  have hdelta1 : delta < d1 := by dsimp [delta]; nlinarith [hmpos, hm1]
  have hdelta2 : delta < d2 := by dsimp [delta]; nlinarith [hmpos, hm2]
  have hdelta3 : delta < d3 := by dsimp [delta]; nlinarith [hmpos, hm3]
  refine ⟨epsilon, delta, hepspos, ?_, hdelta_pos, hdelta_one, ?_⟩
  · exact le_trans heps12 (by norm_num)
  · intro T hT hTdelta
    have hT1 : T < d1 := lt_of_le_of_lt hTdelta hdelta1
    have hT2 : T < d2 := lt_of_le_of_lt hTdelta hdelta2
    have hT3 : T < d3 := lt_of_le_of_lt hTdelta hdelta3
    have hdist : dist T (0 : ℝ) = T := by simp [abs_of_pos hT]
    have h1 : f1 T < 1 / 2 := hd1 (by simpa [hdist] using hT1)
    have h2 : f2 T < 1 / 2 := hd2 (by simpa [hdist] using hT2)
    have h3 : f3 T < 4 * C := hd3 (by simpa [hdist] using hT3)
    dsimp
    refine ⟨?_, ?_, ?_⟩
    · simpa [f1, pfun] using le_of_lt h1
    · simpa [f2, kfun, pfun, qfun] using le_of_lt h2
    · simpa [f3, kfun, pfun, qfun] using le_of_lt h3
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.InitialBackgroundSmallness
