import PoincareConjecture.ParallelImplementation.SlabTimeLipschitz
import PoincareConjecture.ParallelImplementation.ZeroTraceLowerJetSmallness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ZeroTraceValueHolderSmallness
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open scoped Topology ContDiff BoundedContinuousFunction
/-- Zero trace yields quantitative smallness in the full parabolic Holder value seminorm. -/
theorem zero_trace_value_holder_smallness
    (T alpha : ℝ) (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha < 1)
    (z : FullJet T) (hz : z ∈ fullParabolicJetSet T alpha hT.le) :
    ∀ p q : Slab T, ‖z.1.1.1.1 p-z.1.1.1.1 q‖ ≤
      8 * ‖z‖ * T^(1-alpha/2) * parabolicRho p q ^ alpha :=
/- SWARM_PROOF_BEGIN -/
by
  intro p q
  have hlower :=
    PoincareConjecture.ParallelImplementation.ZeroTraceLowerJetSmallness.zero_trace_lower_jet_smallness
      T alpha hT z hz
  have htimeNorm : ‖z.1.2‖ ≤ ‖z‖ := by
    calc
      ‖z.1.2‖ ≤ ‖z.1‖ := norm_snd_le _
      _ ≤ ‖z‖ := norm_fst_le _
  have hhessNorm : ‖z.1.1.1.2.2‖ ≤ ‖z‖ := by
    calc
      ‖z.1.1.1.2.2‖ ≤ ‖z.1.1.1.2‖ := norm_snd_le _
      _ ≤ ‖z.1.1.1‖ := norm_snd_le _
      _ ≤ ‖z.1.1‖ := norm_fst_le _
      _ ≤ ‖z.1‖ := norm_fst_le _
      _ ≤ ‖z‖ := norm_fst_le _
  have hgradNorm : ‖z.1.1.1.2.1‖ ≤ 3 * Real.sqrt T * ‖z‖ := by
    calc
      ‖z.1.1.1.2.1‖ ≤
          (2 * ‖z.1.2‖ + ‖z.1.1.1.2.2‖) * Real.sqrt T := hlower.2
      _ ≤ (2 * ‖z‖ + ‖z‖) * Real.sqrt T := by
        apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg T)
        linarith [htimeNorm, hhessNorm]
      _ = 3 * Real.sqrt T * ‖z‖ := by ring
  let S : ℝ := T ^ (1 - alpha / 2)
  let C : ℝ := ‖z‖ * S
  let d : ℝ := ‖p.2 - q.2‖
  let τ : ℝ := |(p.1 : ℝ) - (q.1 : ℝ)|
  have hSpos : 0 < S := by
    dsimp [S]
    exact Real.rpow_pos_of_pos hT (1 - alpha / 2)
  have hSnonneg : 0 ≤ S := hSpos.le
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdnonneg : 0 ≤ d := by dsimp [d]; positivity
  have hτnonneg : 0 ≤ τ := by dsimp [τ]; positivity
  have hτleT : τ ≤ T := by
    dsimp [τ]
    apply abs_le.mpr
    constructor <;> linarith [p.1.2.1, p.1.2.2, q.1.2.1, q.1.2.2]
  have hnearScale : d ≤ Real.sqrt T →
      Real.sqrt T * d ≤ S * d ^ alpha := by
    intro hdsmall
    by_cases hdzero : d = 0
    · simp [hdzero, S, Real.zero_rpow ha.ne']
    · have hdpos : 0 < d := lt_of_le_of_ne hdnonneg (Ne.symm hdzero)
      have hexp : 0 ≤ 1 - alpha := by linarith
      have hpow := Real.rpow_le_rpow hdnonneg hdsmall hexp
      have hdfactor : d = d ^ alpha * d ^ (1 - alpha) := by
        calc
          d = d ^ (1 : ℝ) := (Real.rpow_one d).symm
          _ = d ^ alpha * d ^ (1 - alpha) := by
            rw [← Real.rpow_add hdpos]
            congr 1
            ring
      have hcore : Real.sqrt T * Real.sqrt T ^ (1 - alpha) = S := by
        calc
          Real.sqrt T * Real.sqrt T ^ (1 - alpha) =
              Real.sqrt T ^ (1 : ℝ) * Real.sqrt T ^ (1 - alpha) := by
                rw [Real.rpow_one]
          _ = Real.sqrt T ^ (1 + (1 - alpha)) := by
                rw [← Real.rpow_add (Real.sqrt_pos.2 hT)]
          _ = S := by
                rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
                change T ^ ((1 / 2 : ℝ) * (1 + (1 - alpha))) =
                  T ^ (1 - alpha / 2)
                congr 1
                ring
      calc
        Real.sqrt T * d = Real.sqrt T * (d ^ alpha * d ^ (1 - alpha)) := by
          conv_lhs => rw [hdfactor]
        _ ≤ Real.sqrt T * (d ^ alpha * Real.sqrt T ^ (1 - alpha)) := by
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg T)
          exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hdnonneg _)
        _ = S * d ^ alpha := by
          calc
            Real.sqrt T * (d ^ alpha * Real.sqrt T ^ (1 - alpha)) =
                (Real.sqrt T * Real.sqrt T ^ (1 - alpha)) * d ^ alpha := by ring
            _ = S * d ^ alpha := by rw [hcore]
  have hfarScale : Real.sqrt T ≤ d → T ≤ S * d ^ alpha := by
    intro hdbig
    have hpow := Real.rpow_le_rpow (Real.sqrt_nonneg T) hdbig ha.le
    have hcore : S * Real.sqrt T ^ alpha = T := by
      calc
        S * Real.sqrt T ^ alpha =
            T ^ (1 - alpha / 2) * T ^ ((1 / 2 : ℝ) * alpha) := by
              dsimp [S]
              rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hT.le]
        _ = T ^ ((1 - alpha / 2) + (1 / 2 : ℝ) * alpha) :=
              (Real.rpow_add hT _ _).symm
        _ = T ^ (1 : ℝ) := by
              congr 1
              ring
        _ = T := Real.rpow_one T
    calc
      T = S * Real.sqrt T ^ alpha := hcore.symm
      _ ≤ S * d ^ alpha := mul_le_mul_of_nonneg_left hpow hSnonneg
  have htimeScale : τ ≤ S * τ ^ (alpha / 2) := by
    by_cases hτzero : τ = 0
    · simp [hτzero, S, Real.zero_rpow (div_ne_zero ha.ne' (by norm_num : (2 : ℝ) ≠ 0))]
    · have hτpos : 0 < τ := lt_of_le_of_ne hτnonneg (Ne.symm hτzero)
      have hexp : 0 ≤ 1 - alpha / 2 := by linarith
      have hpow := Real.rpow_le_rpow hτnonneg hτleT hexp
      have hτfactor : τ = τ ^ (alpha / 2) * τ ^ (1 - alpha / 2) := by
        calc
          τ = τ ^ (1 : ℝ) := (Real.rpow_one τ).symm
          _ = τ ^ (alpha / 2) * τ ^ (1 - alpha / 2) := by
            rw [← Real.rpow_add hτpos]
            congr 1
            ring
      calc
        τ = τ ^ (alpha / 2) * τ ^ (1 - alpha / 2) := hτfactor
        _ ≤ τ ^ (alpha / 2) * S := by
          exact mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hτnonneg _)
        _ = S * τ ^ (alpha / 2) := by ring
  have hspatial :
      ‖z.1.1.1.1 (p.1,p.2) - z.1.1.1.1 (p.1,q.2)‖ ≤
        3 * C * d ^ alpha := by
    by_cases hdsmall : d ≤ Real.sqrt T
    · have hjet : z.1.1.1 ∈ spaceTimeC2JetSet T := hz.1.1
      let f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 6) :=
        fun x => z.1.1.1.1 (p.1,x)
      have hslice := hjet p.1
      have hfdiffAt (x : EuclideanSpace ℝ (Fin 3)) : DifferentiableAt ℝ f x := by
        change DifferentiableAt ℝ (fun y => z.1.1.1.1 (p.1,y)) x
        exact (hslice.1 x).differentiableAt
      have hderivBound : ∀ x : EuclideanSpace ℝ (Fin 3),
          ‖fderiv ℝ f x‖ ≤ 3 * Real.sqrt T * ‖z‖ := by
        intro x
        have hgradAt := (hslice.1 x).fderiv
        rw [hgradAt]
        exact (BoundedContinuousFunction.norm_coe_le_norm z.1.1.1.2.1 (p.1,x)).trans
          hgradNorm
      have hLipConst : 0 ≤ 3 * Real.sqrt T * ‖z‖ := by positivity
      have hderivNN (x : EuclideanSpace ℝ (Fin 3)) :
          ‖fderiv ℝ f x‖₊ ≤ Real.toNNReal (3 * Real.sqrt T * ‖z‖) := by
        rw [← NNReal.coe_le_coe, Real.coe_toNNReal (3 * Real.sqrt T * ‖z‖) hLipConst,
          coe_nnnorm]
        exact hderivBound x
      have hLip : LipschitzWith (Real.toNNReal (3 * Real.sqrt T * ‖z‖)) f :=
        lipschitzWith_of_nnnorm_fderiv_le (fun x => hfdiffAt x) hderivNN
      have hmv : ‖f p.2 - f q.2‖ ≤
          (3 * Real.sqrt T * ‖z‖) * ‖q.2 - p.2‖ := by
        have hh := hLip.dist_le_mul p.2 q.2
        simpa [dist_eq_norm, norm_sub_rev, Real.coe_toNNReal
          (3 * Real.sqrt T * ‖z‖) hLipConst] using hh
      have hscale := hnearScale hdsmall
      calc
        ‖z.1.1.1.1 (p.1,p.2) - z.1.1.1.1 (p.1,q.2)‖ = ‖f p.2 - f q.2‖ := rfl
        _ ≤ (3 * Real.sqrt T * ‖z‖) * ‖q.2 - p.2‖ := hmv
        _ = 3 * ‖z‖ * (Real.sqrt T * d) := by
          dsimp [d]
          rw [norm_sub_rev]
          ring
        _ ≤ 3 * ‖z‖ * (S * d ^ alpha) :=
          mul_le_mul_of_nonneg_left hscale (by positivity)
        _ = 3 * C * d ^ alpha := by dsimp [C]; ring
    · have hdbig : Real.sqrt T ≤ d := le_of_not_ge hdsmall
      have hvalPoint (x : EuclideanSpace ℝ (Fin 3)) :
          ‖z.1.1.1.1 (p.1,x)‖ ≤ T * ‖z‖ := by
        calc
          ‖z.1.1.1.1 (p.1,x)‖ ≤ ‖z.1.1.1.1‖ :=
            BoundedContinuousFunction.norm_coe_le_norm z.1.1.1.1 (p.1,x)
          _ ≤ T * ‖z.1.2‖ := hlower.1
          _ ≤ T * ‖z‖ := mul_le_mul_of_nonneg_left htimeNorm hT.le
      have hdiff :
          ‖z.1.1.1.1 (p.1,p.2) - z.1.1.1.1 (p.1,q.2)‖ ≤ 2 * T * ‖z‖ := by
        calc
          _ ≤ ‖z.1.1.1.1 (p.1,p.2)‖ + ‖z.1.1.1.1 (p.1,q.2)‖ := norm_sub_le _ _
          _ ≤ T * ‖z‖ + T * ‖z‖ := add_le_add (hvalPoint p.2) (hvalPoint q.2)
          _ = 2 * T * ‖z‖ := by ring
      calc
        _ ≤ 2 * T * ‖z‖ := hdiff
        _ ≤ 3 * C * d ^ alpha := by
          have hscale := hfarScale hdbig
          calc
            2 * T * ‖z‖ = 2 * ‖z‖ * T := by ring
            _ ≤ (2 * ‖z‖) * (S * d ^ alpha) :=
              mul_le_mul_of_nonneg_left hscale (by positivity)
            _ ≤ 3 * C * d ^ alpha := by
              dsimp [C]
              nlinarith [mul_nonneg (norm_nonneg z)
                (mul_nonneg hSnonneg (Real.rpow_nonneg hdnonneg alpha))]
  have htempeq : (Real.sqrt τ) ^ alpha = τ ^ (alpha / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hτnonneg]
    congr 1
    ring
  have hrhoD : d ≤ parabolicRho p q := by
    dsimp [d, parabolicRho]
    linarith [Real.sqrt_nonneg τ]
  have hrhoSqrt : Real.sqrt τ ≤ parabolicRho p q := by
    dsimp [parabolicRho]
    linarith [hdnonneg]
  have hspacePow : d ^ alpha ≤ parabolicRho p q ^ alpha :=
    Real.rpow_le_rpow hdnonneg hrhoD ha.le
  have htimePow : τ ^ (alpha / 2) ≤ parabolicRho p q ^ alpha := by
    rw [← htempeq]
    exact Real.rpow_le_rpow (Real.sqrt_nonneg τ) hrhoSqrt ha.le
  have hspatial' :
      ‖z.1.1.1.1 (p.1,p.2) - z.1.1.1.1 (p.1,q.2)‖ ≤
        3 * C * parabolicRho p q ^ alpha := by
    exact hspatial.trans (mul_le_mul_of_nonneg_left hspacePow (by positivity))
  have htemporal :
      ‖z.1.1.1.1 (p.1,q.2) - z.1.1.1.1 (q.1,q.2)‖ ≤
        C * parabolicRho p q ^ alpha := by
    have htime :=
      PoincareConjecture.ParallelImplementation.SlabTimeLipschitz.slab_time_lipschitz
        T hT.le z.1.1.1.1 z.1.2 hz.2.1 p.1 q.1 q.2
    calc
      _ = ‖z.1.1.1.1 (q.1,q.2) - z.1.1.1.1 (p.1,q.2)‖ := by
        rw [norm_sub_rev]
      _ ≤ ‖z.1.2‖ * τ := by simpa [τ, abs_sub_comm] using htime
      _ ≤ ‖z‖ * τ := mul_le_mul_of_nonneg_right htimeNorm hτnonneg
      _ ≤ ‖z‖ * (S * τ ^ (alpha / 2)) :=
        mul_le_mul_of_nonneg_left htimeScale (norm_nonneg _)
      _ = C * τ ^ (alpha / 2) := by dsimp [C]; ring
      _ ≤ C * parabolicRho p q ^ alpha :=
        mul_le_mul_of_nonneg_left htimePow hCnonneg
  have hsum :
      ‖z.1.1.1.1 (p.1,p.2) - z.1.1.1.1 (q.1,q.2)‖ ≤
        3 * C * parabolicRho p q ^ alpha + C * parabolicRho p q ^ alpha := by
    calc
      _ = ‖(z.1.1.1.1 (p.1,p.2) - z.1.1.1.1 (p.1,q.2)) +
            (z.1.1.1.1 (p.1,q.2) - z.1.1.1.1 (q.1,q.2))‖ := by
        congr 1
        abel
      _ ≤ ‖z.1.1.1.1 (p.1,p.2) - z.1.1.1.1 (p.1,q.2)‖ +
            ‖z.1.1.1.1 (p.1,q.2) - z.1.1.1.1 (q.1,q.2)‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hspatial' htemporal
  have htarget : 3 * C * parabolicRho p q ^ alpha +
      C * parabolicRho p q ^ alpha ≤ 8 * ‖z‖ * S * parabolicRho p q ^ alpha := by
    dsimp [C]
    have hpowNonneg : 0 ≤ parabolicRho p q ^ alpha := Real.rpow_nonneg (by
      unfold parabolicRho
      positivity) _
    nlinarith [mul_nonneg (norm_nonneg z) (mul_nonneg hSnonneg hpowNonneg)]
  exact hsum.trans htarget
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ZeroTraceValueHolderSmallness
