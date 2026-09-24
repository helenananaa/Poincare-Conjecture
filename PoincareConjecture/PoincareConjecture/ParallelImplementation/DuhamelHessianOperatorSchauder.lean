import PoincareConjecture.ParallelImplementation.HessianOperatorDifference
import PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ActualDuhamelSpatialSchauder
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.DuhamelHessianOperatorSchauder
open Set MeasureTheory
open scoped Topology ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- **Math.** Joint space-time bounds for the genuine second Frechet derivative. -/
theorem actual_duhamel_hessian_operator_schauder
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (F : (ℝ × E3) →ᵇ ℝ) (L T : ℝ),
      0 ≤ L → 0 ≤ T →
      (∀ r ∈ Icc (0:ℝ) T, ∀ x z : E3, |F (r,x)-F (r,z)| ≤ L*‖x-z‖^alpha) →
      let u : ℝ → E3 → ℝ := fun t x => ∫ r in (0:ℝ)..t, ∫ y : E3,
        MorganTianLib.ParabolicPDE.euclideanHeatKernel 3 (t-r) (x-y)*F (r,y)
      (∀ t ∈ Icc (0:ℝ) T, ContDiff ℝ 2 (u t)) ∧
      (∀ t ∈ Icc (0:ℝ) T, ∀ x, ‖fderiv ℝ (fderiv ℝ (u t)) x‖ ≤ C*L*t^(alpha/2)) ∧
      ∀ t ∈ Icc (0:ℝ) T, ∀ s ∈ Icc (0:ℝ) T, ∀ x z,
        ‖fderiv ℝ (fderiv ℝ (u t)) x - fderiv ℝ (fderiv ℝ (u s)) z‖ ≤
          C*L*(‖x-z‖^alpha+|t-s|^(alpha/2)) :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨Csp, hCsp, hsp⟩ :=
    MorganTianLib.MetricCoefficient.actual_duhamel_spatial_schauder alpha ha ha1
  obtain ⟨Ct, hCt, htemp⟩ :=
    PoincareConjecture.ParallelImplementation.ActualDuhamelTemporalSchauder.actual_duhamel_temporal_schauder
      alpha ha ha1
  let C : ℝ := 1 + max (9 * Csp) (9 * Ct)
  have hC : 0 < C := by
    dsimp [C]
    have hspPos : 0 < 9 * Csp := by positivity
    have htempPos : 0 < 9 * Ct := by positivity
    have hmaxPos : 0 < max (9 * Csp) (9 * Ct) :=
      lt_of_lt_of_le hspPos (le_max_left (9 * Csp) (9 * Ct))
    linarith
  have hCspC : 9 * Csp ≤ C := by
    dsimp [C]
    linarith [le_max_left (9 * Csp) (9 * Ct)]
  have hCtC : 9 * Ct ≤ C := by
    dsimp [C]
    linarith [le_max_right (9 * Csp) (9 * Ct)]
  refine ⟨C, hC, ?_⟩
  intro F L T hL hT hholder u
  let H : ℝ → E3 → E3 →L[ℝ] E3 →L[ℝ] ℝ :=
    fun t x => fderiv ℝ (fderiv ℝ (u t)) x
  have hzero : u 0 = fun _ : E3 => (0 : ℝ) := by
    funext x
    simp [u]
  have hsource (q : ℝ) (hq : 0 ≤ q) (hqT : q ≤ T) :
      ContDiff ℝ 2 (u q) ∧
      (∀ x (i j : Fin 3),
        |fderiv ℝ (fun y => fderiv ℝ (u q) y (EuclideanSpace.single i 1)) x
          (EuclideanSpace.single j 1)| ≤ Csp * L * q^(alpha/2)) ∧
      (∀ x z (i j : Fin 3),
        |fderiv ℝ (fun y => fderiv ℝ (u q) y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1) -
         fderiv ℝ (fun y => fderiv ℝ (u q) y (EuclideanSpace.single i 1)) z
            (EuclideanSpace.single j 1)| ≤ Csp * L * ‖x-z‖^alpha) := by
    by_cases hq0 : q = 0
    · subst q
      refine ⟨?_, ?_, ?_⟩
      · simpa [hzero] using
          (contDiff_const : ContDiff ℝ 2 (fun _ : E3 => (0 : ℝ)))
      · intro x i j
        have hpow : 0 ≤ (0 : ℝ)^(alpha/2) := Real.rpow_nonneg (by norm_num) _
        have hbound : 0 ≤ Csp * L * (0 : ℝ)^(alpha/2) := by positivity
        simpa [hzero] using hbound
      · intro x z i j
        have hbound : 0 ≤ Csp * L * ‖x-z‖^alpha := by positivity
        simpa [hzero] using hbound
    · have hqpos : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
      have hqholder : ∀ r ∈ Icc (0:ℝ) q, ∀ x z : E3,
          |F (r,x)-F (r,z)| ≤ L*‖x-z‖^alpha := by
        intro r hr x z
        apply hholder r
        exact ⟨hr.1, hr.2.trans hqT⟩
      have hraw := hsp F L q hL hqpos hqholder
      refine ⟨?_, ?_, ?_⟩
      · simpa [u] using hraw.1
      · intro x i j
        simpa [u] using hraw.2.1 x i j
      · intro x z i j
        simpa [u] using hraw.2.2 x z i j
  have hspaceOp : ∀ t ∈ Icc (0:ℝ) T, ∀ x z : E3,
      ‖H t x - H t z‖ ≤ 9 * Csp * L * ‖x-z‖^alpha := by
    intro t ht x z
    have hs := hsource t ht.1 ht.2
    let D : ℝ := Csp * L * ‖x-z‖^alpha
    have hD : 0 ≤ D := by dsimp [D]; positivity
    have hcomponents : ∀ i j : Fin 3,
        |fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1) -
         fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) z
            (EuclideanSpace.single j 1)| ≤ D := by
      intro i j
      simpa [D] using hs.2.2 x z i j
    have hbridge :=
      PoincareConjecture.ParallelImplementation.HessianOperatorDifference.hessian_opNorm_difference_of_components
        (u t) (u t) hs.1 hs.1 x z D hD hcomponents
    calc
      ‖H t x - H t z‖ ≤ 9 * D := by simpa [H] using hbridge
      _ = 9 * Csp * L * ‖x-z‖^alpha := by dsimp [D]; ring
  have hOpSup : ∀ t ∈ Icc (0:ℝ) T, ∀ x : E3,
      ‖H t x‖ ≤ 9 * Csp * L * t^(alpha/2) := by
    intro t ht x
    have hs := hsource t ht.1 ht.2
    let D : ℝ := Csp * L * t^(alpha/2)
    have hpow : 0 ≤ t^(alpha/2) := Real.rpow_nonneg ht.1 _
    have hD : 0 ≤ D := by
      dsimp [D]
      exact mul_nonneg (mul_nonneg (le_of_lt hCsp) hL) hpow
    have hcomponents : ∀ i j : Fin 3,
        |fderiv ℝ (fun y => fderiv ℝ (u t) y (EuclideanSpace.single i 1)) x
            (EuclideanSpace.single j 1) -
         fderiv ℝ (fun y => fderiv ℝ (fun _ : E3 => (0:ℝ)) y
             (EuclideanSpace.single i 1)) x (EuclideanSpace.single j 1)| ≤ D := by
      intro i j
      have hi := hs.2.1 x i j
      simpa [D] using hi
    have hbridge :=
      PoincareConjecture.ParallelImplementation.HessianOperatorDifference.hessian_opNorm_difference_of_components
        (u t) (fun _ : E3 => (0:ℝ)) hs.1
        (contDiff_const : ContDiff ℝ 2 (fun _ : E3 => (0:ℝ))) x x D hD hcomponents
    have hzeroH (x : E3) :
        fderiv ℝ (fderiv ℝ (fun _ : E3 => (0:ℝ))) x = 0 := by simp
    calc
      ‖H t x‖ = ‖H t x - fderiv ℝ (fderiv ℝ (fun _ : E3 => (0:ℝ))) x‖ := by
        rw [hzeroH, sub_zero]
      _ ≤ 9 * D := by simpa [H] using hbridge
      _ = 9 * Csp * L * t^(alpha/2) := by dsimp [D]; ring
  have htimeOp : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → ∀ x : E3,
      ‖H b x - H a x‖ ≤ 9 * Ct * L * (b-a)^(alpha/2) := by
    intro a b ha hab hb x
    by_cases habEq : a = b
    · subst b
      have hpow : 0 ≤ (0:ℝ)^(alpha/2) := Real.rpow_nonneg (by norm_num) _
      have hbound : 0 ≤ 9 * Ct * L * (0:ℝ)^(alpha/2) := by positivity
      simpa using hbound
    · have hstrict : a < b := lt_of_le_of_ne hab habEq
      have hh : 0 < b-a := sub_pos.mpr hstrict
      have hsum : a + (b-a) = b := by ring
      have hholderPlus : ∀ r ∈ Icc (0:ℝ) (a + (b-a)), ∀ y z : E3,
          |F (r,y)-F (r,z)| ≤ L*‖y-z‖^alpha := by
        intro r hr y z
        apply hholder r
        have hrb : r ≤ b := by rw [← hsum]; exact hr.2
        exact ⟨hr.1, hrb.trans hb⟩
      have htempCoord := htemp F L a (b-a) hL ha hh hholderPlus x
      let D : ℝ := Ct * L * (b-a)^(alpha/2)
      have hD : 0 ≤ D := by dsimp [D]; positivity
      have hcomponents : ∀ i j : Fin 3,
          |fderiv ℝ (fun y => fderiv ℝ (u b) y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single j 1) -
           fderiv ℝ (fun y => fderiv ℝ (u a) y (EuclideanSpace.single i 1)) x
              (EuclideanSpace.single j 1)| ≤ D := by
        intro i j
        simpa [D, hsum] using htempCoord i j
      have hsa := hsource a ha (le_trans hab hb)
      have hsb := hsource b (le_trans ha hab) hb
      have hbridge :=
        PoincareConjecture.ParallelImplementation.HessianOperatorDifference.hessian_opNorm_difference_of_components
          (u b) (u a) hsb.1 hsa.1 x x D hD hcomponents
      calc
        ‖H b x - H a x‖ ≤ 9 * D := by simpa [H] using hbridge
        _ = 9 * Ct * L * (b-a)^(alpha/2) := by dsimp [D]; ring
  have htimeAt : ∀ t ∈ Icc (0:ℝ) T, ∀ s ∈ Icc (0:ℝ) T, ∀ x : E3,
      ‖H t x - H s x‖ ≤ 9 * Ct * L * |t-s|^(alpha/2) := by
    intro t ht s hs x
    by_cases hts : t ≤ s
    · have h := htimeOp t s ht.1 hts hs.2 x
      have habs : |t-s| = s-t := by
        calc
          |t-s| = -(t-s) := abs_of_nonpos (sub_nonpos.mpr hts)
          _ = s-t := by ring
      calc
        ‖H t x - H s x‖ = ‖H s x - H t x‖ := norm_sub_rev _ _
        _ ≤ 9 * Ct * L * (s-t)^(alpha/2) := h
        _ = 9 * Ct * L * |t-s|^(alpha/2) := by rw [habs]
    · have hst : s ≤ t := le_of_not_ge hts
      have h := htimeOp s t hs.1 hst ht.2 x
      have habs : |t-s| = t-s := abs_of_nonneg (sub_nonneg.mpr hst)
      simpa [habs] using h
  have hcoefSp : 9 * Csp * L ≤ C * L := by
    calc
      9 * Csp * L = (9 * Csp) * L := by ring
      _ ≤ C * L := mul_le_mul_of_nonneg_right hCspC hL
  have hcoefTemp : 9 * Ct * L ≤ C * L := by
    calc
      9 * Ct * L = (9 * Ct) * L := by ring
      _ ≤ C * L := mul_le_mul_of_nonneg_right hCtC hL
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    exact (hsource t ht.1 ht.2).1
  · intro t ht x
    change ‖H t x‖ ≤ C * L * t^(alpha/2)
    have hpow : 0 ≤ t^(alpha/2) := Real.rpow_nonneg ht.1 _
    calc
      ‖H t x‖ ≤ 9 * Csp * L * t^(alpha/2) := hOpSup t ht x
      _ ≤ C * L * t^(alpha/2) := by
        apply mul_le_mul_of_nonneg_right hcoefSp hpow
  · intro t ht s hs x z
    change ‖H t x - H s z‖ ≤ C * L * (‖x-z‖^alpha + |t-s|^(alpha/2))
    let A : ℝ := ‖x-z‖^alpha
    let B : ℝ := |t-s|^(alpha/2)
    have hA : 0 ≤ A := by dsimp [A]; exact Real.rpow_nonneg (norm_nonneg _) _
    have hB : 0 ≤ B := by dsimp [B]; exact Real.rpow_nonneg (abs_nonneg _) _
    calc
      ‖H t x - H s z‖ =
          ‖(H t x - H t z) + (H t z - H s z)‖ := by congr 1; abel
      _ ≤ ‖H t x - H t z‖ + ‖H t z - H s z‖ := norm_add_le _ _
      _ ≤ 9 * Csp * L * A + 9 * Ct * L * B :=
        add_le_add (by simpa [A] using hspaceOp t ht x z)
          (by simpa [B] using htimeAt t ht s hs z)
      _ ≤ C * L * A + C * L * B :=
        add_le_add (mul_le_mul_of_nonneg_right hcoefSp hA)
          (mul_le_mul_of_nonneg_right hcoefTemp hB)
      _ = C * L * (A+B) := by ring
      _ = C * L * (‖x-z‖^alpha + |t-s|^(alpha/2)) := by simp [A, B]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.DuhamelHessianOperatorSchauder
