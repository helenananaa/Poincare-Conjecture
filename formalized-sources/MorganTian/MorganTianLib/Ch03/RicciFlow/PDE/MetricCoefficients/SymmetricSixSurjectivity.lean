import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.LocalInverseControl
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseQuadraticRemainder
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.PrincipalPartDifference
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- The six-coordinate encoder represents every symmetric metric coefficient uniquely. -/
theorem symmetric_six_all_metrics :
    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖≤3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i = ∑ j : Fin 3, symmetricSixMatrix q i j*v j) ∧
      ∀ A : E3 →L[ℝ] E3, (∀ v w : E3, inner ℝ (A v) w=inner ℝ v (A w)) →
        ∃! q : E6, E q=A :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨E, hE_inj, hE_norm, hE_action, hE_sym⟩ := symmetric_six_realization
  refine ⟨E, hE_inj, hE_norm, hE_action, ?_⟩
  intro A hA
  let e : Fin 3 → E3 := fun i => EuclideanSpace.single i 1
  let q : E6 := WithLp.toLp 2 ![A (e 0) 0, A (e 1) 1, A (e 2) 2,
    A (e 1) 0, A (e 2) 0, A (e 2) 1]
  have hAcoord : ∀ i j : Fin 3, (A (e j)) i = (A (e i)) j := by
    intro i j
    simpa [e, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      hA (e j) (e i)
  have hEcoord : ∀ i j : Fin 3, (E q (e j)) i = (E q (e i)) j := by
    intro i j
    simpa [e, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      hE_sym q (e j) (e i)
  have hEentry : ∀ i j : Fin 3, (E q (e j)) i = symmetricSixMatrix q i j := by
    intro i j
    rw [hE_action q (e j) i]
    simp [e, symmetricSixMatrix]
  have hupper : ∀ i j : Fin 3, i ≤ j → (A (e j)) i = (E q (e j)) i := by
    intro i j hij
    have hij' : i.val ≤ j.val := hij
    rw [hEentry]
    fin_cases i <;> fin_cases j
    · simp [e, q, symmetricSixMatrix]
    · simp [e, q, symmetricSixMatrix]
    · simp [e, q, symmetricSixMatrix]
    · fin_omega
    · simp [e, q, symmetricSixMatrix]
    · simp [e, q, symmetricSixMatrix]
    · fin_omega
    · fin_omega
    · simp [e, q, symmetricSixMatrix]
  have hcoord : ∀ i j : Fin 3, (A (e j)) i = (E q (e j)) i := by
    intro i j
    by_cases hij : i ≤ j
    · exact hupper i j hij
    · have hji : j ≤ i := by omega
      rw [hAcoord i j, hEcoord i j]
      exact hupper j i hji
  have hbasis : ∀ j : Fin 3, A (e j) = E q (e j) := by
    intro j
    ext i
    exact hcoord i j
  have hexpand (v : E3) : (∑ j : Fin 3, v j • e j) = v := by
    simpa [e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hEq : E q = A := by
    apply ContinuousLinearMap.ext
    intro v
    calc
      E q v = E q (∑ j : Fin 3, v j • e j) := by rw [hexpand]
      _ = ∑ j : Fin 3, v j • E q (e j) := by simp only [map_sum, map_smul]
      _ = ∑ j : Fin 3, v j • A (e j) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hbasis j]
      _ = A (∑ j : Fin 3, v j • e j) := by
        rw [map_sum]
        simp only [map_smul]
      _ = A v := by rw [hexpand]
  refine ⟨q, hEq, ?_⟩
  intro r hr
  apply hE_inj
  exact hr.trans hEq.symm
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
