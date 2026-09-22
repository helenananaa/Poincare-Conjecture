import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.DeTurckPrincipalJet
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.MetricSecondJetSymmetry
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateMetricCompatibility
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.CoordinateChristoffelSmooth
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.InverseDifferential
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricInverseBounds
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter
open scoped Topology ContDiff BigOperators RealInnerProductSpace
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- The frozen Ricci-DeTurck principal-jet calculation applies to actual C2 metric derivatives. -/
theorem actual_metric_principal_jet_identity (G : E3 → (E3 →L[ℝ] E3))
    (hG : ContDiff ℝ 2 G)
    (hsym : ∀ y v w : E3, inner ℝ (G y v) w=inner ℝ v (G y w))
    (x : E3) (c : ℝ) (hc : 0<c)
    (hpos : ∀ v : E3, c*‖v‖^2 ≤ inner ℝ (G x v) v) (i j : Fin 3) :
    let C : Matrix (Fin 3) (Fin 3) ℝ := fun k l => ((G x).inverse (EuclideanSpace.single l 1)) k
    let Q := fun r s k l : Fin 3 =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single s 1)) x
        (EuclideanSpace.single r 1) (EuclideanSpace.single l 1)) k;
    -2*(∑ k : Fin 3, (principalConnectionJet C Q k k i j-principalConnectionJet C Q j k i k)) +
      (∑ p : Fin 3, ∑ q : Fin 3, C p q*(Q i p j q+Q j p i q-Q i j p q)) =
      ∑ p : Fin 3, ∑ q : Fin 3, C p q*Q p q i j :=
/- SWARM_PROOF_BEGIN -/
by
  dsimp
  classical
  have hInvSym :=
    (symmetric_inverse_bounds (G x) c hc hpos (hsym x)).1
  have hC : ∀ k l : Fin 3,
      (G x).inverse (EuclideanSpace.single l 1) k =
        (G x).inverse (EuclideanSpace.single k 1) l := by
    intro k l
    simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using
      hInvSym (EuclideanSpace.single l 1) (EuclideanSpace.single k 1)
  have hQ := metric_second_jets_symmetric G hG hsym x
  rcases hQ with ⟨hQderiv, hQmetric⟩
  have hderiv : ∀ r s i j : Fin 3,
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single s 1)) x
        (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)) i =
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single r 1)) x
        (EuclideanSpace.single s 1) (EuclideanSpace.single j 1)) i := by
    intro r s i j
    exact congrArg (fun L : E3 →L[ℝ] E3 => L (EuclideanSpace.single j 1) i)
      (hQderiv r s)
  have hmetric : ∀ r s i j : Fin 3,
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single s 1)) x
        (EuclideanSpace.single r 1) (EuclideanSpace.single j 1)) i =
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single s 1)) x
        (EuclideanSpace.single r 1) (EuclideanSpace.single i 1)) j := by
    intro r s i j
    have h := hQmetric r s (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using h
  apply deturck_principal_jet_cancellation
    (fun k l => (G x).inverse (EuclideanSpace.single l 1) k) hC
    (fun r s => fun k l =>
      (fderiv ℝ (fun y : E3 => fderiv ℝ G y (EuclideanSpace.single s 1)) x
        (EuclideanSpace.single r 1) (EuclideanSpace.single l 1)) k)
    hderiv hmetric i j
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
