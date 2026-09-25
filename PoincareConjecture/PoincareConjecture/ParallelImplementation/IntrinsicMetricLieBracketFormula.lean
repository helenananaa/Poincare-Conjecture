import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.HamiltonGauge
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBracketFormula
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem metric_lie_bracket_formula
    (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3)
    (W X Y : Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3) (x : E3) :

    MorganTianLib.metricLieDerivativeAt g W x (X x) (Y x) =
      W.dir (fun y => g.metricInner y (X y) (Y y)) x -
      g.metricInner x (Riemannian.DCLieBracket W X x) (Y x) -
      g.metricInner x (X x) (Riemannian.DCLieBracket W Y x) :=
/- SWARM_PROOF_BEGIN -/
by
  have hLC : g.leviCivitaConnection.IsLeviCivita g :=
    g.leviCivitaConnection.isLeviCivita_of_koszulDual g
      (fun X Y Z q => g.koszulDualSection_dual X Y Z q)
  have hX :
      (g.leviCivitaConnection.cov (MorganTianLib.extendVector x (X x)) W) x =
        (g.leviCivitaConnection.cov X W) x := by
    apply g.leviCivitaConnection.cov_congr_apply_left W
    exact MorganTianLib.extendVector_apply x (X x)
  have hY :
      (g.leviCivitaConnection.cov (MorganTianLib.extendVector x (Y x)) W) x =
        (g.leviCivitaConnection.cov Y W) x := by
    apply g.leviCivitaConnection.cov_congr_apply_left W
    exact MorganTianLib.extendVector_apply x (Y x)
  have hWX :
      (g.leviCivitaConnection.cov W X) x =
        (g.leviCivitaConnection.cov X W) x + Riemannian.DCLieBracket W X x := by
    have ht := hLC.1 W X x
    rw [sub_eq_iff_eq_add] at ht
    calc
      (g.leviCivitaConnection.cov W X) x =
          Riemannian.DCLieBracket W X x + (g.leviCivitaConnection.cov X W) x := ht
      _ = (g.leviCivitaConnection.cov X W) x + Riemannian.DCLieBracket W X x :=
        add_comm _ _
  have hWY :
      (g.leviCivitaConnection.cov W Y) x =
        (g.leviCivitaConnection.cov Y W) x + Riemannian.DCLieBracket W Y x := by
    have ht := hLC.1 W Y x
    rw [sub_eq_iff_eq_add] at ht
    calc
      (g.leviCivitaConnection.cov W Y) x =
          Riemannian.DCLieBracket W Y x + (g.leviCivitaConnection.cov Y W) x := ht
      _ = (g.leviCivitaConnection.cov Y W) x + Riemannian.DCLieBracket W Y x :=
        add_comm _ _
  have hmain :
      W.dir (fun y => g.metricInner y (X y) (Y y)) x =
        g.metricInner x ((g.leviCivitaConnection.cov X W) x) (Y x) +
          g.metricInner x (Riemannian.DCLieBracket W X x) (Y x) +
          g.metricInner x (X x) ((g.leviCivitaConnection.cov Y W) x) +
          g.metricInner x (X x) (Riemannian.DCLieBracket W Y x) := by
    calc
      W.dir (fun y => g.metricInner y (X y) (Y y)) x =
          g.metricInner x ((g.leviCivitaConnection.cov W X) x) (Y x) +
            g.metricInner x (X x) ((g.leviCivitaConnection.cov W Y) x) :=
        hLC.2 W X Y x
      _ = _ := by
        rw [hWX, hWY, g.metricInner_add_left, g.metricInner_add_right]
        ring
  rw [MorganTianLib.metricLieDerivativeAt, hX, hY]
  linarith [hmain]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.IntrinsicMetricLieBracketFormula
