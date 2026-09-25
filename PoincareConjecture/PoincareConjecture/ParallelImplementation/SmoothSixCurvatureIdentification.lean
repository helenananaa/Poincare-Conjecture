import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import MorganTianLib.Ch03.RicciFlow.Basic
import PoincareConjecture.ParallelImplementation.SmoothSixLeviCivitaIdentification
import PoincareConjecture.ParallelImplementation.SmoothSixChristoffelField
import PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields
import PoincareConjecture.ParallelImplementation.EuclideanConnectionCurvatureExpansion
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmoothSixCurvatureIdentification
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_six_curvature_identification
    (E : E6 →L[ℝ] (E3 →L[ℝ] E3))
    (hE : ∀ (q : E6) (v : E3) (i : Idx), (E q v) i = ∑ j : Idx, symmetricSixMatrix q i j*v j)
    (u : E3 → E6) (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ (x v : E3), v ≠ 0 → 0 < inner ℝ (metricOp E u x v) v) :

    ∃ g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3,
      ∃ V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3,
        (∀ (x v w : E3), g.metricInner x v w = inner ℝ (metricOp E u x v) w) ∧
        (∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1) ∧
        ∀ (x : E3) (i j k s : Idx), (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) s : E3 →L[ℝ] ℝ) ((g.leviCivitaConnection.curvature (V i) (V j) (V k)) x) = (deriv (fun t : ℝ => (christoffelField E u) (x + t • EuclideanSpace.single j 1) s i k) 0 - deriv (fun t : ℝ => (christoffelField E u) (x + t • EuclideanSpace.single i 1) s j k) 0 + (∑ m : Idx, ((christoffelField E u) x m i k * (christoffelField E u) x s j m - (christoffelField E u) x m j k * (christoffelField E u) x s i m))) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨g, V, hg, hV, hcoeff⟩ :=
    PoincareConjecture.ParallelImplementation.SmoothSixLeviCivitaIdentification.exists_six_levicivita_identification
      E hE u hu hpos
  obtain ⟨W, hW, hbrW, _⟩ :=
    PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields.exists_coordinate_fields
  let G : E3 → First := fun x k i j => christoffelField E u x k i j
  have hVW : ∀ i : Idx, V i = W i := by
    intro i
    apply Riemannian.SmoothVectorField.ext
    intro x
    rw [hV i x, hW i x]
  have hG : ∀ (x : E3) (i j k : Idx),
      (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ)
        ((g.leviCivitaConnection.cov (V i) (V j)) x) = G x k i j := by
    intro x i j k
    simpa [G] using hcoeff x i j k
  have hbr : ∀ (i j : Idx) (x : E3),
      Riemannian.DCLieBracket (V i) (V j) x = 0 := by
    intro i j x
    rw [hVW i, hVW j]
    exact hbrW i j x
  have hGsmooth : ∀ k i j : Idx, ContDiff ℝ ∞ (fun x : E3 => G x k i j) := by
    intro k i j
    change ContDiff ℝ ∞ (fun x : E3 => christoffelField E u x k i j)
    exact PoincareConjecture.ParallelImplementation.SmoothSixChristoffelField.smooth_six_christoffel
      E hE u hu hpos k i j
  refine ⟨g, V, hg, hV, ?_⟩
  simpa [G] using
    (PoincareConjecture.ParallelImplementation.EuclideanConnectionCurvatureExpansion.curvature_in_coordinate_frame
      g.leviCivitaConnection V hV G hG hbr hGsmooth)
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmoothSixCurvatureIdentification
