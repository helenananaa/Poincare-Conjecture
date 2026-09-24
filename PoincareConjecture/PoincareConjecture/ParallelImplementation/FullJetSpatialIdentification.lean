import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
/-- Identify both spatial jet fields with the genuine derivatives of an equal value slice. -/
theorem full_jet_spatial_identification
    (T alpha : ℝ) (hT : 0 ≤ T) (z : FullJet T)
    (hz : z ∈ fullParabolicJetSet T alpha hT)
    (t : Set.Icc (0:ℝ) T) (u : E3 → E6)
    (hu : ∀ x, z.1.1.1.1 (t,x) = u x) :
    (∀ x, z.1.1.1.2.1 (t,x) = fderiv ℝ u x) ∧
    (∀ x, z.1.1.1.2.2 (t,x) = fderiv ℝ (fderiv ℝ u) x) :=
/- SWARM_PROOF_BEGIN -/
by
  have hjet := hz.1.1 t
  constructor
  · intro x
    have hvalue : (fun y : E3 => z.1.1.1.1 (t, y)) = u := funext hu
    have hfd : HasFDerivAt u (z.1.1.1.2.1 (t, x)) x := by
      simpa only [hvalue] using hjet.1 x
    exact hfd.fderiv.symm
  · intro x
    have hfirst : ∀ y : E3,
        z.1.1.1.2.1 (t, y) = fderiv ℝ u y := by
      intro y
      have hvalue : (fun w : E3 => z.1.1.1.1 (t, w)) = u := funext hu
      have hfd : HasFDerivAt u (z.1.1.1.2.1 (t, y)) y := by
        simpa only [hvalue] using hjet.1 y
      exact hfd.fderiv.symm
    have hderivValue :
        (fun y : E3 => z.1.1.1.2.1 (t, y)) = fderiv ℝ u := funext hfirst
    have hfd : HasFDerivAt (fderiv ℝ u) (z.1.1.1.2.2 (t, x)) x := by
      simpa only [hderivValue] using hjet.2 x
    exact hfd.fderiv.symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.FullJetSpatialIdentification
