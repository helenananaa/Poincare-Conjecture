import Mathlib
import PoincareConjecture.ParallelImplementation.SmallC3UnforcedClassicalDeTurck
import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.LocalizedNormalizedC3Extension
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.NormalizedLocalClassicalDeTurck
open scoped Topology BigOperators ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance stdGroup0 : NormedAddCommGroup (E3 →L[ℝ] E6) := inferInstance
local instance stdSpace0 : NormedSpace ℝ (E3 →L[ℝ] E6) := inferInstance
local instance stdGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdGroup2 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance stdSpace2 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.SpaceTimeC2JetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
theorem exists_normalized_local_classical_deturck
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1)
    (u : E3 → E6) (hu : ContDiff ℝ 3 u) (p0 : E3) (hp0 : u p0=0) :

    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i=∑ j : Fin 3, symmetricSixMatrix q i j*v j) ∧
      ∃ r T : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ hT : 0 < T, T ≤ 1 ∧
      ∃ U : E3 → E6, ContDiff ℝ 3 U ∧ HasCompactSupport U ∧
        (∀ x : E3, ‖x‖ ≤ 1 → U x=u (p0+r • x)) ∧
        (∀ x : E3, 2 ≤ ‖x‖ → U x=0) ∧
      ∃ z : FullJet T, z.1.1 ∈ parabolicC2HolderSet T alpha ∧
        (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T ∧
        (∀ x : E3, z.1.1.1.1 (⟨0,le_rfl,hT.le⟩,x)=U x) ∧
        (∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x))) ∧
        (∀ p : Slab T, IsUnit (metricOp E (fun y => z.1.1.1.1 (p.1,y)) p.2) ∧
          ∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 p)) v) v) ∧
        ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ (x : E3) (i j : Fin 3),
          HasDerivAt (fun s : ℝ => (if i=j then 1 else 0)+symmetricSixMatrix (timeExtension z.1.1.1.1 x s) i j)
            (-2*actualRicci E (fun y => z.1.1.1.1 (t,y)) x i j + actualLie E (fun y => z.1.1.1.1 (t,y)) x i j) (t:ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases PoincareConjecture.ParallelImplementation.SmallC3UnforcedClassicalDeTurck.exists_small_c3_unforced_classical_deturck
      alpha ha ha1 with
    ⟨E, hEinj, hEnorm, hEaction, epsilon, delta, C, hepsilon, hdelta,
      hdelta1, hC, hsolution⟩
  obtain ⟨r, hrpos, hrle, U, hU, hUcompact, hUonball, hUzero,
      hU0, hU1, hU2, hU3⟩ :=
    PoincareConjecture.ParallelImplementation.LocalizedNormalizedC3Extension.exists_localized_normalized_c3_extension
      u hu p0 hp0 epsilon hepsilon
  let T : ℝ := delta
  have hTpos : 0 < T := by
    dsimp [T]
    exact hdelta
  have hTle1 : T ≤ 1 := by
    dsimp [T]
    exact hdelta1
  have hTdelta : T ≤ delta := by
    dsimp [T]
    exact le_rfl
  obtain ⟨z, hz, hzgraph, hzinc, hzbound, hzinitial, hzslices,
      hzmetric, hzequation⟩ :=
    hsolution T hTpos hTdelta U hU hU0 hU1 hU2 hU3
  refine ⟨E, hEinj, hEnorm, hEaction, r, T, hrpos, hrle, hTpos, hTle1,
    U, hU, hUcompact, hUonball, hUzero, z, hz, hzgraph, hzinitial,
    hzslices, hzmetric, ?_⟩
  intro t ht0 htT x i j
  simpa [zero_sub] using hzequation t ht0 htT x i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.NormalizedLocalClassicalDeTurck
