import PoincareConjecture.ParallelImplementation.ParabolicForcingSpace
import PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import PoincareConjecture.ParallelImplementation.BoundedC3InitialHolderJets
import PoincareConjecture.ParallelImplementation.SmallInitialClassicalDeTurckSolution
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SmallC3UnforcedClassicalDeTurck
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
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
local instance derivativeGroup0 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance derivativeSpace0 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance derivativeGroup1 : NormedAddCommGroup (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
local instance derivativeSpace1 : NormedSpace ℝ (E3 →L[ℝ] E3 →L[ℝ] E3 →L[ℝ] E6) := inferInstance
theorem exists_small_c3_unforced_classical_deturck
    (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha < 1) :

    ∃ E : E6 →L[ℝ] (E3 →L[ℝ] E3), Function.Injective E ∧ ‖E‖ ≤ 3 ∧
      (∀ (q : E6) (v : E3) (i : Idx), (E q v) i=∑ j : Idx, symmetricSixMatrix q i j*v j) ∧
      ∃ epsilon delta C : ℝ, 0 < epsilon ∧ 0 < delta ∧ delta ≤ 1 ∧ 0 < C ∧
        ∀ (T : ℝ) (hT : 0 < T), T ≤ delta →
        ∀ (u : E3 → E6), ContDiff ℝ 3 u →
          (∀ x : E3, ‖u x‖ ≤ epsilon) →
          (∀ x : E3, ‖fderiv ℝ u x‖ ≤ epsilon) →
          (∀ x : E3, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ epsilon) →
          (∀ x : E3, ‖fderiv ℝ (fderiv ℝ (fderiv ℝ u)) x‖ ≤ epsilon) →
          ∃ z : FullJet T, z.1.1 ∈ parabolicC2HolderSet T alpha ∧
            (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T ∧
            (∀ p : Pair T, z.2 p=(parabolicRho p.1.1 p.1.2^alpha)⁻¹ • (z.1.2 p.1.1-z.1.2 p.1.2)) ∧
            ‖z‖ ≤ C ∧ (∀ x : E3, z.1.1.1.1 (⟨0,le_rfl,hT.le⟩,x)=u x) ∧
            (∀ t : Set.Icc (0:ℝ) T, ContDiff ℝ 2 (fun x : E3 => z.1.1.1.1 (t,x))) ∧
            (∀ p : Slab T, IsUnit (metricOp E (fun y => z.1.1.1.1 (p.1,y)) p.2) ∧
              ∀ v : E3, (1/2:ℝ)*‖v‖^2 ≤ inner ℝ ((1+E (z.1.1.1.1 p)) v) v) ∧
            ∀ t : Set.Icc (0:ℝ) T, 0 < (t:ℝ) → (t:ℝ) < T → ∀ (x : E3) (i j : Idx),
              HasDerivAt (fun s : ℝ => (if i=j then 1 else 0)+symmetricSixMatrix (timeExtension z.1.1.1.1 x s) i j)
                (0 - 2*actualRicci E (fun y => z.1.1.1.1 (t,y)) x i j +
                  actualLie E (fun y => z.1.1.1.1 (t,y)) x i j) (t:ℝ) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  rcases PoincareConjecture.ParallelImplementation.SmallInitialClassicalDeTurckSolution.exists_small_initial_classical_deturck_solution
      alpha ha ha1 with
    ⟨E, hEinj, hEnorm, hEaction, epsilon, delta, C, hepsilon, hdelta,
      hdelta1, hC, hsolution⟩
  let epsilon' : ℝ := epsilon / 3
  have hepsilon' : 0 < epsilon' := by
    dsimp [epsilon']
    positivity
  refine ⟨E, hEinj, hEnorm, hEaction, epsilon', delta, C, hepsilon',
    hdelta, hdelta1, hC, ?_⟩
  intro T hT hTdelta u hu h0 h1 h2 h3
  have hM : 0 ≤ epsilon' := le_of_lt hepsilon'
  obtain ⟨u0, A0, H0, hvalues, hu0deriv, hA0deriv,
      hu0norm, hA0norm, hH0norm, hu0holder, hA0holder, hH0holder⟩ :=
    PoincareConjecture.ParallelImplementation.BoundedC3InitialHolderJets.exists_bounded_c3_initial_holder_jets
      u hu epsilon' alpha hM ha (by linarith [ha1])
      (fun x => by simpa [epsilon'] using h0 x)
      (fun x => by simpa [epsilon'] using h1 x)
      (fun x => by simpa [epsilon'] using h2 x)
      (fun x => by simpa [epsilon'] using h3 x)
  let F : ForcingJet E6 T := (0, 0)
  have hFgraph : F ∈ forcingGraph E6 T alpha := by
    intro p
    simp [F]
  have hFnorm : ‖F‖ ≤ 1 := by simp [F]
  have hscale : 3 * epsilon' = epsilon := by
    dsimp [epsilon']
    ring
  obtain ⟨z, hz, hztimeGraph, hzinc, hzbound, hzinitial, hzslices,
      hzmetric, hzequation⟩ :=
    hsolution T hT hTdelta u0 A0 H0 hu0deriv hA0deriv
      (by linarith [hu0norm, hscale])
      (by linarith [hA0norm, hscale])
      (by linarith [hH0norm, hscale])
      (by intro x y; rw [← hscale]; exact hu0holder x y)
      (by intro x y; rw [← hscale]; exact hA0holder x y)
      (by intro x y; rw [← hscale]; exact hH0holder x y)
      F hFgraph hFnorm
  refine ⟨z, hz, hztimeGraph, hzinc, hzbound, ?_, hzslices, hzmetric, ?_⟩
  · intro x
    rw [hzinitial x]
    exact (hvalues x).1
  · intro t ht0 htT x i j
    have hzero : symmetricSixMatrix (0 : E6) i j = 0 := by
      fin_cases i <;> fin_cases j <;> simp [symmetricSixMatrix]
    simpa [F, hzero] using hzequation t ht0 htT x i j
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SmallC3UnforcedClassicalDeTurck
