import PoincareConjecture.ParallelImplementation.NonzeroFullJetSpatialDerivative
import PoincareConjecture.ParallelImplementation.FullJetJointC1
import PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.ActualGradientJointC1
open PoincareConjecture.ParallelImplementation.FullParabolicJetCompleteness
open PoincareConjecture.ParallelImplementation.ParabolicC2HolderJet
open PoincareConjecture.ParallelImplementation.SlabTimeDerivativeGraph
open PoincareConjecture.ParallelImplementation.FiniteSpatialDifferenceJet
open scoped Topology ContDiff BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
/-- Joint regularity of the ACTUAL spatial derivative of the original field,
not of a separately chosen solution or a formal derivative symbol. -/
theorem actual_spatial_derivatives_joint_c1
    (T alpha : ℝ) (hT : 0 < T) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (z : FullJet T) (hzSpace : z.1.1 ∈ parabolicC2HolderSet T alpha)
    (hzTime : (z.1.1.1.1,z.1.2) ∈ slabTimeDerivativeGraph T)
    (hzInc : ∀ p : Pair T, z.2 p = (parabolicRho p.1.1 p.1.2 ^ alpha)⁻¹ •
      (z.1.2 p.1.1 - z.1.2 p.1.2))
    (C : ℝ) (hC : 0 ≤ C)
    (hquot : ∀ (i : Fin 3) (h : ℝ), h ≠ 0 → ‖finiteSpatialDifferenceJet z i h‖ ≤ C) :
    ∀ v : E3, ContDiffOn ℝ 1
      (fun q : ℝ × E3 => (fderiv ℝ (fun x : E3 => timeExtension z.1.1.1.1 x q.1) q.2) v)
      (Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set E3)) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  intro v
  let U : Set (ℝ × E3) := Set.Ioo (0 : ℝ) T ×ˢ Set.univ
  let e (i : Fin 3) : E3 := EuclideanSpace.single i 1
  let coord (i : Fin 3) : ℝ × E3 → EuclideanSpace ℝ (Fin 6) := fun q =>
    (fderiv ℝ (fun x : E3 => timeExtension z.1.1.1.1 x q.1) q.2) (e i)
  have hcoord : ∀ i : Fin 3, ContDiffOn ℝ 1 (coord i) U := by
    intro i
    obtain ⟨dz, hdz, hnorm, hvalue⟩ :=
      NonzeroFullJetSpatialDerivative.exists_actual_nonzero_spatial_derivative_jet
        T alpha hT ha ha1 z ⟨hzSpace, hzTime, hzInc⟩ i C hC
        (fun h hh => hquot i h hh)
    have hdzSpace : dz.1.1 ∈ parabolicC2HolderSet T alpha := hdz.1
    have hdzTime : (dz.1.1.1.1, dz.1.2) ∈ slabTimeDerivativeGraph T := hdz.2.1
    have hjoint := FullJetJointC1.contDiffOn_one_of_actual_full_jet
      T alpha hT dz hdzSpace hdzTime
    have heq (q : ℝ × E3) (hq : q ∈ U) :
        coord i q = timeExtension dz.1.1.1.1 q.2 q.1 := by
      rcases q with ⟨t,x⟩
      have ht : t ∈ Set.Ioo (0 : ℝ) T := hq.1
      let ts : Set.Icc (0 : ℝ) T := ⟨t, ⟨ht.1.le, ht.2.le⟩⟩
      have hactual : HasFDerivAt (fun y : E3 => z.1.1.1.1 (ts,y))
          (z.1.1.1.2.1 (ts,x)) x := (hzSpace.1 ts).1 x
      have hext : (fun y : E3 => timeExtension z.1.1.1.1 y t) =
          (fun y : E3 => z.1.1.1.1 (ts,y)) := by
        funext y
        simp [timeExtension, ts, Set.mem_Icc, ht.1.le, ht.2.le]
      have hactual' : HasFDerivAt (fun y : E3 => timeExtension z.1.1.1.1 y t)
          (z.1.1.1.2.1 (ts,x)) x := hactual.congr_of_eventuallyEq (Filter.Eventually.of_forall (congrFun hext))
      have hderiv : fderiv ℝ (fun y : E3 => timeExtension z.1.1.1.1 y t) x =
          z.1.1.1.2.1 (ts,x) := hactual'.fderiv
      have hv := hvalue (ts,x)
      have hdzval : timeExtension dz.1.1.1.1 x t = dz.1.1.1.1 (ts,x) := by
        simp [timeExtension, ts, Set.mem_Icc, ht.1.le, ht.2.le]
      change (fderiv ℝ (fun y : E3 => timeExtension z.1.1.1.1 y t) x) (e i) =
        timeExtension dz.1.1.1.1 x t
      rw [hderiv, hdzval, hv]
    exact hjoint.congr fun q hq => heq q hq
  have hvsum : v = ∑ i : Fin 3, (v i) • e i := by
    simpa [e, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v |>.symm
  have hsum : ContDiffOn ℝ 1 (fun q : ℝ × E3 =>
      ∑ i : Fin 3, (v i) • coord i q) U := by
    simpa using (ContDiffOn.sum (s := Finset.univ) (t := U)
      (fun i hi => (hcoord i).const_smul (v i)))
  have heval (q : ℝ × E3) :
      (fderiv ℝ (fun x : E3 => timeExtension z.1.1.1.1 x q.1) q.2) v =
      ∑ i : Fin 3, (v i) • coord i q := by
    calc
      _ = (fderiv ℝ (fun x : E3 => timeExtension z.1.1.1.1 x q.1) q.2)
          (∑ i : Fin 3, (v i) • e i) := congrArg _ hvsum
      _ = ∑ i : Fin 3, (v i) •
          (fderiv ℝ (fun x : E3 => timeExtension z.1.1.1.1 x q.1) q.2) (e i) := by
        simp only [map_sum, map_smul]
      _ = _ := by simp [coord]
  exact hsum.congr fun q hq => heval q
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ActualGradientJointC1
