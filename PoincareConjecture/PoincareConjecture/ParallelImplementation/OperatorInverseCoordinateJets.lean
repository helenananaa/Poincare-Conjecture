import PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries
import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.SymmetricSixRealization
import PoincareConjecture.ParallelImplementation.OperatorInverseLocalDerivative
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.OperatorInverseCoordinateJets
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem inverse_coordinate_jets
    (g : E3 → (E3 →L[ℝ] E3)) (g' : E3 →L[ℝ] (E3 →L[ℝ] E3))
    (x : E3) (hg : HasFDerivAt g g' x) (hunit : IsUnit (g x)) :

    let G : E3 → Mat := fun y i j => (g y (EuclideanSpace.single j 1)) i
    let H : E3 → Mat := fun y i j => (Ring.inverse (g y) (EuclideanSpace.single j 1)) i
    ∃ dh : Idx → Mat,
      (∀ a i j, HasDerivAt (fun t : ℝ => H (x + t • EuclideanSpace.single a 1) i j) (dh a i j) 0) ∧
      (∀ a : Idx, ∀ᶠ t : ℝ in 𝓝 0, ∀ i j : Idx,
        (∑ k : Idx, G (x + t • EuclideanSpace.single a 1) i k * H (x + t • EuclideanSpace.single a 1) k j) = if i = j then 1 else 0) ∧
      (∀ i j : Idx, (∑ k : Idx, H x i k * G x k j) = if i = j then 1 else 0) :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  dsimp only
  rcases PoincareConjecture.ParallelImplementation.OperatorInverseLocalDerivative.operator_inverse_local_derivative
      g g' x hg hunit with ⟨⟨D, hD, hD_formula⟩, hIdentities⟩
  rcases PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries.exists_operator_entries with
    ⟨C, hC_norm, hC_injective, hC_entries, hC_one, hC_mul⟩
  let dh : Idx → Mat := fun a i j =>
    (D (EuclideanSpace.single a 1)) (EuclideanSpace.single j 1) i
  refine ⟨dh, ?_, ?_, ?_⟩
  · intro a i j
    let v : E3 := EuclideanSpace.single a 1
    let e : E3 := EuclideanSpace.single j 1
    let line : ℝ → E3 := fun t => x + t • v
    have hline : HasDerivAt line v 0 := by
      simpa [line, v] using
        ((hasDerivAt_id' (0 : ℝ)).smul_const (EuclideanSpace.single a (1 : ℝ))).const_add x
    have hinvLine : HasDerivAt (fun t : ℝ => Ring.inverse (g (line t))) (D v) 0 := by
      have hDline : HasFDerivAt (fun y : E3 => Ring.inverse (g y)) D (line 0) := by
        simpa [line] using hD
      have h :=
        (HasFDerivAt.comp (f := line) (x := (0 : ℝ)) hDline hline.hasFDerivAt).hasDerivAt
      simpa [line, Function.comp_def] using h
    have hinvApply : HasDerivAt
        (fun t : ℝ => (Ring.inverse (g (line t))) e) ((D v) e) 0 := by
      have h := hinvLine.clm_apply (hasDerivAt_const (c := e) (x := (0 : ℝ)))
      simpa using h
    have hcoord : HasDerivAt
        (fun t : ℝ => ((Ring.inverse (g (line t))) e) i) (((D v) e) i) 0 := by
      let proj : E3 →L[ℝ] ℝ := PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) i
      have hproj : HasFDerivAt (fun w : E3 => proj w) proj
          ((Ring.inverse (g (line 0))) e) := proj.hasFDerivAt
      have h := (HasFDerivAt.comp
        (f := fun t : ℝ => (Ring.inverse (g (line t))) e) (x := (0 : ℝ))
        hproj hinvApply.hasFDerivAt).hasDerivAt
      simpa [Function.comp_def, proj, PiLp.proj, PiLp.projₗ, line] using h
    simpa [dh, v, e, line] using hcoord
  · intro a
    let line : ℝ → E3 := fun t => x + t • EuclideanSpace.single a 1
    have hline_tendsto : Filter.Tendsto line (𝓝 0) (𝓝 x) := by
      have hline_deriv : HasDerivAt line (EuclideanSpace.single a (1 : ℝ)) 0 := by
        simpa [line] using
          ((hasDerivAt_id' (0 : ℝ)).smul_const (EuclideanSpace.single a (1 : ℝ))).const_add x
      simpa [line] using hline_deriv.continuousAt.tendsto
    filter_upwards [hline_tendsto.eventually hIdentities] with t ht
    intro i j
    calc
      (∑ k : Idx,
          (g (line t) (EuclideanSpace.single k 1)) i *
            (Ring.inverse (g (line t)) (EuclideanSpace.single j 1)) k) =
          C (g (line t) * Ring.inverse (g (line t))) i j := by
        rw [hC_mul]
        simp_rw [hC_entries]
      _ = C 1 i j := congrArg (fun A : E3 →L[ℝ] E3 => C A i j) ht.1
      _ = if i = j then 1 else 0 := by rw [hC_one]
  · intro i j
    have hInvG : Ring.inverse (g x) * g x = 1 :=
      (Ring.isUnit_iff_inverse_mul_cancel (g x)).mp hunit
    have h := congrArg (fun A : E3 →L[ℝ] E3 => C A i j)
      hInvG
    calc
      (∑ k : Idx,
          (Ring.inverse (g x) (EuclideanSpace.single k 1)) i *
            (g x (EuclideanSpace.single j 1)) k) = C (Ring.inverse (g x) * g x) i j := by
        rw [hC_mul]
        simp_rw [hC_entries]
      _ = C 1 i j := h
      _ = if i = j then 1 else 0 := by rw [hC_one]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.OperatorInverseCoordinateJets
