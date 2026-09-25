import Mathlib
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
import PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries
import PoincareConjecture.ParallelImplementation.SymmetricSixPacking
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.SymmetricOperatorSixEncoding
open scoped Topology BigOperators ContDiff Manifold BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
theorem exists_symmetric_operator_six_encoding :

    ∃ P : (E3 →L[ℝ] E3) →L[ℝ] E6, ‖P‖ ≤ 3 ∧
      ∀ (E : E6 →L[ℝ] (E3 →L[ℝ] E3)),
        (∀ (q : E6) (v : E3) (i : Fin 3), (E q v) i =
          ∑ j : Fin 3, MorganTianLib.MetricCoefficient.symmetricSixMatrix q i j*v j) →
        ∀ M : E3 →L[ℝ] E3,
          (∀ v w : E3, inner ℝ (M v) w = inner ℝ (M w) v) → E (P M) = M :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  obtain ⟨C, hCnorm, _hCinj, hCentry, _hCidentity, _hCmul⟩ :=
    PoincareConjecture.ParallelImplementation.CoordinateOperatorEntries.exists_operator_entries
  obtain ⟨S, hSnorm, _hScoords, _hSroundtrip, hSsym⟩ :=
    PoincareConjecture.ParallelImplementation.SymmetricSixPacking.exists_symmetric_six_packing
  let P : (E3 →L[ℝ] E3) →L[ℝ] E6 := S.comp C
  have hCaction (M : E3 →L[ℝ] E3) : ‖C M‖ ≤ ‖M‖ := by
    calc
      ‖C M‖ ≤ ‖C‖ * ‖M‖ := C.le_opNorm M
      _ ≤ 1 * ‖M‖ := mul_le_mul_of_nonneg_right hCnorm (norm_nonneg _)
      _ = ‖M‖ := by ring
  have hPnorm : ‖P‖ ≤ 3 := by
    apply ContinuousLinearMap.opNorm_le_bound P (by norm_num)
    intro M
    change ‖S (C M)‖ ≤ 3 * ‖M‖
    calc
      ‖S (C M)‖ ≤ ‖S‖ * ‖C M‖ := S.le_opNorm (C M)
      _ ≤ 3 * ‖C M‖ := mul_le_mul_of_nonneg_right hSnorm (norm_nonneg _)
      _ ≤ 3 * ‖M‖ := mul_le_mul_of_nonneg_left (hCaction M) (by norm_num)
  refine ⟨P, hPnorm, ?_⟩
  intro E hE M hM
  have hentries (i j : Fin 3) : C M i j = C M j i := by
    rw [hCentry M i j, hCentry M j i]
    have h := hM (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
    simpa [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right] using h
  have hround := hSsym (C M) hentries
  have hmat (i j : Fin 3) :
      MorganTianLib.MetricCoefficient.symmetricSixMatrix (P M) i j = C M i j := by
    have h := congrArg (fun A : PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra.Mat => A i j) hround
    simpa [P] using h
  have hexpand (v : E3) :
      v = ∑ j : Fin 3, v j • EuclideanSpace.single j 1 := by
    simpa using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v).symm
  have hMcoord (v : E3) (i : Fin 3) :
      (M v) i = ∑ j : Fin 3, C M i j * v j := by
    calc
      (M v) i = (M (∑ j : Fin 3, v j • EuclideanSpace.single j 1)) i :=
        congrArg (fun x : E3 => (M x) i) (hexpand v)
      _ =
          ∑ j : Fin 3, v j * (M (EuclideanSpace.single j 1)) i := by
        simp
      _ = ∑ j : Fin 3, C M i j * v j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [hCentry]
        ring
  apply ContinuousLinearMap.ext
  intro v
  ext i
  calc
    (E (P M) v) i =
        ∑ j : Fin 3,
          MorganTianLib.MetricCoefficient.symmetricSixMatrix (P M) i j * v j := hE (P M) v i
    _ = ∑ j : Fin 3, C M i j * v j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hmat]
    _ = (M v) i := (hMcoord v i).symm
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.SymmetricOperatorSixEncoding
