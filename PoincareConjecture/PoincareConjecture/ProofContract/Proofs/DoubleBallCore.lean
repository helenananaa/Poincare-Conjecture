import PoincareConjecture.ProofContract.V1.Obligations

/-! Concrete hemisphere coordinates for a recursive double-ball construction.
No sphere-recognition or quotient-homeomorphism conclusion is assumed here. -/
noncomputable section
namespace PoincareConjecture.ProofContract.Proofs.DoubleBall
open V1 Set

abbrev E4 := EuclideanSpace ℝ (Fin 4)
abbrev Ball := Metric.closedBall (0 : Euclidean3) 1

def boundary (s : Sphere2) : Ball := ⟨s, le_of_eq s.property⟩

def seam (h : Sphere2 ≃ₜ Sphere2) (x y : Ball ⊕ Ball) : Prop :=
  ∃ s : Sphere2, x = Sum.inl (boundary s) ∧ y = Sum.inr (boundary (h s))

abbrev Space (h : Sphere2 ≃ₜ Sphere2) := Quot (seam h)

def tail (x : E4) : Euclidean3 := WithLp.toLp 2 (fun i => x i.succ)

def raw (upper : Bool) (x : Ball) : E4 :=
  WithLp.toLp 2 (Fin.cases
    ((if upper then (1 : ℝ) else -1) * Real.sqrt (1 - ‖(x : Euclidean3)‖ ^ 2))
    (fun i => (x : Euclidean3) i))

@[simp] theorem tail_raw (upper : Bool) (x : Ball) :
    tail (raw upper x) = (x : Euclidean3) := by
  ext i
  rfl

/-- Euclidean norm split into the first coordinate and the remaining three. -/
theorem norm_sq_split (x : E4) : ‖x‖ ^ 2 = (x 0) ^ 2 + ‖tail x‖ ^ 2 := by
  simp only [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, tail]

end PoincareConjecture.ProofContract.Proofs.DoubleBall
