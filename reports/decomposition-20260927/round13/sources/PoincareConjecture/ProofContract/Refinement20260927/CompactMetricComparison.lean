import PoincareConjecture.ProofContract.Refinement20260927.SweepoutExtinctionRoot
set_option autoImplicit false
noncomputable section
universe u
namespace PoincareConjecture.ProofContract.Refinement20260927
open Set V1
open scoped Topology
abbrev MetricOperator := Euclidean3 →L[ℝ] Euclidean3
def quadraticValue (A : MetricOperator) (v : Euclidean3) : ℝ := inner ℝ (A v) v
/-- **Math.** Uniform coercivity is a conclusion, not a supplied chart constant. -/
def CompactQuadraticLowerStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (Q : X → MetricOperator), Continuous Q →
    (∀ x v, v ≠ 0 → 0 < quadraticValue (Q x) v) →
    ∃ m : ℝ, 0 < m ∧ ∀ x v, m * ‖v‖^2 ≤ quadraticValue (Q x) v
/-- **Math.** One time radius works for all points of the same compact space.
Continuity is needed only on the actual closed slab, including its endpoints. -/
def CompactMetricTimeVariationStatement : Prop :=
  ∀ (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (Q : ℝ × X → MetricOperator) (a b : ℝ), a ≤ b →
    ContinuousOn Q (Icc a b ×ˢ univ) → ∀ t ∈ Icc a b, ∀ e : ℝ, 0 < e →
    ∃ d : ℝ, 0 < d ∧ ∀ s ∈ Icc a b, dist s t < d →
      ∀ x : X, ‖Q (s,x) - Q (t,x)‖ ≤ e
/-- **Math.** Algebraic perturbation of the SAME quadratic form. -/
theorem quadratic_error (A B : MetricOperator) (v : Euclidean3) :
    |quadraticValue A v - quadraticValue B v| ≤ ‖A-B‖ * ‖v‖^2 := by
  have h : quadraticValue A v - quadraticValue B v = inner ℝ ((A-B) v) v := by
    simp [quadraticValue, inner_sub_left]
  rw [h]
  calc
    |inner ℝ ((A-B) v) v| ≤ ‖(A-B) v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖A-B‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right
      ((A-B).le_opNorm v) (norm_nonneg v)
    _ = _ := by ring
/-- **Math.** The two independent compactness leaves yield one uniform relative
comparison, valid for every vector, chart point and time within the slab. -/
theorem compact_metric_relative (coercive : CompactQuadraticLowerStatement.{u})
    (timeUniform : CompactMetricTimeVariationStatement.{u})
    (X : Type u) [MetricSpace X] [CompactSpace X] [Nonempty X]
    (Q : ℝ × X → MetricOperator) {a b t : ℝ} (hab : a ≤ b)
    (hQ : ContinuousOn Q (Icc a b ×ˢ univ))
    (hpos : ∀ t ∈ Icc a b, ∀ x v, v ≠ 0 → 0 < quadraticValue (Q (t,x)) v)
    (ht : t ∈ Icc a b) {eta : ℝ} (he : 0 < eta) :
    ∃ d : ℝ, 0 < d ∧ ∀ s ∈ Icc a b, dist s t < d → ∀ x v,
      (1-eta)*quadraticValue (Q (t,x)) v ≤ quadraticValue (Q (s,x)) v ∧
      quadraticValue (Q (s,x)) v ≤ (1+eta)*quadraticValue (Q (t,x)) v := by
  have hslice : Continuous (fun x : X => Q (t,x)) :=
    hQ.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨ht,mem_univ x⟩)
  obtain ⟨m,hm,hlower⟩ := coercive X (fun x => Q (t,x)) hslice (hpos t ht)
  obtain ⟨d,hd,hclose⟩ := timeUniform X Q a b hab hQ t ht (m*eta) (mul_pos hm he)
  refine ⟨d,hd,?_⟩
  intro s hs hst x v
  have herr := quadratic_error (Q (s,x)) (Q (t,x)) v
  have hop := mul_le_mul_of_nonneg_right (hclose s hs hst x) (sq_nonneg ‖v‖)
  have hrel := mul_le_mul_of_nonneg_left (hlower x v) he.le
  have hbound : |quadraticValue (Q (s,x)) v-quadraticValue (Q (t,x)) v| ≤
      eta*quadraticValue (Q (t,x)) v := by nlinarith [herr,hop,hrel]
  have hb := abs_le.mp hbound
  constructor <;> nlinarith [hb.1,hb.2]
#print axioms quadratic_error
#print axioms compact_metric_relative
end PoincareConjecture.ProofContract.Refinement20260927
