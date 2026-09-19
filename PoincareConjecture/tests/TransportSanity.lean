import PoincareConjecture.ParallelMath.Transport.RelativeGramArea
import PoincareConjecture.ParallelMath.Transport.MinmaxLocal
import PoincareConjecture.ParallelMath.Transport.ExtendedInfimum
import PoincareConjecture.ParallelMath.Transport.TorusUniversal

noncomputable section
open scoped ENNReal
open Set
open PoincareConjecture.ParallelMath.Transport
open PoincareConjecture.ParallelMath.Variational
open PoincareConjecture.Topology.FiberSaturation
namespace TransportSanity

/-- A nonzero rank-one reference form is allowed; neither determinant is positive. -/
example : (1-(1/4 : ℝ))*Real.sqrt (1*1-1^2) ≤
      Real.sqrt ((5/4 : ℝ)*(5/4)-(5/4)^2) ∧
    Real.sqrt ((5/4 : ℝ)*(5/4)-(5/4)^2) ≤ (1+(1/4 : ℝ))*Real.sqrt (1*1-1^2) := by
  apply relative_gram_area_distortion 1 1 1 (5/4) (5/4) (5/4) (1/4)
    (by norm_num) (by norm_num)
  · intro s t
    nlinarith [sq_nonneg (s+t)]
  · intro s t
    constructor <;> nlinarith [sq_nonneg (s+t)]

/-- The empty admissible class remains at infinity, not the junk real infimum zero. -/
example : (2 : ℝ≥0∞)*(⨅ _a : Empty, (3 : ℝ≥0∞)) ≤ (⨅ _a : Empty, (4 : ℝ≥0∞)) ∧
    (⨅ _a : Empty, (4 : ℝ≥0∞)) ≤ (5 : ℝ≥0∞)*(⨅ _a : Empty, (3 : ℝ≥0∞)) := by
  apply ennreal_infimum_twoSided (fun _a : Empty => 3) (fun _a : Empty => 4)
    2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  intro a
  exact a.elim

/-- Infimum zero is approached but not attained. -/
theorem positive_cost_inf : leastCost (fun x : Ioi (0 : ℝ) => (x : ℝ)) = 0 := by
  unfold leastCost
  have h : range (fun x : Ioi (0 : ℝ) => (x : ℝ)) = Ioi (0 : ℝ) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  rw [h]
  exact csInf_Ioi

example : ¬ ∃ x : Ioi (0 : ℝ), (x : ℝ) = 0 := by
  rintro ⟨x,hx⟩
  exact (ne_of_gt x.property) hx

/-- The minmax result applies on an actual closed slab and needs no attained minimum. -/
example : ContinuousOn (fun _t : ℝ =>
    leastPeak (fun x : Ioi (0 : ℝ) => fun _j : Unit => (x : ℝ))) (Icc (0 : ℝ) 1) := by
  letI : Nonempty (Ioi (0 : ℝ)) := ⟨⟨1, by norm_num⟩⟩
  apply leastPeak_continuousOn_from_derivative_bounds
    (fun (x : Ioi (0 : ℝ)) (_j : Unit) (_t : ℝ) => (x : ℝ))
    (fun (_x : Ioi (0 : ℝ)) (_j : Unit) (_t : ℝ) => 0) 0 1 0 (by norm_num)
  · intro x j
    exact continuous_const.continuousOn
  · intro x j t ht
    exact x.property.le
  · intro x j t ht
    exact hasDerivAt_const t (x : ℝ)
  · intro x j t ht
    simp
  · intro x t ht
    refine ⟨x.1, ?_⟩
    rintro y ⟨j, rfl⟩
    exact le_rfl

/-- A nonempty example of the actual simply connected covering construction. -/
example : IsCoveringMap (MappingTorus.proj (Homeomorph.refl Unit) (1 : ℝ)) ∧
    SimplyConnectedSpace (Unit × ℝ) := by
  have h := mappingTorus_universal_cover_data (Homeomorph.refl Unit) 1 (by norm_num)
  exact ⟨h.1, h.2.1⟩
end TransportSanity
