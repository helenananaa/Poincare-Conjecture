import PoincareConjecture.ParallelMath.Variational.AreaToWidth
import PoincareConjecture.ParallelMath.Variational.MinmaxContinuity
import ReferenceBridges.WidthTorus.TwistedBundle
open Set
open PoincareConjecture.ParallelMath.Variational
open PoincareConjecture.ParallelMath.TorusObstruction
open PoincareConjecture.Topology.FiberSaturation
noncomputable section
namespace WidthTorusSanity
/-- The positive ray has infimum zero without any point realizing it. -/
theorem nonattained_cost : leastCost (fun x : Ioi (0 : ℝ) => (x : ℝ)) = 0 := by
  unfold leastCost
  have h : range (fun x : Ioi (0 : ℝ) => (x : ℝ)) = Ioi (0 : ℝ) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x,hx⟩,rfl⟩⟩
  rw [h]
  exact csInf_Ioi
example : ¬ ∃ x : Ioi (0 : ℝ), (x : ℝ) = 0 := by
  rintro ⟨x,hx⟩
  exact (ne_of_gt x.property) hx
example : leastPeak (fun x : Ioi (0 : ℝ) => fun _ : Unit => (x : ℝ)) = 0 := by
  simpa [leastPeak, peakCost] using nonattained_cost
example : ¬ SimplyConnectedSpace (MappingTorus.Space (Homeomorph.refl PUnit) 1) :=
  mappingTorus_not_simplyConnected _
example : 1 ≤ Real.sqrt ((1 : ℝ)*1-0^2) ∧ Real.sqrt ((1 : ℝ)*1-0^2) ≤ 1 := by
  norm_num
end WidthTorusSanity
