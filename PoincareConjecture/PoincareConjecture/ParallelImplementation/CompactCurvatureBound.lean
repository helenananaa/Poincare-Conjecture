import MorganTianLib.Ch01.CurvatureNormManifold
import MorganTianLib.Ch01.MetricRescaling
import MorganTianLib.Ch01.OrthoFrame
import MorganTianLib.Ch03.RicciFlow.ScalarCurvatureSmooth

/-!
# Compact bounds for curvature in local orthonormal frames

For each centre `a`, Morgan--Tian's smooth local frame is globally extended as
smooth vector fields and is orthonormal on `orthoFrameSet a`. The curvature
pairing of these fields is a smooth scalar function on the manifold. Compactness
bounds each such scalar function; a finite subcover by the frame neighbourhoods
then gives one bound for all frame components at all points.

This is a geometric compactness estimate on the actual Levi-Civita curvature.
The final conversion from uniform frame-component bounds to the Rayleigh
inequality `HasCurvatureOperatorNormLeAt` is kept separate here and remains the
next algebraic adapter.
-/

open Bundle Set
open scoped ContDiff Manifold Topology Bundle
open Riemannian

noncomputable section

namespace PoincareConjecture.ParallelImplementation.CompactCurvatureBound

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [I.Boundaryless]

/-- **Math.** The curvature component read in the smooth local orthonormal frame based at
`a`. Away from its orthonormality neighbourhood this is still the genuine
curvature pairing of the globally smooth frame fields. -/
def frameCurvatureComponent (g : RiemannianMetric I M) (a : M)
    (i j k l : Fin (Module.finrank ℝ E)) (q : M) : ℝ :=
  g.leviCivitaConnection.curvatureForm g
    (MorganTianLib.orthoFrameField g a i)
    (MorganTianLib.orthoFrameField g a j)
    (MorganTianLib.orthoFrameField g a k)
    (MorganTianLib.orthoFrameField g a l) q

omit [I.Boundaryless] in
theorem continuous_frameCurvatureComponent (g : RiemannianMetric I M)
    (a : M) (i j k l : Fin (Module.finrank ℝ E)) :
    Continuous (frameCurvatureComponent g a i j k l) := by
  exact (MorganTianLib.curvatureForm_contMDiff g g.leviCivitaConnection
    (MorganTianLib.orthoFrameField g a i)
    (MorganTianLib.orthoFrameField g a j)
    (MorganTianLib.orthoFrameField g a k)
    (MorganTianLib.orthoFrameField g a l)).continuous

/-- **Math.** The smooth-field component is the pointwise
curvature tensor applied to the actual frame vectors. -/
theorem frameCurvatureComponent_eq_curvatureFormAt
    (g : RiemannianMetric I M) (a q : M)
    (i j k l : Fin (Module.finrank ℝ E)) :
    frameCurvatureComponent g a i j k l q =
      MorganTianLib.curvatureFormAt g g.leviCivitaConnection q
        (MorganTianLib.orthoFrameField g a i q)
        (MorganTianLib.orthoFrameField g a j q)
        (MorganTianLib.orthoFrameField g a k q)
        (MorganTianLib.orthoFrameField g a l q) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change g.leviCivitaConnection.curvatureForm g
      (MorganTianLib.orthoFrameField g a i)
      (MorganTianLib.orthoFrameField g a j)
      (MorganTianLib.orthoFrameField g a k)
      (MorganTianLib.orthoFrameField g a l) q = _
  exact (MorganTianLib.curvatureFormAt_eq g g.leviCivitaConnection
    (MorganTianLib.orthoFrameField g a i)
    (MorganTianLib.orthoFrameField g a j)
    (MorganTianLib.orthoFrameField g a k)
    (MorganTianLib.orthoFrameField g a l) q).symm

omit [I.Boundaryless] in
/-- **Math.** A compact bound for one component of the curvature in the frame based at
`a`. The bound is defined from compactness of the range of the continuous
absolute-value function. -/
theorem exists_frameCurvatureComponent_bound (g : RiemannianMetric I M)
    (a : M) (i j k l : Fin (Module.finrank ℝ E)) :
    ∃ C : ℝ, ∀ q : M, |frameCurvatureComponent g a i j k l q| ≤ C := by
  obtain ⟨C, hC⟩ := IsCompact.exists_bound_of_continuousOn
    (isCompact_univ : IsCompact (Set.univ : Set M))
    ((continuous_abs.comp (continuous_frameCurvatureComponent g a i j k l)).continuousOn)
  refine ⟨C, ?_⟩
  intro q
  have hq := hC q (Set.mem_univ q)
  simpa only [Real.norm_eq_abs, abs_abs, Function.comp_apply] using hq

noncomputable def frameCurvatureComponentBound (g : RiemannianMetric I M)
    (a : M) (i j k l : Fin (Module.finrank ℝ E)) : ℝ :=
  Classical.choose (exists_frameCurvatureComponent_bound g a i j k l)

omit [I.Boundaryless] in
theorem frameCurvatureComponent_le_bound (g : RiemannianMetric I M)
    (a : M) (i j k l : Fin (Module.finrank ℝ E)) (q : M) :
    |frameCurvatureComponent g a i j k l q| ≤
      frameCurvatureComponentBound g a i j k l := by
  exact Classical.choose_spec (exists_frameCurvatureComponent_bound g a i j k l) q

omit [I.Boundaryless] in
theorem frameCurvatureComponentBound_nonneg (g : RiemannianMetric I M)
    (a : M) (i j k l : Fin (Module.finrank ℝ E)) (hM : Nonempty M) :
    0 ≤ frameCurvatureComponentBound g a i j k l := by
  obtain ⟨q⟩ := hM
  exact (abs_nonneg _).trans (frameCurvatureComponent_le_bound g a i j k l q)

/-- **Math.** Add the finitely many individual compact component bounds in the frame
based at `a`. This single nonnegative number bounds every component of that
frame on all of `M`. -/
noncomputable def frameCurvatureComponentSumBound
    (g : RiemannianMetric I M) (a : M) : ℝ :=
  ∑ i : Fin (Module.finrank ℝ E),
    ∑ j : Fin (Module.finrank ℝ E),
      ∑ k : Fin (Module.finrank ℝ E),
        ∑ l : Fin (Module.finrank ℝ E),
          frameCurvatureComponentBound g a i j k l

omit [I.Boundaryless] in
theorem frameCurvatureComponentSumBound_nonneg (g : RiemannianMetric I M)
    (a : M) (hM : Nonempty M) : 0 ≤ frameCurvatureComponentSumBound g a := by
  unfold frameCurvatureComponentSumBound
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro k hk
  apply Finset.sum_nonneg
  intro l hl
  exact frameCurvatureComponentBound_nonneg g a i j k l hM

omit [I.Boundaryless] in
theorem frameCurvatureComponent_le_sumBound (g : RiemannianMetric I M)
    (a : M) (hM : Nonempty M) (i j k l : Fin (Module.finrank ℝ E)) :
    frameCurvatureComponentBound g a i j k l ≤ frameCurvatureComponentSumBound g a := by
  unfold frameCurvatureComponentSumBound
  calc
    frameCurvatureComponentBound g a i j k l ≤
        ∑ l' : Fin (Module.finrank ℝ E),
          frameCurvatureComponentBound g a i j k l' :=
      Finset.single_le_sum
        (fun l' _ => frameCurvatureComponentBound_nonneg g a i j k l' hM)
        (Finset.mem_univ l)
    _ ≤ ∑ k' : Fin (Module.finrank ℝ E),
          ∑ l' : Fin (Module.finrank ℝ E),
            frameCurvatureComponentBound g a i j k' l' :=
      Finset.single_le_sum
        (fun k' _ => Finset.sum_nonneg fun l' _ =>
          frameCurvatureComponentBound_nonneg g a i j k' l' hM)
        (Finset.mem_univ k)
    _ ≤ ∑ j' : Fin (Module.finrank ℝ E),
          ∑ k' : Fin (Module.finrank ℝ E),
            ∑ l' : Fin (Module.finrank ℝ E),
              frameCurvatureComponentBound g a i j' k' l' :=
      Finset.single_le_sum
        (fun j' _ => Finset.sum_nonneg fun k' _ => Finset.sum_nonneg fun l' _ =>
          frameCurvatureComponentBound_nonneg g a i j' k' l' hM)
        (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin (Module.finrank ℝ E),
          ∑ j' : Fin (Module.finrank ℝ E),
            ∑ k' : Fin (Module.finrank ℝ E),
              ∑ l' : Fin (Module.finrank ℝ E),
                frameCurvatureComponentBound g a i' j' k' l' :=
      Finset.single_le_sum
        (fun i' _ => Finset.sum_nonneg fun j' _ => Finset.sum_nonneg fun k' _ =>
          Finset.sum_nonneg fun l' _ =>
            frameCurvatureComponentBound_nonneg g a i' j' k' l' hM)
        (Finset.mem_univ i)

/-- **Math.** **Uniform compact frame-component bound.** There is one nonnegative
constant `C` such that at each point `q` one can choose a local orthonormal
frame whose actual Levi-Civita curvature components all have absolute value
at most `C`.

The frame may depend on `q`, as local orthonormal frames need not globalize.
Compactness is used through a finite subcover of the frame neighbourhoods and
compact boundedness of every smooth curvature component. -/
theorem exists_compact_uniform_curvature_frame_component_bound
    (g : RiemannianMetric I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q : M,
      ∃ a : M, q ∈ MorganTianLib.orthoFrameSet (I := I) (M := M) a ∧
        ∀ i j k l : Fin (Module.finrank ℝ E),
          |MorganTianLib.curvatureFormAt g g.leviCivitaConnection q
              (MorganTianLib.orthoFrameField g a i q)
              (MorganTianLib.orthoFrameField g a j q)
              (MorganTianLib.orthoFrameField g a k q)
              (MorganTianLib.orthoFrameField g a l q)| ≤ C := by
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    obtain ⟨centres, hcover⟩ :=
      (isCompact_univ : IsCompact (Set.univ : Set M)).elim_finite_subcover
        (fun a => MorganTianLib.orthoFrameSet (I := I) (M := M) a)
        (fun a => MorganTianLib.isOpen_orthoFrameSet (I := I) (M := M) a)
        (by
          intro q hq
          refine Set.mem_iUnion.mpr ⟨q, ?_⟩
          exact MorganTianLib.mem_orthoFrameSet_self (I := I) (M := M) q)
    let C : ℝ := centres.sum (fun a => frameCurvatureComponentSumBound g a)
    have hC : 0 ≤ C := by
      dsimp [C]
      exact Finset.sum_nonneg fun a _ =>
        frameCurvatureComponentSumBound_nonneg g a hM
    refine ⟨C, hC, ?_⟩
    intro q
    have hqcov : q ∈ ⋃ a ∈ centres,
        MorganTianLib.orthoFrameSet (I := I) (M := M) a :=
      hcover (Set.mem_univ q)
    simp only [Set.mem_iUnion] at hqcov
    rcases hqcov with ⟨a, ha, hqa⟩
    refine ⟨a, hqa, ?_⟩
    intro i j k l
    rw [← frameCurvatureComponent_eq_curvatureFormAt g a q i j k l]
    calc
      |frameCurvatureComponent g a i j k l q| ≤
          frameCurvatureComponentBound g a i j k l :=
        frameCurvatureComponent_le_bound g a i j k l q
      _ ≤ frameCurvatureComponentSumBound g a :=
        frameCurvatureComponent_le_sumBound g a hM i j k l
      _ ≤ C := by
        dsimp [C]
        exact Finset.single_le_sum
          (fun b _ => frameCurvatureComponentSumBound_nonneg g b hM) ha
  · refine ⟨0, le_rfl, ?_⟩
    intro q
    exact (hM ⟨q⟩).elim

#print axioms exists_compact_uniform_curvature_frame_component_bound

end PoincareConjecture.ParallelImplementation.CompactCurvatureBound

end
