import MorganTianLib.Ch03.RicciFlow.PDE.MetricCoefficients.ConnectionDifferenceFiber
import MorganTianLib.Ch01.InvGramTrace
import MorganTianLib.Ch01.RicciFrame
import Mathlib
set_option autoImplicit false
noncomputable section
namespace MorganTianLib.MetricCoefficient
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators RealInnerProductSpace Manifold Bundle Matrix BoundedContinuousFunction
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "T3" => Fin 3 → Fin 3 → Fin 3 → ℝ
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩

/-- **Math.** exists global connection difference trace. -/
theorem exists_global_connection_difference_trace {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
    [SigmaCompactSpace M] [T2Space M]
    (g : Riemannian.RiemannianMetric (𝓡 3) M)
    (nabla nabla0 : Riemannian.AffineConnection (𝓡 3) M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) := ⟨g.toRiemannianMetric⟩;
    ∃ W : Riemannian.SmoothVectorField (𝓡 3) M, ∀ p : M,
      let e := stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) p);
      W p = ∑ i, connectionDifferenceField nabla nabla0
        (MorganTianLib.extendVector p (e i)) (MorganTianLib.extendVector p (e i)) p :=
/- SWARM_PROOF_BEGIN -/
by
  classical
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : AddCommMonoid (Riemannian.SmoothVectorField (𝓡 3) M) := {
    add_assoc a b c := Riemannian.SmoothVectorField.ext fun q => add_assoc (a q) (b q) (c q)
    zero_add a := Riemannian.SmoothVectorField.ext fun q => zero_add (a q)
    add_zero a := Riemannian.SmoothVectorField.ext fun q => add_zero (a q)
    add_comm a b := Riemannian.SmoothVectorField.ext fun q => add_comm (a q) (b q)
    nsmul := nsmulRec }
  let trace : ∀ q : M, TangentSpace (𝓡 3) q := fun q =>
    ∑ i, connectionDifferenceField nabla nabla0
      (MorganTianLib.extendVector q
        (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) q) i))
      (MorganTianLib.extendVector q
        (stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) q) i)) q
  have sum_apply (s : Finset (Fin (Module.finrank ℝ E3)))
      (F : Fin (Module.finrank ℝ E3) → Riemannian.SmoothVectorField (𝓡 3) M) (q : M) :
      (∑ i ∈ s, F i) q = ∑ i ∈ s, F i q := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Riemannian.SmoothVectorField.add_apply, ih]
  let frameSum : M → Riemannian.SmoothVectorField (𝓡 3) M := fun p =>
    ∑ i : Fin (Module.finrank ℝ E3),
      connectionDifferenceField nabla nabla0
        (MorganTianLib.orthoFrameField g p i) (MorganTianLib.orthoFrameField g p i)
  have frameSum_apply (p q : M) :
      frameSum p q = ∑ i : Fin (Module.finrank ℝ E3),
        connectionDifferenceField nabla nabla0
          (MorganTianLib.orthoFrameField g p i) (MorganTianLib.orthoFrameField g p i) q := by
    dsimp [frameSum]
    simpa using sum_apply (Finset.univ : Finset (Fin (Module.finrank ℝ E3)))
      (fun i : Fin (Module.finrank ℝ E3) => connectionDifferenceField nabla nabla0
        (MorganTianLib.orthoFrameField g p i) (MorganTianLib.orthoFrameField g p i)) q
  have trace_eq_frame (p q : M)
      (hq : q ∈ MorganTianLib.orthoFrameSet (I := 𝓡 3) (M := M) p) :
      trace q = ∑ i : Fin (Module.finrank ℝ E3),
        connectionDifferenceField nabla nabla0
          (MorganTianLib.orthoFrameField g p i) (MorganTianLib.orthoFrameField g p i) q := by
    obtain ⟨D, hD⟩ := connection_difference_fiber_bilinear nabla nabla0 q
    let eStd := stdOrthonormalBasis ℝ (TangentSpace (𝓡 3) q)
    let eFrame := MorganTianLib.orthoFrameBasis g p hq
    have hdim : Module.finrank ℝ E3 = Module.finrank ℝ (TangentSpace (𝓡 3) q) := rfl
    let e : OrthonormalBasis (Fin (Module.finrank ℝ E3)) ℝ
        (TangentSpace (𝓡 3) q) := eStd.reindex (finCongr hdim).symm
    have hstd : trace q = ∑ j, D (eStd j) (eStd j) := by
      dsimp [trace]
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa only [MorganTianLib.extendVector_apply] using
        (hD (MorganTianLib.extendVector q (eStd i))
          (MorganTianLib.extendVector q (eStd i))).symm
    have hreindex : (∑ i : Fin (Module.finrank ℝ E3), D (e i) (e i)) =
        ∑ j : Fin (Module.finrank ℝ (TangentSpace (𝓡 3) q)), D (eStd j) (eStd j) := by
      refine Fintype.sum_equiv (finCongr hdim) _ _ ?_
      intro i
      change D (eStd i) (eStd i) = D (eStd i) (eStd i)
      rfl
    have hgram : ∀ a b : Fin (Module.finrank ℝ E3),
        (1 : Matrix (Fin (Module.finrank ℝ E3)) (Fin (Module.finrank ℝ E3)) ℝ) a b =
          inner ℝ (eFrame.toBasis a) (eFrame.toBasis b) := by
      intro a b
      rw [Matrix.one_apply]
      change (if a = b then (1 : ℝ) else 0) = inner ℝ (eFrame a) (eFrame b)
      exact (orthonormal_iff_ite.mp eFrame.orthonormal a b).symm
    have hinv := MorganTianLib.sum_orthonormalBasis_diagonal_eq_invGram
      e eFrame.toBasis D (G := 1) (Ginv := 1) hgram (by simp)
    have hdiag : (∑ a : Fin (Module.finrank ℝ E3),
        ∑ b : Fin (Module.finrank ℝ E3),
          (1 : Matrix (Fin (Module.finrank ℝ E3)) (Fin (Module.finrank ℝ E3)) ℝ) a b •
            D (eFrame.toBasis a) (eFrame.toBasis b)) =
        ∑ a : Fin (Module.finrank ℝ E3), D (eFrame a) (eFrame a) := by
      simp [Matrix.one_apply]
    have hframe : (∑ i : Fin (Module.finrank ℝ E3), D (eFrame i) (eFrame i)) =
        ∑ i : Fin (Module.finrank ℝ E3),
          connectionDifferenceField nabla nabla0
            (MorganTianLib.orthoFrameField g p i)
            (MorganTianLib.orthoFrameField g p i) q := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      simpa [eFrame] using hD
        (MorganTianLib.orthoFrameField g p i) (MorganTianLib.orthoFrameField g p i)
    calc
      trace q = ∑ j, D (eStd j) (eStd j) := hstd
      _ = ∑ i : Fin (Module.finrank ℝ E3), D (e i) (e i) := hreindex.symm
      _ = ∑ a : Fin (Module.finrank ℝ E3),
          ∑ b : Fin (Module.finrank ℝ E3),
            (1 : Matrix (Fin (Module.finrank ℝ E3)) (Fin (Module.finrank ℝ E3)) ℝ) a b •
              D (eFrame.toBasis a) (eFrame.toBasis b) := hinv
      _ = ∑ a : Fin (Module.finrank ℝ E3), D (eFrame a) (eFrame a) := hdiag
      _ = ∑ i : Fin (Module.finrank ℝ E3),
          connectionDifferenceField nabla nabla0
            (MorganTianLib.orthoFrameField g p i)
            (MorganTianLib.orthoFrameField g p i) q := hframe
  have trace_eq_frameSum (p q : M)
      (hq : q ∈ MorganTianLib.orthoFrameSet (I := 𝓡 3) (M := M) p) :
      trace q = frameSum p q := by
    calc
      trace q = ∑ i : Fin (Module.finrank ℝ E3),
          connectionDifferenceField nabla nabla0
            (MorganTianLib.orthoFrameField g p i)
            (MorganTianLib.orthoFrameField g p i) q := trace_eq_frame p q hq
      _ = frameSum p q := (frameSum_apply p q).symm
  refine ⟨⟨trace, ?_⟩, ?_⟩
  · intro p
    apply (frameSum p).smooth.contMDiffAt.congr_of_eventuallyEq
    filter_upwards [(MorganTianLib.isOpen_orthoFrameSet
      (I := 𝓡 3) (M := M) p).mem_nhds
      (MorganTianLib.mem_orthoFrameSet_self (I := 𝓡 3) (M := M) p)] with q hq
    congr 1
    exact trace_eq_frameSum p q hq
  · intro p
    rfl
/- SWARM_PROOF_END -/
end MorganTianLib.MetricCoefficient
