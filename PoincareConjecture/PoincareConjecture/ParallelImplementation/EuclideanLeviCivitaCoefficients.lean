import PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
import PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
import DoCarmoLib.Riemannian.Manifold.DoCarmoCh2
import PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields
import PoincareConjecture.ParallelImplementation.CoordinateKoszulRecovery
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.EuclideanLeviCivitaCoefficients
open PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open PoincareConjecture.ParallelImplementation.SixMetricCoordinateModel
open MorganTianLib.MetricCoefficient
open scoped Topology BigOperators ContDiff Manifold
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E6" => EuclideanSpace ℝ (Fin 6)
local instance : NeZero (Module.finrank ℝ E3) := ⟨by simp⟩
theorem exists_intrinsic_coordinate_coefficients :

    ∃ V : Idx → Riemannian.SmoothVectorField 𝓘(ℝ, E3) E3,
      (∀ (i : Idx) (x : E3), V i x = EuclideanSpace.single i 1) ∧
      ∀ (g : Riemannian.RiemannianMetric 𝓘(ℝ, E3) E3) (x : E3) (h : Mat) (d : First),
        (∀ a b : Idx, (∑ l : Idx, h a l * g.metricInner x (EuclideanSpace.single l 1)
          (EuclideanSpace.single b 1)) = if a=b then 1 else 0) →
        (∀ a i j : Idx, fderiv ℝ (fun y : E3 => g.metricInner y
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) x
            (EuclideanSpace.single a 1) = d a i j) →
        ∀ i j k : Idx, (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) k : E3 →L[ℝ] ℝ) ((g.leviCivitaConnection.cov (V i) (V j)) x) = christoffel h d k i j :=
/- SWARM_PROOF_BEGIN -/
by
  obtain ⟨V, hV, hbr, hdir⟩ :=
    PoincareConjecture.ParallelImplementation.EuclideanCoordinateFields.exists_coordinate_fields
  refine ⟨V, hV, ?_⟩
  intro g x h d hInv hd i j k
  let W : E3 := (g.leviCivitaConnection.cov (V i) (V j)) x
  let w : Idx → ℝ := fun a =>
    (PiLp.proj (p := 2) (β := fun _ : Idx => ℝ) a : E3 →L[ℝ] ℝ) W
  let G : Mat := fun a b =>
    g.metricInner x (EuclideanSpace.single a 1) (EuclideanSpace.single b 1)

  have hdSymm : ∀ a b c : Idx, d a b c = d a c b := by
    intro a b c
    have hfun : (fun y : E3 => g.metricInner y
        (EuclideanSpace.single b 1) (EuclideanSpace.single c 1)) =
        (fun y : E3 => g.metricInner y
        (EuclideanSpace.single c 1) (EuclideanSpace.single b 1)) := by
      funext y
      exact g.metricInner_comm y _ _
    have hder := congrArg (fun f : E3 → ℝ =>
      fderiv ℝ f x (EuclideanSpace.single a 1)) hfun
    simpa only [hd a b c, hd a c b] using hder

  have hdirMetric (a b c : Idx) :
      (V a).dir (fun y : E3 => g.metricInner y (V b y) (V c y)) x = d a b c := by
    have hfun : (fun y : E3 => g.metricInner y (V b y) (V c y)) =
        (fun y : E3 => g.metricInner y
          (EuclideanSpace.single b 1) (EuclideanSpace.single c 1)) := by
      funext y
      rw [hV b y, hV c y]
    calc
      (V a).dir (fun y : E3 => g.metricInner y (V b y) (V c y)) x =
          (V a).dir (fun y : E3 => g.metricInner y
            (EuclideanSpace.single b 1) (EuclideanSpace.single c 1)) x :=
        congrArg (fun f : E3 → ℝ => (V a).dir f x) hfun
      _ = fderiv ℝ (fun y : E3 => g.metricInner y
            (EuclideanSpace.single b 1) (EuclideanSpace.single c 1)) x
            (EuclideanSpace.single a 1) := hdir _ a x
      _ = d a b c := hd a b c

  have hdual (l : Idx) :
      2 * g.metricInner x (V l x) W = g.koszulRHS (V j) (V i) (V l) x := by
    calc
      2 * g.metricInner x (V l x) W =
          2 * g.metricInner x W (V l x) := by
        rw [g.metricInner_comm]
      _ = g.koszulRHS (V j) (V i) (V l) x := by
        simpa [W, Riemannian.RiemannianMetric.leviCivitaConnection,
          Riemannian.RiemannianMetric.leviCivitaCovField] using
          (g.koszulDualSection_dual (V j) (V i) (V l) x)

  have hRHS (l : Idx) :
      g.koszulRHS (V j) (V i) (V l) x =
        d j i l + d i l j - d l j i := by
    simp only [Riemannian.RiemannianMetric.koszulRHS,
      hdirMetric j i l, hdirMetric i l j, hdirMetric l j i,
      hbr j l x, hbr i l x, hbr j i x,
      g.metricInner_zero_left]
    ring

  have hpair (l : Idx) :
      g.metricInner x (EuclideanSpace.single l 1) W = lowerChristoffel d l i j := by
    have h := hdual l
    rw [hRHS l] at h
    rw [hV l x] at h
    have hrewrite : d i l j = d i j l := hdSymm i l j
    have hrewrite' : d l j i = d l i j := hdSymm l j i
    rw [hrewrite, hrewrite'] at h
    unfold lowerChristoffel
    linarith

  have hWcoord : W = ∑ a : Idx, w a • (EuclideanSpace.single a 1) := by
    ext a
    simp [w, Pi.single_apply]

  have hmetricSum (l : Idx) (s : Finset Idx) :
      g.metricInner x (EuclideanSpace.single l 1)
        (∑ a ∈ s, w a • (EuclideanSpace.single a 1)) =
      ∑ a ∈ s, w a *
        g.metricInner x (EuclideanSpace.single l 1) (EuclideanSpace.single a 1) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simp only [Finset.sum_insert ha, g.metricInner_add_right,
          g.metricInner_smul_right, ih]

  have hw : ∀ l : Idx, (∑ a : Idx, G l a * w a) = lowerChristoffel d l i j := by
    intro l
    calc
      (∑ a : Idx, G l a * w a) =
          ∑ a : Idx, w a *
            g.metricInner x (EuclideanSpace.single l 1) (EuclideanSpace.single a 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        simp only [G]
        ring
      _ = g.metricInner x (EuclideanSpace.single l 1) W := by
        rw [hWcoord]
        exact (hmetricSum l Finset.univ).symm
      _ = lowerChristoffel d l i j := hpair l

  have hrec :=
    PoincareConjecture.ParallelImplementation.CoordinateKoszulRecovery.recover_christoffel_from_lower
      G h d w i j hInv hw
  change w k = christoffel h d k i j
  exact hrec k
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.EuclideanLeviCivitaCoefficients
