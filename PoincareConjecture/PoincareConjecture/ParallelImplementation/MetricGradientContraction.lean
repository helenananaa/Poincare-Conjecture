import MorganTianLib.Ch02.Gradient
import Mathlib
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle BigOperators
namespace PoincareConjecture.ParallelImplementation.MetricGradientContraction
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
def scalarDifferential (f : M → ℝ) (p : M) (v : TangentSpace I p) : ℝ :=
  mfderiv I 𝓘(ℝ, ℝ) f p v

theorem sum_metric_basis_derivatives_eq_gradient_pairing (g : RiemannianMetric I M)
    (u f : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u)
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (p : M)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι ℝ (TangentSpace I p))
    (hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0) :
    (∑ i, scalarDifferential (I := I) u p (b i) * scalarDifferential (I := I) f p (b i)) =
      (MorganTianLib.gradientField g u hu).dir f p :=
/- SWARM_PROOF_BEGIN -/
by
  let G := MorganTianLib.gradientField g u hu
  let F := MorganTianLib.gradientField g f hf
  let c : ι → ℝ := fun i => (b.repr (G p)) i
  have hmetricSum (a : ι → ℝ) (Y : TangentSpace I p) :
      g.metricInner p (∑ i, a i • b i) Y =
        ∑ i, a i * g.metricInner p (b i) Y := by
    simp
  have hrepr : (∑ i, c i • b i) = G p := by
    exact b.sum_repr (G p)
  have hpairBasis (i : ι) :
      g.metricInner p (G p) (b i) = c i := by
    calc
      g.metricInner p (G p) (b i) =
          g.metricInner p (∑ j, c j • b j) (b i) := by rw [← hrepr]
      _ = ∑ j, c j * g.metricInner p (b j) (b i) := hmetricSum c (b i)
      _ = c i := by
        rw [Finset.sum_eq_single i]
        · rw [hb i i]
          simp
        · intro j hj hji
          rw [hb j i]
          simp [hji]
        · intro hi
          exact (hi (Finset.mem_univ i)).elim
  have hdu (i : ι) :
      scalarDifferential (I := I) u p (b i) =
        g.metricInner p (G p) (b i) := by
    obtain ⟨X, hX⟩ := Riemannian.exists_smoothVectorField_eq p (b i)
    have hRiesz := MorganTianLib.metricInner_gradientField_eq_dir g hu X p
    calc
      scalarDifferential (I := I) u p (b i) = X.dir u p := by
        change mfderiv I 𝓘(ℝ, ℝ) u p (b i) =
          mfderiv I 𝓘(ℝ, ℝ) u p (X p)
        rw [hX]
      _ = g.metricInner p (G p) (X p) := by simpa [G] using hRiesz.symm
      _ = g.metricInner p (G p) (b i) := by rw [hX]
  have hcoeff (i : ι) : c i = scalarDifferential (I := I) u p (b i) := by
    dsimp [c]
    calc
      (b.repr (G p)) i = g.metricInner p (G p) (b i) := (hpairBasis i).symm
      _ = scalarDifferential (I := I) u p (b i) := (hdu i).symm
  have hdf (i : ι) :
      scalarDifferential (I := I) f p (b i) =
        g.metricInner p (F p) (b i) := by
    obtain ⟨X, hX⟩ := Riemannian.exists_smoothVectorField_eq p (b i)
    have hRiesz := MorganTianLib.metricInner_gradientField_eq_dir g hf X p
    calc
      scalarDifferential (I := I) f p (b i) = X.dir f p := by
        change mfderiv I 𝓘(ℝ, ℝ) f p (b i) =
          mfderiv I 𝓘(ℝ, ℝ) f p (X p)
        rw [hX]
      _ = g.metricInner p (F p) (X p) := by simpa [F] using hRiesz.symm
      _ = g.metricInner p (F p) (b i) := by rw [hX]
  have hFbasis (i : ι) :
      g.metricInner p (b i) (F p) = scalarDifferential (I := I) f p (b i) := by
    calc
      g.metricInner p (b i) (F p) = g.metricInner p (F p) (b i) :=
        g.metricInner_comm p (b i) (F p)
      _ = scalarDifferential (I := I) f p (b i) := (hdf i).symm
  have hsumPair :
      g.metricInner p (G p) (F p) =
        ∑ i, scalarDifferential (I := I) u p (b i) *
          scalarDifferential (I := I) f p (b i) := by
    calc
      g.metricInner p (G p) (F p) =
          g.metricInner p (∑ i, c i • b i) (F p) := by rw [← hrepr]
      _ = ∑ i, c i * g.metricInner p (b i) (F p) := hmetricSum c (F p)
      _ = ∑ i, scalarDifferential (I := I) u p (b i) *
          scalarDifferential (I := I) f p (b i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoeff i, hFbasis i]
  calc
    (∑ i, scalarDifferential (I := I) u p (b i) *
        scalarDifferential (I := I) f p (b i)) =
        g.metricInner p (G p) (F p) := hsumPair.symm
    _ = g.metricInner p (F p) (G p) := g.metricInner_comm p (G p) (F p)
    _ = G.dir f p := by
      simpa [G, F] using MorganTianLib.metricInner_gradientField_eq_dir g hf G p
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.MetricGradientContraction
