import MorganTianLib.Ch03.RicciFlow.CurvatureLaplacian
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.BackgroundTensorCutoff
open MorganTianLib Riemannian
open scoped ContDiff Manifold Topology Bundle RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
def scalarCovTensor (χ : M → ℝ) : CovTensorField I M 0 := fun _ p => χ p
def cutoffCrossTensor (nabla : AffineConnection I M) (χ : M → ℝ)
    (A : CovTensorField I M 2) : CovTensorField I M 4 :=
  fun Z p => (Z 0).dir χ p * covTensorDerivAlong nabla (Z 1) A
    (fun i => Z i.succ.succ) p
theorem roughLaplacian_cutoff_product
    (g₀ : Riemannian.RiemannianMetric I M) (χ : M → ℝ) (A : CovTensorField I M 2)
    (hχ : ContMDiff I 𝓘(ℝ, ℝ) 2 χ)
    (hA : ∀ Y : Fin 2 → SmoothVectorField I M, ContMDiff I 𝓘(ℝ, ℝ) 2 (A Y))
    (Y : Fin 2 → SmoothVectorField I M) (p : M) :
    roughLaplacian g₀ g₀.leviCivitaConnection (fun Z q => χ q * A Z q) Y p =
      χ p * roughLaplacian g₀ g₀.leviCivitaConnection A Y p +
      A Y p * roughLaplacian g₀ g₀.leviCivitaConnection
        (scalarCovTensor (I := I) χ) (fun i => Fin.elim0 i) p +
      2 * traceFirstTwo g₀ (cutoffCrossTensor g₀.leviCivitaConnection χ A) Y p :=
/- SWARM_PROOF_BEGIN -/
by
  have horder : (1 : ℕ∞ω) ≤ 2 := by norm_num
  have dirC1 (X : SmoothVectorField I M) (f : M → ℝ)
      (hf : ContMDiff I 𝓘(ℝ, ℝ) 2 f) :
      ContMDiff I 𝓘(ℝ, ℝ) 1 (X.dir f) := by
    have htan : ContMDiff I.tangent (modelWithCornersSelf ℝ ℝ).tangent 1
        (tangentMap I (modelWithCornersSelf ℝ ℝ) f) :=
      hf.contMDiff_tangentMap (m := 1) (by norm_num)
    have hproj := contMDiff_snd_tangentBundle_modelSpace ℝ
      (modelWithCornersSelf ℝ ℝ) (n := 1)
    have hsec := X.smooth.of_le (m := 1) (by norm_num)
    have hcomp := ContMDiff.comp hproj (ContMDiff.comp htan hsec)
    change ContMDiff I 𝓘(ℝ, ℝ) 1 (X.dir f) at hcomp
    exact hcomp

  have hderivC1 (X : SmoothVectorField I M) :
      ∀ Z : Fin 2 → SmoothVectorField I M,
        ContMDiff I 𝓘(ℝ, ℝ) 1 (covTensorDerivAlong
          g₀.leviCivitaConnection X A Z) := by
    intro Z
    change ContMDiff I 𝓘(ℝ, ℝ) 1
      (fun q => X.dir (A Z) q - ∑ i, A (Function.update Z i
        (g₀.leviCivitaConnection.cov X (Z i))) q)
    have hfirst := dirC1 X (A Z) (hA Z)
    have hsum : ContMDiff I 𝓘(ℝ, ℝ) 1
        (fun q => ∑ i, A (Function.update Z i
          (g₀.leviCivitaConnection.cov X (Z i))) q) := by
      apply contMDiff_finsetSum (t := Finset.univ)
      intro i hi
      exact (hA (Function.update Z i
        (g₀.leviCivitaConnection.cov X (Z i)))).of_le horder
    exact hfirst.sub hsum

  have productRule {k : ℕ} (f : M → ℝ) (T : CovTensorField I M k)
      (X : SmoothVectorField I M) (Z : Fin k → SmoothVectorField I M)
      (q : M) (hf : MDiffAt f q)
      (hT : ∀ W : Fin k → SmoothVectorField I M, MDiffAt (T W) q) :
      covTensorDerivAlong g₀.leviCivitaConnection X
          (fun W r => f r * T W r) Z q =
        f q * covTensorDerivAlong g₀.leviCivitaConnection X T Z q +
          X.dir f q * T Z q := by
    change X.dir (fun r => f r * T Z r) q -
        ∑ i, f q * T (Function.update Z i
          (g₀.leviCivitaConnection.cov X (Z i))) q =
      f q * (X.dir (T Z) q - ∑ i, T (Function.update Z i
        (g₀.leviCivitaConnection.cov X (Z i))) q) + X.dir f q * T Z q
    rw [X.dir_mul q hf (hT Z)]
    rw [mul_sub, Finset.mul_sum]
    ring

  have addRule {k : ℕ} (S T : CovTensorField I M k)
      (X : SmoothVectorField I M) (Z : Fin k → SmoothVectorField I M)
      (q : M) (hS : ∀ W : Fin k → SmoothVectorField I M, MDiffAt (S W) q)
      (hT : ∀ W : Fin k → SmoothVectorField I M, MDiffAt (T W) q) :
      covTensorDerivAlong g₀.leviCivitaConnection X
          (fun W r => S W r + T W r) Z q =
      covTensorDerivAlong g₀.leviCivitaConnection X S Z q +
          covTensorDerivAlong g₀.leviCivitaConnection X T Z q := by
    change X.dir (fun r => S Z r + T Z r) q -
        ∑ i, (S (Function.update Z i
          (g₀.leviCivitaConnection.cov X (Z i))) q +
          T (Function.update Z i (g₀.leviCivitaConnection.cov X (Z i))) q) =
      (X.dir (S Z) q - ∑ i, S (Function.update Z i
        (g₀.leviCivitaConnection.cov X (Z i))) q) +
      (X.dir (T Z) q - ∑ i, T (Function.update Z i
        (g₀.leviCivitaConnection.cov X (Z i))) q)
    rw [X.dir_add q (hS Z) (hT Z)]
    rw [Finset.sum_add_distrib]
    ring

  have scalarRule (V : SmoothVectorField I M) (f : M → ℝ) :
      covTensorDerivAlong g₀.leviCivitaConnection V
          (scalarCovTensor (I := I) f) =
        scalarCovTensor (I := I) (V.dir f) := by
    funext Z q
    simp only [covTensorDerivAlong, scalarCovTensor]
    have hfun : scalarCovTensor (I := I) f Z = f := by
      funext r
      rfl
    rw [hfun]
    simp

  let B : CovTensorField I M 2 := fun Z q => χ q * A Z q
  let D (X : SmoothVectorField I M) : CovTensorField I M 2 := fun Z q =>
    covTensorDerivAlong g₀.leviCivitaConnection X A Z q
  have hχ1 : ContMDiff I 𝓘(ℝ, ℝ) 1 χ := hχ.of_le horder
  have hχdir1 (X : SmoothVectorField I M) :
      ContMDiff I 𝓘(ℝ, ℝ) 1 (X.dir χ) := dirC1 X χ hχ
  have hfirst (X : SmoothVectorField I M) :
      covTensorDerivAlong g₀.leviCivitaConnection X B =
        (fun Z q => χ q * D X Z q + X.dir χ q * A Z q) := by
    funext Z q
    exact productRule χ A X Z q
      (hχ1.mdifferentiableAt (by simp))
      (fun W => (hA W).mdifferentiableAt (by simp))

  have hsecond (X : SmoothVectorField I M)
      (Z : Fin 2 → SmoothVectorField I M) :
        secondCovDerivAlong g₀.leviCivitaConnection X X
          (fun W q => χ q * A W q) Z p =
        χ p * secondCovDerivAlong g₀.leviCivitaConnection X X A Z p +
          secondCovDerivAlong g₀.leviCivitaConnection X X
            (scalarCovTensor (I := I) χ) (fun i => Fin.elim0 i) p * A Z p +
          2 * (X.dir χ p * D X Z p) := by
    change secondCovDerivAlong g₀.leviCivitaConnection X X B Z p = _
    unfold secondCovDerivAlong
    rw [hfirst X]
    have hDdiff : ∀ W : Fin 2 → SmoothVectorField I M,
        MDiffAt (D X W) p := by
      intro W
      exact (hderivC1 X W).mdifferentiableAt (by simp)
    have hAdiff : ∀ W : Fin 2 → SmoothVectorField I M,
        MDiffAt (A W) p := by
      intro W
      exact (hA W).mdifferentiableAt (by simp)
    have hχdiff : MDiffAt χ p := hχ1.mdifferentiableAt (by simp)
    have hχ'diff : MDiffAt (X.dir χ) p := by
      exact (hχdir1 X).mdifferentiableAt (by simp)
    rw [addRule (fun W q => χ q * D X W q) (fun W q => X.dir χ q * A W q)
      X Z p (by intro W; exact (hχ1.mul (hderivC1 X W)).mdifferentiableAt (by simp))
      (by intro W; exact ((hχdir1 X).mul ((hA W).of_le horder)).mdifferentiableAt (by simp))]
    rw [productRule χ (D X) X Z p hχdiff hDdiff]
    rw [productRule (X.dir χ) A X Z p hχ'diff hAdiff]
    rw [productRule χ A (g₀.leviCivitaConnection.cov X X) Z p hχdiff hAdiff]
    have hDfield : D X = covTensorDerivAlong g₀.leviCivitaConnection X A := rfl
    rw [hDfield]
    rw [scalarRule X χ, scalarRule X (X.dir χ),
      scalarRule (g₀.leviCivitaConnection.cov X X) χ]
    simp only [scalarCovTensor]
    ring

  rw [roughLaplacian_apply, roughLaplacian_apply, roughLaplacian_apply]
  rw [traceFirstTwo]
  simp only [cutoffCrossTensor]
  simp_rw [hsecond]
  simp [Fin.cons_zero, Fin.cons_succ, Fin.cons_one, D]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  simp_rw [mul_comm]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.BackgroundTensorCutoff
