import PoincareConjecture.ParallelImplementation.ConformalSectionalRecovered
import PoincareConjecture.ParallelImplementation.ScalarSectionalTrace
import PoincareConjecture.ParallelImplementation.ConformalMetricBasis
import PoincareConjecture.ParallelImplementation.MetricTraceBasis
import PoincareConjecture.ParallelImplementation.MetricGradientContraction
import MorganTianLib.Ch02.Laplacian
set_option autoImplicit false
noncomputable section
open Riemannian
open scoped ContDiff Manifold Topology Bundle BigOperators
namespace PoincareConjecture.ParallelImplementation.ConformalScalarCurvature
open PoincareConjecture.ParallelImplementation.ConformalConnection
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]
/-- **Math.** Conformal scalar curvature for the actual canonical Levi-Civita metric contractions. -/
theorem scalarCurvatureAt_conformalMetric (g : RiemannianMetric I M)
    (u : M → ℝ) (hu : ContMDiff I 𝓘(ℝ, ℝ) ∞ u) (p : M) :
    let g' := conformalMetric g u hu
    let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g (fun X Y Z q => g.koszulDualSection_dual X Y Z q)
    let hLC' := g'.leviCivitaConnection.isLeviCivita_of_koszulDual g' (fun X Y Z q => g'.koszulDualSection_dual X Y Z q)
    MorganTianLib.scalarCurvatureAt g' g'.leviCivitaConnection hLC' p =
      Real.exp (-2 * u p) * (MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p -
        2 * ((Module.finrank ℝ E : ℝ)-1) * MorganTianLib.laplacianAt g g.leviCivitaConnection u p -
        ((Module.finrank ℝ E : ℝ)-1) * ((Module.finrank ℝ E : ℝ)-2) *
          g.metricInner p (MorganTianLib.gradientField g u hu p) (MorganTianLib.gradientField g u hu p)) :=
/- SWARM_PROOF_BEGIN -/
by
  let g' := conformalMetric g u hu
  let hLC := g.leviCivitaConnection.isLeviCivita_of_koszulDual g
    (fun X Y Z q => g.koszulDualSection_dual X Y Z q)
  let hLC' := g'.leviCivitaConnection.isLeviCivita_of_koszulDual g'
    (fun X Y Z q => g'.koszulDualSection_dual X Y Z q)
  change MorganTianLib.scalarCurvatureAt g' g'.leviCivitaConnection hLC' p =
    Real.exp (-2 * u p) * (MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p -
      2 * ((Module.finrank ℝ E : ℝ) - 1) * MorganTianLib.laplacianAt g g.leviCivitaConnection u p -
      ((Module.finrank ℝ E : ℝ) - 1) * ((Module.finrank ℝ E : ℝ) - 2) *
        g.metricInner p (MorganTianLib.gradientField g u hu p)
          (MorganTianLib.gradientField g u hu p))
  letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let ob : OrthonormalBasis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) :=
    stdOrthonormalBasis ℝ (TangentSpace I p)
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I p) := ob.toBasis
  have horth : Orthonormal ℝ (fun i => b i) := by
    simp [b, OrthonormalBasis.coe_toBasis]
  have hb : ∀ i j, g.metricInner p (b i) (b j) = if i = j then 1 else 0 := by
    intro i j
    have h := (orthonormal_iff_ite.mp horth) i j
    change inner ℝ (b i) (b j) = if i = j then 1 else 0 at h
    change inner ℝ (b i) (b j) = if i = j then 1 else 0
    exact h
  obtain ⟨b', hb'scale, hb'⟩ :=
    PoincareConjecture.ParallelImplementation.ConformalMetricBasis.exists_conformal_metric_basis
      g u hu p b hb
  let X : Fin (Module.finrank ℝ E) → SmoothVectorField I M :=
    fun i => MorganTianLib.extendVector p (b i)
  have hX (i : Fin (Module.finrank ℝ E)) : X i p = b i := by
    simp [X, MorganTianLib.extendVector_apply]
  let G := MorganTianLib.gradientField g u hu
  let K : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => MorganTianLib.sectionalCurvatureAt g g.leviCivitaConnection p (b i) (b j)
  let H : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => MorganTianLib.hessianAt g.leviCivitaConnection u p (b i) (b i)
  let D : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => PoincareConjecture.ParallelImplementation.MetricGradientContraction.scalarDifferential
      (I := I) u p (b i)
  let normG := g.metricInner p (G p) (G p)
  let c := Real.exp (-2 * u p)
  let dim : ℝ := (Module.finrank ℝ E : ℝ)
  let C : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ :=
    fun i j => K i j - H i - H j + D i ^ 2 + D j ^ 2 - normG
  have htraceG : MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p =
      ∑ i, ∑ j, K i j := by
    exact PoincareConjecture.ParallelImplementation.ScalarSectionalTrace.scalarCurvatureAt_eq_sum_sectional
      g g.leviCivitaConnection hLC p b hb
  have htraceG' : MorganTianLib.scalarCurvatureAt g' g'.leviCivitaConnection hLC' p =
      ∑ i, ∑ j, MorganTianLib.sectionalCurvatureAt g' g'.leviCivitaConnection p
        (b' i) (b' j) := by
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g'.toRiemannianMetric⟩
    exact PoincareConjecture.ParallelImplementation.ScalarSectionalTrace.scalarCurvatureAt_eq_sum_sectional
      g' g'.leviCivitaConnection hLC' p b' hb'
  have htraceLap : MorganTianLib.laplacianAt g g.leviCivitaConnection u p =
      ∑ i, H i := by
    exact PoincareConjecture.ParallelImplementation.MetricTraceBasis.laplacianAt_eq_sum_of_metric_basis
      g g.leviCivitaConnection u hu p b hb
  have hcontract :=
    PoincareConjecture.ParallelImplementation.MetricGradientContraction.sum_metric_basis_derivatives_eq_gradient_pairing
      g u u hu hu p b hb
  have hnormSum : ∑ i, D i ^ 2 = normG := by
    have hpair : ∑ i, D i * D i = G.dir u p := by
      simpa [D, PoincareConjecture.ParallelImplementation.MetricGradientContraction.scalarDifferential,
        G] using hcontract
    have hgrad := MorganTianLib.metricInner_gradientField_eq_dir g hu G p
    calc
      ∑ i, D i ^ 2 = ∑ i, D i * D i := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = G.dir u p := hpair
      _ = normG := hgrad.symm
  have hdiagG (i : Fin (Module.finrank ℝ E)) : K i i = 0 := by
    let B := MorganTianLib.curvatureFormAt g g.leviCivitaConnection p
    have hB : Riemannian.IsAlgCurvatureForm B :=
      MorganTianLib.isAlgCurvatureForm_curvatureFormAt g g.leviCivitaConnection hLC p
    have hnum : B (b i) (b i) (b i) (b i) = 0 := by
      have hskew := hB.antisymm₁₂ (b i) (b i) (b i) (b i)
      nlinarith [hskew]
    have hden : Riemannian.wedgeSq (b i) (b i) = 0 := by
      simp [Riemannian.wedgeSq]
    change B (b i) (b i) (b i) (b i) /
      Riemannian.wedgeSq (b i) (b i) = 0
    rw [hnum, hden]
    simp
  have hdiagG' (i : Fin (Module.finrank ℝ E)) :
      MorganTianLib.sectionalCurvatureAt g' g'.leviCivitaConnection p (b' i) (b' i) = 0 := by
    letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
      ⟨g'.toRiemannianMetric⟩
    let B := MorganTianLib.curvatureFormAt g' g'.leviCivitaConnection p
    have hB : Riemannian.IsAlgCurvatureForm B :=
      MorganTianLib.isAlgCurvatureForm_curvatureFormAt g' g'.leviCivitaConnection hLC' p
    have hnum : B (b' i) (b' i) (b' i) (b' i) = 0 := by
      have hskew := hB.antisymm₁₂ (b' i) (b' i) (b' i) (b' i)
      nlinarith [hskew]
    have hden : Riemannian.wedgeSq (b' i) (b' i) = 0 := by
      simp [Riemannian.wedgeSq]
    change B (b' i) (b' i) (b' i) (b' i) /
      Riemannian.wedgeSq (b' i) (b' i) = 0
    rw [hnum, hden]
    simp
  have hsectionFormula (i j : Fin (Module.finrank ℝ E)) (hij : i ≠ j) :
      MorganTianLib.sectionalCurvatureAt g' g'.leviCivitaConnection p (b' i) (b' j) =
        c * C i j := by
    let Xi := X i
    let Xj := X j
    have hXi : Xi p = b i := hX i
    have hXj : Xj p = b j := hX j
    have hnormXi : g.metricInner p (Xi p) (Xi p) = 1 := by
      rw [hXi]
      simpa using hb i i
    have hnormXj : g.metricInner p (Xj p) (Xj p) = 1 := by
      rw [hXj]
      simpa using hb j j
    have horthXY : g.metricInner p (Xi p) (Xj p) = 0 := by
      rw [hXi, hXj]
      simpa [hij] using hb i j
    have hsec :=
      PoincareConjecture.ParallelImplementation.ConformalSectionalRecovered.sectionalCurvatureAt_conformalMetric
        g u hu Xi Xj p hnormXi hnormXj horthXY
    have hscale :
        MorganTianLib.sectionalCurvatureAt g' g'.leviCivitaConnection p (b' i) (b' j) =
          MorganTianLib.sectionalCurvatureAt g' g'.leviCivitaConnection p (b i) (b j) := by
      letI : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
        ⟨g'.toRiemannianMetric⟩
      let s := Real.exp (-u p)
      let B := MorganTianLib.curvatureFormAt g' g'.leviCivitaConnection p
      have hB : Riemannian.IsAlgCurvatureForm B :=
        MorganTianLib.isAlgCurvatureForm_curvatureFormAt g' g'.leviCivitaConnection hLC' p
      have hsmul2 (a : ℝ) (x y z t : TangentSpace I p) :
          B x (a • y) z t = a * B x y z t := by
        calc
          B x (a • y) z t = -B (a • y) x z t := hB.antisymm₁₂ x (a • y) z t
          _ = -(a * B y x z t) := by rw [hB.smul_left a y x z t]
          _ = a * B x y z t := by rw [hB.antisymm₁₂ y x z t]; ring
      have hzero₁₂ (x z t : TangentSpace I p) : B x x z t = 0 := by
        have h := hB.antisymm₁₂ x x z t
        nlinarith [h]
      have hzero₃₄ (x y z : TangentSpace I p) : B x y z z = 0 := by
        have h := hB.antisymm₃₄ x y z z
        nlinarith [h]
      have hsmul3 (a b : ℝ) (x y : TangentSpace I p) :
          B x y (a • x) (b • y) = a * B x y x (b • y) := by
        have hcyc := hB.bianchi x y (a • x) (b • y)
        have hsecond : B y (a • x) x (b • y) = -a * B x y x (b • y) := by
          calc
            B y (a • x) x (b • y) = a * B y x x (b • y) :=
              hsmul2 a y x x (b • y)
            _ = a * (-B x y x (b • y)) := by
              rw [hB.antisymm₁₂ y x x (b • y)]
            _ = _ := by ring
        have hthird : B (a • x) x y (b • y) = 0 := by
          rw [hB.smul_left a x x y (b • y)]
          simp [hzero₁₂]
        rw [hsecond, hthird] at hcyc
        nlinarith [hcyc]
      have hsmul4 (a : ℝ) (x y : TangentSpace I p) :
          B x y x (a • y) = a * B x y x y := by
        have hcyc := hB.bianchi x y (a • y) x
        have hthird : B (a • y) x y x = a * B x y x y := by
          calc
            B (a • y) x y x = a * B y x y x := hB.smul_left a y x y x
            _ = a * B x y x y := by
              rw [hB.antisymm₁₂ y x y x, hB.antisymm₃₄ x y y x]
              ring
        rw [hzero₃₄ y (a • y) x, hthird] at hcyc
        rw [hB.antisymm₃₄ x y x (a • y)]
        nlinarith [hcyc]
      have hnumScale (a : ℝ) (x y : TangentSpace I p) :
          B (a • x) (a • y) (a • x) (a • y) = a ^ 4 * B x y x y := by
        calc
          B (a • x) (a • y) (a • x) (a • y) =
              a * B x (a • y) (a • x) (a • y) := hB.smul_left a x (a • y) (a • x) (a • y)
          _ = a * (a * B x y (a • x) (a • y)) := by rw [hsmul2 a x y (a • x) (a • y)]
          _ = a ^ 4 * B x y x y := by rw [hsmul3 a a x y, hsmul4 a x y]; ring
      have hwedgeScale (a : ℝ) (x y : TangentSpace I p) :
          Riemannian.wedgeSq (a • x) (a • y) = a ^ 4 * Riemannian.wedgeSq x y := by
        simp only [Riemannian.wedgeSq, real_inner_smul_left, real_inner_smul_right]
        ring
      have hs : s ≠ 0 := by
        dsimp [s]
        exact Real.exp_ne_zero _
      have hdenBasis : Riemannian.wedgeSq (b' i) (b' j) = 1 := by
        have hxx : inner ℝ (b' i) (b' i) = 1 := by
          have h := hb' i i
          have hm : g'.metricInner p (b' i) (b' i) = 1 := by simpa using h
          change inner ℝ (b' i) (b' i) = 1
          exact hm
        have hyy : inner ℝ (b' j) (b' j) = 1 := by
          have h := hb' j j
          have hm : g'.metricInner p (b' j) (b' j) = 1 := by simpa using h
          change inner ℝ (b' j) (b' j) = 1
          exact hm
        have hxy : inner ℝ (b' i) (b' j) = 0 := by
          have h := hb' i j
          have hm : g'.metricInner p (b' i) (b' j) = 0 := by simpa [hij] using h
          change inner ℝ (b' i) (b' j) = 0
          exact hm
        unfold Riemannian.wedgeSq
        rw [hxx, hyy, hxy]
        norm_num
      have hdenScale : Riemannian.wedgeSq (b' i) (b' j) =
          s ^ 4 * Riemannian.wedgeSq (b i) (b j) := by
        rw [hb'scale i, hb'scale j]
        exact hwedgeScale s (b i) (b j)
      have hdenRel : 1 = s ^ 4 * Riemannian.wedgeSq (b i) (b j) := by
        rw [← hdenBasis]
        exact hdenScale
      have hdenNonzero : Riemannian.wedgeSq (b i) (b j) ≠ 0 := by
        intro hz
        rw [hz] at hdenRel
        simp at hdenRel
      rw [hb'scale i, hb'scale j]
      change B (s • b i) (s • b j) (s • b i) (s • b j) /
        Riemannian.wedgeSq (s • b i) (s • b j) =
        B (b i) (b j) (b i) (b j) / Riemannian.wedgeSq (b i) (b j)
      rw [hnumScale s (b i) (b j), hwedgeScale s (b i) (b j)]
      field_simp [pow_ne_zero 4 hs, hdenNonzero]
    have hHXi : MorganTianLib.hessian g.leviCivitaConnection u Xi Xi p = H i := by
      simp [H, Xi, X, MorganTianLib.hessianAt_def]
    have hHXj : MorganTianLib.hessian g.leviCivitaConnection u Xj Xj p = H j := by
      simp [H, Xj, X, MorganTianLib.hessianAt_def]
    have hDXi : Xi.dir u p = D i := by
      simp [D, Xi, X, PoincareConjecture.ParallelImplementation.MetricGradientContraction.scalarDifferential,
        Riemannian.SmoothVectorField.dir, MorganTianLib.extendVector_apply]
    have hDXj : Xj.dir u p = D j := by
      simp [D, Xj, X, PoincareConjecture.ParallelImplementation.MetricGradientContraction.scalarDifferential,
        Riemannian.SmoothVectorField.dir, MorganTianLib.extendVector_apply]
    rw [hXi, hXj] at hsec
    rw [← hscale] at hsec
    rw [hHXi, hHXj, hDXi, hDXj] at hsec
    simpa [K, H, D, c, C, normG, G,
      PoincareConjecture.ParallelImplementation.MetricGradientContraction.scalarDifferential,
      MorganTianLib.hessianAt_def, MorganTianLib.extendVector_apply] using hsec
  have hterm (i j : Fin (Module.finrank ℝ E)) :
      MorganTianLib.sectionalCurvatureAt g' g'.leviCivitaConnection p (b' i) (b' j) =
        if i = j then 0 else c * C i j := by
    by_cases hij : i = j
    · subst j
      rw [hdiagG']
      simp
    · simpa [hij] using hsectionFormula i j hij
  have hrowOff (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
      (i : Fin (Module.finrank ℝ E)) :
      (∑ j, if i = j then 0 else f i j) = (∑ j, f i j) - f i i := by
    calc
      (∑ j, if i = j then 0 else f i j) =
          ∑ j, (f i j - if i = j then f i i else 0) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i = j <;> simp [hij]
      _ = _ := by rw [Finset.sum_sub_distrib]; simp
  have hdoubleOff (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
      (∑ i, ∑ j, if i = j then 0 else f i j) =
        (∑ i, ∑ j, f i j) - ∑ i, f i i := by
    calc
      (∑ i, ∑ j, if i = j then 0 else f i j) =
          ∑ i, ((∑ j, f i j) - f i i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hrowOff f i
      _ = _ := by rw [Finset.sum_sub_distrib]
  have hsumLeft (f : Fin (Module.finrank ℝ E) → ℝ) :
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E), f i) =
        dim * ∑ i, f i := by
    calc
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E), f i) =
          ∑ i, (Module.finrank ℝ E : ℝ) * f i := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Finset.sum_const, Fintype.card_fin]
      _ = (Module.finrank ℝ E : ℝ) * ∑ i, f i := by
        exact (Finset.mul_sum Finset.univ f (Module.finrank ℝ E : ℝ)).symm
      _ = dim * ∑ i, f i := by simp [dim]
  have hsumRight (f : Fin (Module.finrank ℝ E) → ℝ) :
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E), f j) =
        dim * ∑ j, f j := by
    simp [dim, Finset.sum_const, Fintype.card_fin]
  have hsumNorm : (∑ i : Fin (Module.finrank ℝ E), normG) = dim * normG := by
    simp [dim, Finset.sum_const, Fintype.card_fin]
  have hsumDimNorm :
      (∑ i : Fin (Module.finrank ℝ E), dim * normG) = dim ^ 2 * normG := by
    simp [dim, Finset.sum_const, Fintype.card_fin]
    ring
  have hKsum : (∑ i, ∑ j, K i j) =
      MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p := htraceG.symm
  have hKdiag : (∑ i : Fin (Module.finrank ℝ E), K i i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact hdiagG i
  have hCsumAll :
      (∑ i, ∑ j, C i j) =
        MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p -
          2 * dim * MorganTianLib.laplacianAt g g.leviCivitaConnection u p +
          2 * dim * normG - dim ^ 2 * normG := by
    simp only [C, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hKsum, hsumLeft H, hsumRight H, hsumLeft (fun i => D i ^ 2),
      hsumRight (fun i => D i ^ 2), hsumNorm]
    rw [hsumDimNorm]
    simp_rw [← htraceLap, hnormSum]
    ring
  have hCsumDiag :
      (∑ i : Fin (Module.finrank ℝ E), C i i) =
        -2 * MorganTianLib.laplacianAt g g.leviCivitaConnection u p +
          2 * normG - dim * normG := by
    simp only [C, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [hKdiag]
    simp_rw [← htraceLap, hnormSum, hsumNorm]
    ring
  have hCsum :
      (∑ i, ∑ j, C i j) - ∑ i, C i i =
        MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p -
          2 * (dim - 1) * MorganTianLib.laplacianAt g g.leviCivitaConnection u p -
          (dim - 1) * (dim - 2) * normG := by
    rw [hCsumAll, hCsumDiag]
    ring
  have hfactorDouble (f : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :
      (∑ i, ∑ j, c * f i j) = c * ∑ i, ∑ j, f i j := by
    calc
      (∑ i, ∑ j, c * f i j) = ∑ i, c * ∑ j, f i j := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (Finset.mul_sum Finset.univ (fun j => f i j) c).symm
      _ = c * ∑ i, ∑ j, f i j := by
        exact (Finset.mul_sum Finset.univ (fun i => ∑ j, f i j) c).symm
  have hfactorDiag (f : Fin (Module.finrank ℝ E) → ℝ) :
      (∑ i, c * f i) = c * ∑ i, f i := by
    exact (Finset.mul_sum Finset.univ f c).symm
  have hsumOff :
      (∑ i, ∑ j, if i = j then 0 else c * C i j) =
        c * (MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p -
          2 * (dim - 1) * MorganTianLib.laplacianAt g g.leviCivitaConnection u p -
          (dim - 1) * (dim - 2) * normG) := by
    calc
      (∑ i, ∑ j, if i = j then 0 else c * C i j) =
          (∑ i, ∑ j, c * C i j) - ∑ i, c * C i i := hdoubleOff _
      _ = c * ((∑ i, ∑ j, C i j) - ∑ i, C i i) := by
        rw [hfactorDouble, hfactorDiag]
        ring
      _ = _ := by rw [hCsum]
  calc
    MorganTianLib.scalarCurvatureAt g' g'.leviCivitaConnection hLC' p =
        ∑ i, ∑ j, MorganTianLib.sectionalCurvatureAt g' g'.leviCivitaConnection p
          (b' i) (b' j) := htraceG'
    _ = ∑ i, ∑ j, if i = j then 0 else c * C i j := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact hterm i j
    _ = c * (MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p -
        2 * (dim - 1) * MorganTianLib.laplacianAt g g.leviCivitaConnection u p -
        (dim - 1) * (dim - 2) * normG) := hsumOff
    _ = Real.exp (-2 * u p) * (MorganTianLib.scalarCurvatureAt g g.leviCivitaConnection hLC p -
        2 * ((Module.finrank ℝ E : ℝ) - 1) * MorganTianLib.laplacianAt g g.leviCivitaConnection u p -
        ((Module.finrank ℝ E : ℝ) - 1) * ((Module.finrank ℝ E : ℝ) - 2) *
          g.metricInner p (MorganTianLib.gradientField g u hu p)
            (MorganTianLib.gradientField g u hu p)) := by
      simp [c, dim, normG, G]
/- SWARM_PROOF_END -/
end PoincareConjecture.ParallelImplementation.ConformalScalarCurvature
