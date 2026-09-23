import Mathlib
import DoCarmoLib.Riemannian.Connection.ChartChristoffelSmooth
import MorganTianLib.Ch01.CurvatureFrameBridge

/-!
# Derivative-level coordinate metric control for retained necks

This module separates coordinate C² control from the existing C⁰
`EpsilonClose`.  Its metric field is the actual chart Gram matrix, and the
first and second jets are iterated Fréchet derivatives.  The estimates below
are finite-dimensional and pointwise on a chart domain.
-/

noncomputable section

open Riemannian
open scoped Manifold Topology Bundle ContDiff

namespace PoincareConjecture.ParallelImplementation.NeckC2Control

/-- The chart Gram matrix, with both indices in the same finite chart frame
used by `Riemannian.chartChristoffel`. -/
noncomputable def chartGramField
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) (α : M) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun y i j => chartGramOnE (I := I) g α i j y

/-- Coordinate C² closeness on a set, measured by the operator norm of the
zeroth-order matrix perturbation and componentwise absolute bounds for all
first and second coordinate derivatives.  Each derivative is an actual
iterated `fderiv` along the chart-frame basis, not an auxiliary jet field. -/
def matrixFieldC2CloseOn
    {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    (G H : E → Matrix n n ℝ) (s : Set E) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ ∀ y ∈ s,
    ‖(Matrix.toEuclideanLin (G y - H y)).toContinuousLinearMap‖ ≤ ε ∧
    (∀ i j, |G y i j - H y i j| ≤ ε) ∧
    (∀ (i j : n) (k : Fin (Module.finrank ℝ E)),
      |fderiv ℝ (fun z => G z i j) y (Module.finBasis ℝ E k) -
        fderiv ℝ (fun z => H z i j) y (Module.finBasis ℝ E k)| ≤ ε) ∧
    (∀ (i j : n) (k l : Fin (Module.finrank ℝ E)),
      |fderiv ℝ (fun z => fderiv ℝ (fun w => G w i j) z
          (Module.finBasis ℝ E k)) y (Module.finBasis ℝ E l) -
        fderiv ℝ (fun z => fderiv ℝ (fun w => H w i j) z
          (Module.finBasis ℝ E k)) y (Module.finBasis ℝ E l)| ≤ ε)

/-- C² coordinate closeness of two genuine Riemannian chart metrics.  This is
independent of Morgan--Tian's C⁰-only `EpsilonClose` predicate. -/
def chartMetricC2CloseOn
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g₀ g : RiemannianMetric I M) (α : M) (s : Set E) (ε : ℝ) : Prop :=
  matrixFieldC2CloseOn (chartGramField (I := I) g α)
    (chartGramField (I := I) g₀ α) s ε

/-- A pointwise uniform ellipticity lower bound for a reference chart Gram
matrix, expressed in the Euclidean norm of the coordinate vector. -/
def matrixFieldUniformLowerBound
    {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    (H : E → Matrix n n ℝ) (s : Set E) (lam : ℝ) : Prop :=
  ∀ y ∈ s, ∀ v : EuclideanSpace ℝ n,
    lam * ‖v‖ ^ 2 ≤ inner ℝ
      ((Matrix.toEuclideanLin (H y)).toContinuousLinearMap v) v

/-- The Euclidean pairing of the linear map represented by a real matrix is
its usual matrix quadratic form. -/
lemma inner_toEuclideanLin_eq_dotProduct
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (x : n → ℝ) :
    inner ℝ
      ((Matrix.toEuclideanLin A).toContinuousLinearMap (WithLp.toLp 2 x))
      (WithLp.toLp 2 x) = dotProduct (star x) (A.mulVec x) := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Matrix.toEuclideanLin_apply,
    dotProduct_comm]

/-- Zeroth-order C² closeness preserves a quantitative positive lower bound.
If the reference chart metric has lower bound `λ` and the operator-norm
perturbation is at most `ε < lam`, then the perturbed quadratic form has lower
bound `lam - ε`. -/
theorem c2Close_preserves_uniform_lower_bound
    {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    {G H : E → Matrix n n ℝ} {s : Set E} {ε lam : ℝ}
    (hclose : matrixFieldC2CloseOn G H s ε)
    (hHref : matrixFieldUniformLowerBound H s lam) :
    ∀ y ∈ s, ∀ v : EuclideanSpace ℝ n,
      (lam - ε) * ‖v‖ ^ 2 ≤ inner ℝ
        ((Matrix.toEuclideanLin (G y)).toContinuousLinearMap v) v := by
  rcases hclose with ⟨hε, hclose⟩
  intro y hy v
  rcases hclose y hy with ⟨hvalue, _, _, _⟩
  have hvalue_apply := (ContinuousLinearMap.opNorm_le_iff hε).mp hvalue v
  have hsplit :
      ((Matrix.toEuclideanLin (G y)).toContinuousLinearMap v) =
        ((Matrix.toEuclideanLin (H y)).toContinuousLinearMap v) +
        ((Matrix.toEuclideanLin (G y - H y)).toContinuousLinearMap v) := by
    simp [map_sub, sub_eq_add_neg, add_assoc]
  have herror : |inner ℝ
      ((Matrix.toEuclideanLin (G y - H y)).toContinuousLinearMap v) v| ≤
      ε * ‖v‖ ^ 2 := by
    calc
      _ ≤ ‖((Matrix.toEuclideanLin (G y - H y)).toContinuousLinearMap v)‖ * ‖v‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ (ε * ‖v‖) * ‖v‖ := by gcongr
      _ = ε * ‖v‖ ^ 2 := by ring
  rw [hsplit, inner_add_left]
  have href := hHref y hy v
  rcases (abs_le.mp herror) with ⟨herrorLo, herrorHi⟩
  nlinarith [sq_nonneg ‖v‖]

/-- A positive lower bound as above implies positive definiteness of the
actual matrix.  Symmetry is supplied by the metric tensor; it is not inferred
from closeness. -/
theorem c2Close_posDef
    {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    {G H : E → Matrix n n ℝ} {s : Set E} {ε lam : ℝ}
    (hclose : matrixFieldC2CloseOn G H s ε)
    (hHref : matrixFieldUniformLowerBound H s lam)
    (hlt : ε < lam)
    (hGsymm : ∀ y ∈ s, (G y).IsHermitian) :
    ∀ y ∈ s, (G y).PosDef := by
  intro y hy
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨hGsymm y hy, ?_⟩
  intro x hx
  let v : EuclideanSpace ℝ n := WithLp.toLp 2 x
  have hv : v ≠ 0 := by
    intro hv
    apply hx
    simpa [v] using hv
  have hlower := c2Close_preserves_uniform_lower_bound hclose hHref y hy v
  rw [inner_toEuclideanLin_eq_dotProduct] at hlower
  have hpos : 0 < lam - ε := sub_pos.mpr hlt
  have hnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  simpa [v] using (lt_of_lt_of_le (mul_pos hpos hnorm) hlower)

/-- Pointwise matrix invertibility for the perturbed chart metric follows from
`PosDef`, using mathlib's finite-dimensional matrix theorem. -/
theorem c2Close_isUnit
    {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    {G H : E → Matrix n n ℝ} {s : Set E} {ε lam : ℝ}
    (hclose : matrixFieldC2CloseOn G H s ε)
    (hHref : matrixFieldUniformLowerBound H s lam)
    (hlt : ε < lam)
    (hGsymm : ∀ y ∈ s, (G y).IsHermitian) :
    ∀ y ∈ s, IsUnit (G y) := by
  intro y hy
  exact (c2Close_posDef hclose hHref hlt hGsymm y hy).isUnit


/-- The actual chart Gram field is symmetric because the underlying metric
bilinear form is symmetric. -/
theorem chartGramField_isHermitian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) (α : M) (y : E) :
    (chartGramField (I := I) g α y).IsHermitian := by
  rw [Matrix.isHermitian_iff_isSymm]
  change (chartGramField (I := I) g α y).transpose = chartGramField (I := I) g α y
  ext i j
  change chartGramOnE (I := I) g α j i y =
    chartGramOnE (I := I) g α i j y
  exact (chartGramOnE_symm (I := I) g α i j y).symm

/-- Positivity and invertibility for two genuine chart metrics from derivative
level coordinate closeness, with the reference chart's uniform ellipticity
constant supplied explicitly. -/
theorem chartMetricC2Close_posDef
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g₀ g : RiemannianMetric I M} {α : M} {s : Set E} {ε lam : ℝ}
    (hclose : chartMetricC2CloseOn (I := I) g₀ g α s ε)
    (hHref : matrixFieldUniformLowerBound (chartGramField (I := I) g₀ α) s lam)
    (hlt : ε < lam) :
    ∀ y ∈ s, (chartGramField (I := I) g α y).PosDef := by
  apply c2Close_posDef hclose hHref hlt
  intro y hy
  exact chartGramField_isHermitian (I := I) g α y

/-- Hence the perturbed chart Gram matrix is a unit, so its matrix inverse is a
true inverse rather than the zero convention for singular matrices. -/
theorem chartMetricC2Close_isUnit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g₀ g : RiemannianMetric I M} {α : M} {s : Set E} {ε lam : ℝ}
    (hclose : chartMetricC2CloseOn (I := I) g₀ g α s ε)
    (hHref : matrixFieldUniformLowerBound (chartGramField (I := I) g₀ α) s lam)
    (hlt : ε < lam) :
    ∀ y ∈ s, IsUnit (chartGramField (I := I) g α y) := by
  intro y hy
  exact (chartMetricC2Close_posDef (I := I) hclose hHref hlt y hy).isUnit

/-- Entrywise inverse perturbation for finite matrices.  The estimate follows
from `A⁻¹ - B⁻¹ = A⁻¹ (B - A) B⁻¹`; the explicit inverse-entry bounds are the
usual finite-dimensional condition-number input. -/
theorem matrixInvEntry_sub_le
    {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : IsUnit A) (hB : IsUnit B)
    {η a b : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hAB : ∀ i j, |A i j - B i j| ≤ η)
    (hAi : ∀ i j, |A⁻¹ i j| ≤ a)
    (hBi : ∀ i j, |B⁻¹ i j| ≤ b) :
    ∀ i j, |A⁻¹ i j - B⁻¹ i j| ≤
      (Fintype.card n : ℝ) ^ 2 * a * η * b := by
  classical
  have hinv : A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ :=
    Matrix.inv_sub_inv ⟨fun _ => hB, fun _ => hA⟩
  intro i j
  have hinner (k : n) :
      |∑ l, (B k l - A k l) * B⁻¹ l j| ≤
        (Fintype.card n : ℝ) * η * b := by
    calc
      |∑ l, (B k l - A k l) * B⁻¹ l j|
          ≤ ∑ l, |(B k l - A k l) * B⁻¹ l j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l, η * b := Finset.sum_le_sum fun l _ => by
        rw [abs_mul]
        have hBA : |B k l - A k l| ≤ η := by
          simpa [abs_sub_comm] using hAB k l
        exact mul_le_mul hBA (hBi l j) (abs_nonneg _) (by positivity)
      _ = (Fintype.card n : ℝ) * η * b := by simp [mul_assoc]
  have hterm (k : n) :
      |A⁻¹ i k * (∑ l, (B k l - A k l) * B⁻¹ l j)| ≤
        a * ((Fintype.card n : ℝ) * η * b) := by
    rw [abs_mul]
    exact mul_le_mul (hAi i k) (hinner k) (abs_nonneg _) (by positivity)
  have hinv' : A⁻¹ - B⁻¹ = A⁻¹ * ((B - A) * B⁻¹) := by
    rw [← Matrix.mul_assoc]
    exact hinv
  have hcoeff := congrArg (fun C : Matrix n n ℝ => C i j) hinv'
  have hcoeff' : A⁻¹ i j - B⁻¹ i j =
      ∑ k, A⁻¹ i k * ∑ l, (B k l - A k l) * B⁻¹ l j := by
    simpa [Matrix.sub_apply, Matrix.mul_apply] using hcoeff
  rw [hcoeff']
  calc
    |∑ k, A⁻¹ i k * ∑ l, (B k l - A k l) * B⁻¹ l j|
        ≤ ∑ k, |A⁻¹ i k * ∑ l, (B k l - A k l) * B⁻¹ l j| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, a * ((Fintype.card n : ℝ) * η * b) :=
          Finset.sum_le_sum fun k _ => hterm k
    _ = (Fintype.card n : ℝ) ^ 2 * a * η * b := by simp; ring


/-- A uniform lower quadratic bound and symmetry imply positive definiteness
pointwise. -/
theorem matrixFieldUniformLowerBound_posDef
    {E n : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Fintype n] [DecidableEq n]
    {H : E → Matrix n n ℝ} {s : Set E} {lam : ℝ}
    (hHref : matrixFieldUniformLowerBound H s lam) (hlam : 0 < lam)
    (hHsymm : ∀ y ∈ s, (H y).IsHermitian) :
    ∀ y ∈ s, (H y).PosDef := by
  intro y hy
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨hHsymm y hy, ?_⟩
  intro x hx
  let v : EuclideanSpace ℝ n := WithLp.toLp 2 x
  have hv : v ≠ 0 := by
    intro hv
    apply hx
    simpa [v] using hv
  have hlower := hHref y hy v
  rw [inner_toEuclideanLin_eq_dotProduct] at hlower
  have hnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
  simpa [v] using (lt_of_lt_of_le (mul_pos hlam hnorm) hlower)

/-- The inverse chart Gram field used by the actual chart Christoffel
coefficients. -/
noncomputable def chartInvGramField
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) (α : M) :
    E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
  fun y i j => chartInvGramOnE (I := I) g α i j y

/-- The matrix-valued inverse chart Gram field is literally the matrix inverse
of the chart Gram field. -/
theorem chartInvGramField_eq_inv_chartGramField
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) (α : M) (y : E) :
    chartInvGramField (I := I) g α y = (chartGramField (I := I) g α y)⁻¹ := by
  ext i j
  rfl

/-- Actual inverse-Gram entries are controlled by C² chart closeness, provided
both inverse matrices have the stated entry bounds.  The missing analytic
producer of these inverse-entry bounds is a uniform ellipticity estimate; this
lemma only packages the finite matrix perturbation calculation. -/
theorem chartMetricC2Close_inverseEntry_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {g₀ g : RiemannianMetric I M} {α : M} {s : Set E} {ε lam a b : ℝ}
    (hclose : chartMetricC2CloseOn (I := I) g₀ g α s ε)
    (hHref : matrixFieldUniformLowerBound (chartGramField (I := I) g₀ α) s lam)
    (hlt : ε < lam) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hInv : ∀ y ∈ s, ∀ (i j : Fin (Module.finrank ℝ E)),
      |chartInvGramField (I := I) g α y i j| ≤ a)
    (hInv₀ : ∀ y ∈ s, ∀ (i j : Fin (Module.finrank ℝ E)),
      |chartInvGramField (I := I) g₀ α y i j| ≤ b) :
    ∀ y ∈ s, ∀ (i j : Fin (Module.finrank ℝ E)),
      |chartInvGramField (I := I) g α y i j -
        chartInvGramField (I := I) g₀ α y i j| ≤
          (Module.finrank ℝ E : ℝ) ^ 2 * a * ε * b := by
  have hε : 0 ≤ ε := hclose.1
  have hlam : 0 < lam := by linarith
  have hunitG := chartMetricC2Close_isUnit (I := I) hclose hHref hlt
  have hpos₀ := matrixFieldUniformLowerBound_posDef hHref hlam
    (fun y hy => chartGramField_isHermitian (I := I) g₀ α y)
  have hunit₀ : ∀ y ∈ s, IsUnit (chartGramField (I := I) g₀ α y) := by
    intro y hy
    exact (hpos₀ y hy).isUnit
  intro y hy i j
  have hmat : ∀ p q,
      |chartGramField (I := I) g α y p q -
        chartGramField (I := I) g₀ α y p q| ≤ ε := by
    rcases hclose.2 y hy with ⟨_, hentries, _, _⟩
    exact hentries
  have hinv := matrixInvEntry_sub_le
    (chartGramField (I := I) g α y) (chartGramField (I := I) g₀ α y)
    (hunitG y hy) (hunit₀ y hy) hε ha hb hmat (hInv y hy) (hInv₀ y hy) i j
  simpa [chartInvGramField_eq_inv_chartGramField, Fintype.card_fin] using hinv

/-- The actual chart curvature component in the chart-frame basis. -/
noncomputable def chartCurvatureComponent
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) (α : M) (y : E)
    (i j k m : Fin (Module.finrank ℝ E)) : ℝ :=
  (Module.finBasis ℝ E).repr
    (MorganTianLib.chartCurvature (I := I) g α y
      ((Module.finBasis ℝ E) i) ((Module.finBasis ℝ E) j)
      ((Module.finBasis ℝ E) k)) m

/-- The chart-curvature basis formula identifies the preceding coefficient
with the explicit Christoffel and first-Christoffel-derivative expression. -/
theorem chartCurvatureComponent_eq_formula
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
      {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
      {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : RiemannianMetric I M) (α : M) {y : E}
    (hy : y ∈ interior (extChartAt I α).target)
    (i j k m : Fin (Module.finrank ℝ E)) :
    chartCurvatureComponent (I := I) g α y i j k m =
      partialDeriv (E := E) i (chartChristoffel (I := I) g α j k m) y -
      partialDeriv (E := E) j (chartChristoffel (I := I) g α i k m) y +
      ∑ r, (chartChristoffel (I := I) g α j k r y *
              chartChristoffel (I := I) g α i r m y -
            chartChristoffel (I := I) g α i k r y *
              chartChristoffel (I := I) g α j r m y) := by
  rw [chartCurvatureComponent, MorganTianLib.chartCurvature_basis (I := I) g α hy i j k]
  simp only [map_sum, map_smul, Module.Basis.repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one,
    Finsupp.finsetSum_apply, Finsupp.single_apply,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

end PoincareConjecture.ParallelImplementation.NeckC2Control
