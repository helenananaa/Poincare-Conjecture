import Mathlib
set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
open scoped BigOperators
abbrev Idx := Fin 3
abbrev Mat := Idx → Idx → ℝ
abbrev First := Idx → Idx → Idx → ℝ
abbrev Second := Idx → Idx → Idx → Idx → ℝ
/-- d a i j represents the coordinate derivative ∂a g_ij. -/
def lowerChristoffel (d : First) (k i j : Idx) : ℝ :=
  (1/2:ℝ)*(d i j k+d j i k-d k i j)
def christoffel (h : Mat) (d : First) (k i j : Idx) : ℝ :=
  ∑ l : Idx, h k l*lowerChristoffel d l i j
/-- Polarized formula for ∂a(g inverse); diagonal inputs recover -h (∂a g) h. -/
def inverseDerivativePolar (h k : Mat) (d : First) (a i j : Idx) : ℝ :=
  -(∑ r : Idx, ∑ s : Idx, h i r*d a r s*k s j)
def gammaPrincipal (h : Mat) (dd : Second) (a k i j : Idx) : ℝ :=
  (1/2:ℝ)*∑ l : Idx, h k l*(dd a i j l+dd a j i l-dd a l i j)
def gammaQuadratic (h k : Mat) (d e : First) (a r i j : Idx) : ℝ :=
  ∑ l : Idx, inverseDerivativePolar h k d a r l*lowerChristoffel e l i j
def gammaDerivative (h : Mat) (d : First) (dd : Second) (a k i j : Idx) : ℝ :=
  gammaPrincipal h dd a k i j+gammaQuadratic h h d d a k i j
def ricciPrincipal (h : Mat) (dd : Second) (i j : Idx) : ℝ :=
  ∑ k : Idx, (gammaPrincipal h dd k k i j-gammaPrincipal h dd j k i k)
def ricciQuadratic (h k : Mat) (d e : First) (i j : Idx) : ℝ :=
  (∑ a : Idx, (gammaQuadratic h k d e a a i j-gammaQuadratic h k d e j a i a))+
  ∑ a : Idx, ∑ b : Idx,
    (christoffel h d a a b*christoffel k e b i j-
    christoffel h d a j b*christoffel k e b i a)
def ricci (h : Mat) (d : First) (dd : Second) (i j : Idx) : ℝ :=
  (∑ k : Idx, (gammaDerivative h d dd k k i j-gammaDerivative h d dd j k i k))+
  ∑ k : Idx, ∑ l : Idx,
    (christoffel h d k k l*christoffel h d l i j-
    christoffel h d k j l*christoffel h d l i k)
def deturckVector (h : Mat) (d : First) (k : Idx) : ℝ :=
  ∑ a : Idx, ∑ b : Idx, h a b*christoffel h d k a b
def vectorPrincipal (h : Mat) (dd : Second) (a k : Idx) : ℝ :=
  ∑ p : Idx, ∑ q : Idx, h p q*gammaPrincipal h dd a k p q
def vectorQuadratic (h : Mat) (d : First) (a k : Idx) : ℝ :=
  ∑ p : Idx, ∑ q : Idx,
    (inverseDerivativePolar h h d a p q*christoffel h d k p q+
    h p q*gammaQuadratic h h d d a k p q)
def vectorDerivative (h : Mat) (d : First) (dd : Second) (a k : Idx) : ℝ :=
  vectorPrincipal h dd a k+vectorQuadratic h d a k
def liePrincipal (g h : Mat) (dd : Second) (i j : Idx) : ℝ :=
  ∑ k : Idx, (g k j*vectorPrincipal h dd i k+g i k*vectorPrincipal h dd j k)
def lieQuadraticRaw (g h : Mat) (d : First) (i j : Idx) : ℝ :=
  ∑ k : Idx, (deturckVector h d k*d k i j+
    g k j*vectorQuadratic h d i k+g i k*vectorQuadratic h d j k)
def lieMetric (g h : Mat) (d : First) (dd : Second) (i j : Idx) : ℝ :=
  ∑ k : Idx, (deturckVector h d k*d k i j+
    g k j*vectorDerivative h d dd i k+g i k*vectorDerivative h d dd j k)
/-- The covariant metric has been eliminated from these polarized lower-order terms. -/
def lieQuadratic (h k : Mat) (d e : First) (i j : Idx) : ℝ :=
  (∑ r : Idx, ∑ a : Idx, ∑ b : Idx, ∑ l : Idx,
    h a b*k r l*lowerChristoffel d l a b*e r i j)+
  (∑ a : Idx, ∑ b : Idx,
    (inverseDerivativePolar h k d i a b*lowerChristoffel e j a b+
    inverseDerivativePolar h k d j a b*lowerChristoffel e i a b))-
  (∑ a : Idx, ∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
    h a b*d i j r*k r l*lowerChristoffel e l a b)-
  (∑ a : Idx, ∑ b : Idx, ∑ r : Idx, ∑ l : Idx,
    h a b*d j i r*k r l*lowerChristoffel e l a b)
def deturckQuadratic (h k : Mat) (d e : First) (i j : Idx) : ℝ :=
  -2*ricciQuadratic h k d e i j+lieQuadratic h k d e i j
end PoincareConjecture.ParallelImplementation.CoordinateDeTurckAlgebra
