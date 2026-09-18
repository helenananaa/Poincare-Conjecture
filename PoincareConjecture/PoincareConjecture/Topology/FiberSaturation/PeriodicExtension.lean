import PoincareConjecture.Topology.FiberSaturation.PeriodIndex
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false
noncomputable section
namespace PoincareConjecture.Topology.FiberSaturation.SmoothBundle
open Set Function
variable {M F : Type*} [TopologicalSpace M] [TopologicalSpace F]

/-- Integer extension of a finite-period parametrization. Smoothness is not
part of this definition: it is proved from agreement on open seam collars. -/
def periodicExtend (T : M ≃ₜ M) (φ : F ≃ₜ F) (P : ℝ × F → M)
    (L : ℝ) (z : ℝ × F) : M :=
  (T ^ periodIndex L z.1) (P (periodRemainder L z.1, (φ ^ periodIndex L z.1) z.2))

/-- The formula on a fixed translated chart, with no floor operation. -/
def periodicCell (T : M ≃ₜ M) (φ : F ≃ₜ F) (P : ℝ × F → M)
    (L : ℝ) (n : ℤ) (z : ℝ × F) : M :=
  (T ^ n) (P (z.1 - (n : ℝ)*L, (φ ^ n) z.2))

theorem periodicExtend_zeroCell (T : M ≃ₜ M) (φ : F ≃ₜ F) (P : ℝ × F → M)
    {L : ℝ} (hL : 0 < L) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) L) (x : F) :
    periodicExtend T φ P L (t,x) = P (t,x) := by
  simp [periodicExtend, periodRemainder, periodIndex_zeroCell hL ht]

/-- Equivariance is established for every integer, not just one step. -/
theorem periodicExtend_translate (T : M ≃ₜ M) (φ : F ≃ₜ F) (P : ℝ × F → M)
    {L : ℝ} (hL : 0 < L) (t : ℝ) (x : F) (n : ℤ) :
    periodicExtend T φ P L (t+(n : ℝ)*L,x) =
      (T ^ n) (periodicExtend T φ P L (t,(φ ^ n) x)) := by
  unfold periodicExtend
  simp only [periodIndex_add_periods hL, periodRemainder_add_periods hL]
  rw [show T ^ (periodIndex L t+n) = T ^ n * T ^ periodIndex L t by
    rw [add_comm, zpow_add]]
  simp only [zpow_add, Homeomorph.mul_apply]

/-- The floor-based formula agrees with P on an entire open seam collar,
including points on both sides of 0 and L. -/
theorem periodicExtend_on_collar (T : M ≃ₜ M) (φ : F ≃ₜ F) (P : ℝ × F → M)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (hεL : ε < L)
    (hseam : ∀ t x, t ∈ Ioo (-ε) ε → P (t+L,x) = T (P (t,φ x)))
    {t : ℝ} (ht : t ∈ Ioo (-ε) (L+ε)) (x : F) :
    periodicExtend T φ P L (t,x) = P (t,x) := by
  by_cases hneg : t < 0
  · have hi : periodIndex L t = -1 := by
      apply periodIndex_eq hL (-1)
      constructor <;> norm_num <;> linarith [ht.1]
    calc
      periodicExtend T φ P L (t,x) = T.symm (P (t+L,φ.symm x)) := by
        simp [periodicExtend,periodRemainder,hi]
      _ = P (t,x) := by
        rw [hseam t (φ.symm x) ⟨ht.1,by linarith⟩]
        simp
  · have ht0 : 0 ≤ t := le_of_not_gt hneg
    by_cases htL : t < L
    · exact periodicExtend_zeroCell T φ P hL ⟨ht0,htL⟩ x
    · have hi : periodIndex L t = 1 := by
        apply periodIndex_eq hL 1
        constructor <;> norm_num <;> linarith [ht.2]
      calc
        periodicExtend T φ P L (t,x) = T (P (t-L,φ x)) := by
          simp [periodicExtend,periodRemainder,hi]
        _ = P (t,x) := by
          have heq := hseam (t-L) x ⟨by linarith,by linarith [ht.2]⟩
          simpa using heq.symm

/-- On every enlarged translated period, the extension equals a fixed chart. -/
theorem periodicExtend_eq_cell (T : M ≃ₜ M) (φ : F ≃ₜ F) (P : ℝ × F → M)
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (hεL : ε < L)
    (hseam : ∀ t x, t ∈ Ioo (-ε) ε → P (t+L,x) = T (P (t,φ x)))
    (n : ℤ) {t : ℝ} (ht : t-(n : ℝ)*L ∈ Ioo (-ε) (L+ε)) (x : F) :
    periodicExtend T φ P L (t,x) = periodicCell T φ P L n (t,x) := by
  have h := periodicExtend_translate T φ P hL (t-(n : ℝ)*L) x n
  rw [sub_add_cancel] at h
  rw [periodicExtend_on_collar T φ P hL hε hεL hseam ht] at h
  exact h

end PoincareConjecture.Topology.FiberSaturation.SmoothBundle
