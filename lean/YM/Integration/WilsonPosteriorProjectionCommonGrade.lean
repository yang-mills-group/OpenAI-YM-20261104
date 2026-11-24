import YM.Integration.WilsonPosteriorProjectionBooking

/-! One finite purchase for all spatial ranks in the prescribed derivative.
At every positive q≤k the original real word stencil requests exactly
`p+1+(stride/q)*q`, and each such height is the identical common grade. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonPosteriorProjectionCommonGrade

open Finset
open scoped BigOperators

def menu (need : ℕ → ℕ) (k : ℕ) := ∑ q ∈ range (k+1), need q
def stride (need : ℕ → ℕ) (k : ℕ) := k.factorial * menu need k
def common (p : ℕ) (need : ℕ → ℕ) (k : ℕ) := p+1+stride need k
def stencil (need : ℕ → ℕ) (k q : ℕ) := stride need k / q

theorem pays (p : ℕ) (need : ℕ → ℕ) (k q : ℕ) (hq : 0<q) (qk : q≤k) :
    need q ≤ stencil need k q ∧ common p need k = p+1+stencil need k q*q := by
  have chip : q ∣ k.factorial := Nat.dvd_factorial hq qk
  have slot : q ≤ k.factorial := Nat.le_of_dvd (Nat.factorial_pos _) chip
  have booked : need q ≤ menu need k := Finset.single_le_sum (fun i _ => Nat.zero_le (need i))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le qk))
  have whole : q ∣ stride need k := dvd_mul_of_dvd_left chip _
  constructor
  · apply (Nat.le_div_iff_mul_le hq).mpr
    exact (Nat.mul_le_mul booked slot).trans_eq (Nat.mul_comm ..)
  · rw [common,stencil,Nat.div_mul_cancel whole]

end YM.Integration.WilsonPosteriorProjectionCommonGrade

