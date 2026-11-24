import YM.Integration.WilsonSmoothUnitLatticeDifference
import Mathlib.Data.ZMod.Basic

/-! Uniform over the period and the phase on the actual finite grid. All other physical
arguments, including the common center, stay outside the translated unit coordinate. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSmoothUnitFiniteGrid
open Set Finset YM.LocalLTE.Weft
open scoped BigOperators Classical
def width(k:ℕ):ℕ:=(2*k+1).factorial
def offset{k:ℕ}(i:J k):ℕ:=width k/(i.val+1)
def point {N:ℕ}(left h:ℝ)(a:ZMod N):ℝ:=left+(a.val:ℝ)*h

theorem lattice {k:ℕ}(i:J k)(h:ℝ): (width k:ℝ)*h*probe k i=(offset i:ℝ)*h:=by
  have within:i.val+1 ≤ 2*k+1:=i.isLt
  have div:i.val+1 ∣ width k:=Nat.dvd_factorial (by omega) within
  have eqn:(offset i)*(i.val+1)=width k:=Nat.div_mul_cancel div
  have cast:(offset i:ℝ)*((i.val:ℝ)+1)=width k:=by exact_mod_cast eqn
  unfold probe
  field_simp
  linarith only [congrArg (fun z:ℝ=>z*h) cast]

theorem reading {N:ℕ}[NeZero N](left h:ℝ)(pos:0<h)(f:ℝ → ℝ)(span:ℕ)(fit:span ≤ N)
    (clear:∀t:ℝ,t ≤ left+(span:ℝ)*h ∨ left+(N:ℝ)*h ≤ t → f t=0)
    (d:ℕ)(price:d ≤ span)(a:ZMod N):
    f (point left h a+(d:ℝ)*h)=f (point left h (a+(d:ZMod N))):=by
  have cast:(a+(d:ZMod N)).val=(a.val+d)%N:=by
    calc
      _=(((a.val+d:ℕ):ZMod N)).val:=by rw [Nat.cast_add,ZMod.natCast_zmod_val]
      _=_:=ZMod.val_natCast N _
  unfold point
  rw [cast]
  by_cases inner:a.val+d<N
  · rw [Nat.mod_eq_of_lt inner,Nat.cast_add];ring_nf
  have wraps:N ≤ a.val+d:=Nat.le_of_not_gt inner
  have back:a.val+d-N<N:=by have:=a.val_lt;omega
  rw [Nat.mod_eq_sub_mod wraps,Nat.mod_eq_of_lt back]
  rw [clear _ (Or.inr (by
    have rising:(N:ℝ) ≤ (a.val:ℝ)+d:=by exact_mod_cast wraps
    nlinarith only [mul_le_mul_of_nonneg_right rising pos.le]))]
  apply Eq.symm
  apply clear
  apply Or.inl
  apply add_le_add_right
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (show a.val+d-N ≤ span by have:=a.val_lt;omega)) pos.le

theorem original {N:ℕ}[NeZero N](k:ℕ)(live:0<k)(left h:ℝ)(pos:0<h)(fit:width k ≤ N)
    (f:ℝ → ℝ)(regular:ContDiff ℝ (↑(2*k+1):WithTop ℕ∞) f)
    (clear:∀t:ℝ,t ≤ left+(width k:ℝ)*h ∨ left+(N:ℝ)*h ≤ t → f t=0)
    (M:ZMod N → ℝ)(economic:∀a,0 ≤ M a)
    (bound:∀a t,t∈Icc (point left h a) (point left h a+(width k:ℝ)*h) →
      |iteratedDeriv (2*k+1) f t| ≤ M a):
    |∑a:ZMod N,deriv f (point left h a)| ≤
      WilsonPosteriorProjectionStencil.cost k ⟨1,by omega⟩*(∑a,M a)*((width k:ℝ)*h)^(2*k):=by
  let turns(i:J k):ZMod N ≃ ZMod N:=Equiv.addRight ((offset i):ZMod N)
  have ht:0<(width k:ℝ)*h:=mul_pos (by exact_mod_cast Nat.factorial_pos (2*k+1)) pos
  apply WilsonSmoothUnitLatticeDifference.smooth k live _ ht _ f regular turns _ M economic bound
  intro a i
  rw [lattice]
  exact reading left h pos f _ fit clear _ (Nat.div_le_self _ _) a

end YM.Integration.WilsonSmoothUnitFiniteGrid
