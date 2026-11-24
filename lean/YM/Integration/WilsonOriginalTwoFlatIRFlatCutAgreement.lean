import YM.Integration.WilsonOriginalTwoFlatIRFlatPolynomial

/-! Agreement of truncated connected coefficients passes to every ordinary
face. All products use the original squarefree census. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatIRFlatCutAgreement
open Finset Marker
open WilsonOriginalTwoFlatIRFlatPolynomial (declared deposit)
open scoped Classical BigOperators
variable {V I:Type}[DecidableEq V][Fintype I]{J:Census V}{q:ℕ}
abbrev Series:=PowerSeries ℂ
def EqualTo (p:ℕ)(A B:Series):Prop:=∀e≤p,PowerSeries.coeff e A=PowerSeries.coeff e B

private theorem multiply {p:ℕ}{a b c d:Series}(x:EqualTo p a b)(y:EqualTo p c d):
    EqualTo p (a*c) (b*d):=by
  intro e ep; rw [PowerSeries.coeff_mul,PowerSeries.coeff_mul]
  apply sum_congr rfl
  intro z hz
  have total:z.1+z.2=e:=mem_antidiagonal.mp hz
  rw [x _ (by omega),y _ (by omega)]

private theorem sum_rows {T:Type}[DecidableEq T](t:Finset T){a b:T→Series}{p:ℕ}
    (pay:∀v∈t,EqualTo p (a v) (b v)):EqualTo p (∑j∈t,a j) (∑j∈t,b j):=by
  intro e ep; rw [map_sum,map_sum]
  exact sum_congr rfl (fun j hj=>pay j hj e ep)

private theorem joined {p:ℕ}{a b c d:Cargo J Series}
    (x:∀s,EqualTo p (a.part s) (b.part s))(y:∀s,EqualTo p (c.part s) (d.part s))
    (s:J.Mode):EqualTo p ((a*c).part s) ((b*d).part s):=by
  rw [Cargo.part_mul,Cargo.part_mul]
  apply sum_rows
  intro t _
  apply sum_rows
  intro u _
  split
  · exact multiply (x t) (y u)
  · exact fun _ _=>rfl

omit [Fintype I] in
theorem factors {p:ℕ}(f g:I→Cargo J Series)(pay:∀z s,EqualTo p ((f z).part s) ((g z).part s))
    (F:Finset I)(s:J.Mode):EqualTo p ((∏j∈F,f j).part s) ((∏j∈F,g j).part s):=by
  induction F using Finset.induction_on generalizing s with
  | empty => exact fun _ _=>rfl
  | insert j F fresh old =>
    rw [prod_insert fresh,prod_insert fresh]
    exact joined (pay j) old s

omit [DecidableEq V] [Fintype I] in
theorem retained (cash:I→Fin (q+1)→ℂ)(z:I)(e:ℕ)(eq:e≤q):
    PowerSeries.coeff e (deposit cash z)=cash z ⟨e,Nat.lt_succ_of_le eq⟩:=by
  rw [deposit,map_sum,sum_eq_single (⟨e,Nat.lt_succ_of_le eq⟩:Fin (q+1))]
  · rw [PowerSeries.coeff_mul_C,PowerSeries.coeff_X_pow]; simp
  · intro j _ miss
    have diff:j.val≠e:=fun h=>miss (Fin.ext h)
    rw [PowerSeries.coeff_mul_C,PowerSeries.coeff_X_pow]; simp [Ne.symm diff]
  · simp

def ordinary (mode:I→J.Mode)(L:I→Series):Cargo J Series:=∏j,(1+Cargo.send (mode j) (L j))

theorem original (mode:I→J.Mode)(cash:I→Fin (q+1)→ℂ)(p:ℕ)(order:p≤q)(L:I→Series)
    (receipts:∀j (e:Fin (q+1)),e.val≤p→cash j e=PowerSeries.coeff e.val (L j))
    (s:J.Mode):EqualTo p ((declared mode cash).part s) ((ordinary mode L).part s):=by
  apply factors
  intro j t h hp
  simp only [Cargo.part_plus,map_add,Cargo.part_send]
  by_cases atMark:t=mode j
  · simp only [atMark,if_true]
    rw [retained cash j h (hp.trans order)]
    rw [receipts j ⟨h,Nat.lt_succ_of_le (hp.trans order)⟩ hp]
  · simp [atMark]

end YM.Integration.WilsonOriginalTwoFlatIRFlatCutAgreement
end
