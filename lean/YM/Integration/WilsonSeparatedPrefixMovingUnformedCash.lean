import YM.Integration.WilsonSeparatedPrefixMovingInvoice
import YM.Integration.WilsonSeparatedPrefixMovingNextCalendar

/-! An arbitrary finite set of true one-field receipts and one full sum over
the possible date of its first connection to the exterior. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixMovingUnformedCash
open WilsonCoeffUV WilsonCoeffUV.Shard WilsonCoeffUV.Mer Lattice RG Bank
open Finset WilsonSeparatedPrefixMovingInvoice WilsonSeparatedPrefixMovingCalendar
open scoped BigOperators Topology Classical

def columns : (n:ℕ)→(Fin n→Credit)→Credit
  | 0, _ => Credit.unit
  | n+1, C => (C 0).prodC (columns n (fun i=>C i.succ))

theorem bought {Z:ℝ}(n:ℕ)(C:Fin n→Credit)(x b:Fin n→ℝ)(sold:∀i,Earned Z (C i) (x i) (b i)):
    Earned Z (columns n C) (∏i,x i) (∏i,b i):=by
  induction n with
  | zero=>simpa only [columns,Finset.univ_eq_empty,Finset.prod_empty] using constant Z 1 zero_le_one
  | succ n ih=>
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ (f:=b)]
    exact (sold 0).mul (ih (fun i=>C i.succ) (fun i=>x i.succ) (fun i=>b i.succ) (fun i=>sold i.succ))

theorem calendar {G:Gauge}{e:ℕ}{E:Credit}{A:Type*}[SeminormedAddCommGroup A]
    (R:Realm G e E)(C:Credit)(t m N:ℕ)(live:R.anchor ≤ t)(base:t ≤ m)(amount:ℝ)
    (pa:0 ≤ amount)(D:ℕ→A)(w:∀j<N,‖D j‖ ≤ amount*C.buy (epoch R t (m+j+1))*
      (paceT R.draws.S m (m+j+1))^2):
    ‖∑j∈range N,D j‖ ≤ 2*amount*(C.finances 1 le_rfl).buy (epoch R t m):=by
  let x:=fun j=>paceT R.draws.S m (m+j+1)
  let c:=amount*(C.finances 1 le_rfl).buy (epoch R t m)
  have cp:0≤c:=mul_nonneg pa (zero_le_one.trans (Credit.purchase _ (window R t m m live base le_rfl).1))
  have single (j:ℕ)(hj:j∈range N):‖D j‖≤c*x j:=by
    have price:=WilsonSeparatedPrefixMovingCalendar.credit R C t m (m+j+1) live base (by omega)
    dsimp only [c,x]
    exact (w j (mem_range.mp hj)).trans (by convert mul_le_mul_of_nonneg_left price pa using 1 <;> ring)
  calc
    _≤∑j∈range N,‖D j‖:=norm_sum_le ..
    _≤∑j∈range N,c*x j:=sum_le_sum single
    _=c*∑j∈range N,x j:=by rw [mul_sum]
    _≤_:=by have final:=mul_le_mul_of_nonneg_left (WilsonSeparatedPrefixMovingNextCalendar.selected R.draws.S m N) cp
            exact final.trans_eq (by dsimp only [c];ring)

end YM.Integration.WilsonSeparatedPrefixMovingUnformedCash
