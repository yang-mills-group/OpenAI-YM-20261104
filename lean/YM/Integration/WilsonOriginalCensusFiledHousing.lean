import YM.Integration.WilsonOriginalCensusFiledOpticalCredit

/-! Remove the transported radius only after the genuine occupied withdrawal, on bounded capture housing. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusFiledHousing
open Finset Lattice Wilson RG Marker QuadraticLocal QuadraticLocal.Advent PhysicalNext.Repeat.Legato
open Multi Comparison.RG02.Cumulants
open WilsonOriginalOccupiedCorridor WilsonCapturedPrimarySoftPartition
open scoped BigOperators Classical

def blockCost (d n:ℕ):ℝ:=(2:ℝ)^n*(2*(((2^(2^n):ℕ):ℝ)*Real.exp (102*(d:ℝ)))*n*Real.exp n)
def fare {V:Type}[DecidableEq V]{J:Census V}(s:J.Mode)(d:ℕ):ℝ:=
  ((shards J s).card:ℝ)+4*(1+blockCost d s.val.card)

theorem enclosed {n:Side}(p:BudgetPoint)(Z:Support n)(d k:ℕ)(right:p.supportExponent=100)(span:coverNumber p.B Z≤d):
    WilsonOriginalFlatOccupiedRate.bill p Z 1 k ≤ blockCost d k:=by
  unfold WilsonOriginalFlatOccupiedRate.bill WilsonOriginalFlatOccupiedRate.roof blockCost
  simp only [right,max_self,one_pow,mul_one]
  have ht:Real.exp ((100+2:ℝ)*(coverNumber p.B Z))≤Real.exp (102*(d:ℝ)):=by
    apply Real.exp_le_exp.mpr
    norm_num1
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast span) (by norm_num)
  gcongr

theorem shrinking {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]{b i:ℕ}(bt : b ≤ i)(w:V→ℝ)(wp:∀v,0<w v)
    (s:(Stock.census V).Mode): Poly.toll (wallet R w bt) s ≤ Poly.toll w s:=by
  have shrunk:∀v,wallet R w bt v ≤ w v:=by
    refine Nat.decreasingInduction (motive:=fun j jt=>∀v,wallet R w jt v ≤ w v) ?_ ?_ bt
    · intro j jt ih v
      rw [show wallet R w jt.le=Stoop.radius (wallet R w jt) (factor R j) from Nat.decreasingInduction_succ_left ..]
      exact (div_le_self (positive R w wp jt v).le (le_max_left ..)).trans (ih v)
    · rw [show wallet R w (le_refl i)=w from Nat.decreasingInduction_self ..]
      exact fun _=>le_rfl
  exact prod_le_prod (fun v _=>(positive R w wp bt v).le) (fun v _=>shrunk v)

theorem clear {A val g fee quoted price H κ card:ℝ}(wallet:1≤A)(f:fee≤A)(fq:0≤fee)(qp:0≤quoted)
    (bound:quoted≤price)(clock:H*κ≤1)(cp:0≤card)(gp:0≤g)
    (paid:A*val≤g*(card+4*(fee+quoted)*H*κ)):
    val≤g*(card+4*(1+price)):=by
  have fare:fee+quoted≤A*(1+price):=calc
    _ ≤ A+price*A:=add_le_add f (bound.trans (le_mul_of_one_le_right (qp.trans bound) wallet))
    _ = _:=by ring
  have core:card+4*(fee+quoted)*H*κ ≤A*(card+4*(1+price)):=calc
    _ = card+4*(fee+quoted)*(H*κ):=by ring
    _ ≤ card+4*(fee+quoted):=add_le_add_right (mul_le_of_le_one_right (by positivity) clock) _
    _ ≤ card*A+4*(A*(1+price)):=add_le_add (le_mul_of_one_le_right cp wallet) (by linarith only [fare])
    _ = _:=by ring
  exact le_of_mul_le_mul_left (calc
    A*val ≤ g*(card+4*(fee+quoted)*H*κ):=paid
    _ ≤ g*(A*(card+4*(1+price))):=mul_le_mul_of_nonneg_left core gp
    _ = A*(g*(card+4*(1+price))):=by ring) (zero_lt_one.trans_le wallet)

end YM.Integration.WilsonOriginalCensusFiledHousing
end
