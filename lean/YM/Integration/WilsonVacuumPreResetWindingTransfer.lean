import YM.Integration.WilsonVacuumPreResetWindingNodes
import Mathlib.LinearAlgebra.Lagrange

/-! A signed transfer of the incoming quiet error within one true finite
program. Both ends use the same forest Gaussian and the same kinetic reset. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetWindingTransfer
open Function Filter Finset Lattice Wilson RG Precision Laurent Tree
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil WilsonCoeffUV.Bank.Realm
open WilsonCoeffUV.Wheel WilsonCoeffUV.Winding WilsonVacuumPreResetWindingNodes
open scoped Classical BigOperators
variable {G:Gauge} {e i m:ℕ} {E:Credit}

private def node (e i:ℕ):ℝ:=(i:ℝ)/(e+1:ℕ)
private def slope (P:Polynomial ℝ):ℝ:=∑j∈range (P.natDegree+1),|P.coeff j|

private theorem increment (P:Polynomial ℝ){t:ℝ}(lower:0 ≤ t)(upper:t ≤ 1):
    |P.eval t-P.eval 0| ≤ slope P*t:=by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_self P.natDegree) t,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_self P.natDegree) 0,
    ←Finset.sum_sub_distrib,slope,Finset.sum_mul]
  apply (abs_sum_le_sum_abs ..).trans
  apply sum_le_sum
  intro j _
  rw [←mul_sub,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  cases j with
  | zero=>simpa using lower
  | succ k=>
    rw [zero_pow (by omega),sub_zero,abs_of_nonneg (pow_nonneg lower _),pow_succ]
    exact mul_le_of_le_one_left lower (pow_le_one₀ lower upper)

theorem observed (d:ℕ):∃C:ℝ,0 ≤ C ∧ ∀(P:Polynomial ℝ)(A t:ℝ),P.natDegree ≤ d→
    0 ≤ A→0 ≤ t→t ≤ 1→(∀u,|u| ≤ 1→|P.eval u| ≤ A)→|P.eval t-P.eval 0| ≤ C*A*t:=by
  let S:=range (d+1)
  let L:=Lagrange.basis S (node d)
  let C:=∑k∈S,slope (L k)
  have nn(k:ℕ):0 ≤ slope (L k):=Finset.sum_nonneg fun _ _=>abs_nonneg _
  refine ⟨C,sum_nonneg (fun j _=>nn j),?_⟩
  intro P A t degree a lo hi paid
  have inj:Set.InjOn (node d) (↑S):=by
    intro k _ j _ h
    exact_mod_cast (div_left_inj' (by positivity:(d+1:ℕ)≠(0:ℝ))).mp h
  have deg:P.degree < (S.card:WithBot ℕ):=P.degree_le_natDegree.trans_lt (by
    rw [show S.card=d+1 from card_range ..]; exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_of_le degree))
  have formula(u:ℝ):P.eval u=∑j∈S,P.eval (node d j)*(L j).eval u:=by
    conv_lhs => rw [Lagrange.eq_interpolate (s:=S) (v:=node d) (f:=P) inj deg,
      Lagrange.interpolate_apply,Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,L]
  rw [formula t,formula 0,←sum_sub_distrib]
  apply (abs_sum_le_sum_abs ..).trans
  change _ ≤ ((∑k∈S,slope (L k))*A)*t
  rw [sum_mul,sum_mul]
  refine sum_le_sum fun k hk=>?_
  have weight:|node d k| ≤ 1:=by
    dsimp [node]
    rw [abs_of_nonneg (by positivity),div_le_one (by positivity)]
    exact_mod_cast Nat.le_of_lt (Finset.mem_range.mp hk)
  rw [←mul_sub,abs_mul]
  convert mul_le_mul (paid _ weight) (increment _ lo hi) (abs_nonneg _) a using 1
  ring

theorem original (Q:Realm G (e+1) E)(hm:Q.anchor ≤ m)(r:ℕ)(hi:i ≤ e)(s:ℝ)(hs:0<s):
    ∃C:ℝ,0 ≤ C ∧ ∀N,m<N→∀(n:Side)(η:ℝ),0<η→η ≤ 1→
      Enter Q.draws Q.paid N (m+1) e (n*(loose Q.draws m).L) η
        (arborθ s (Q.mint m hm).gear e)→
      ∀x,|unripe Q.draws Q.paid N m (story Q.draws Q.paid N (m+1)).1 n i (r+1) x-
        coil0 Q.draws Q.paid m N n i (r+1) x| ≤ C*η:=by
  obtain ⟨K,positive,nodes⟩:=WilsonVacuumPreResetWindingNodes.original Q hm (r+1) hi s hs
  obtain ⟨C,price,pay⟩:=observed i
  refine ⟨C*K,mul_nonneg price positive,?_⟩
  intro N date n η small unit ticket x
  let S:=mStep Q.draws n m
  let q:=n*(loose Q.draws m).L
  let X:=inlet Q.draws Q.paid N (m+1) q
  let Y:=(story Q.draws Q.paid N (m+1)).1 q
  let D:=η⁻¹•(Y-X)
  obtain ⟨P,degree,evaluated⟩:=WilsonVacuumPreResetWindingPolynomial.original S (repeatF S)
    (freeForms Q.draws N (m+1)) (freeForms Q.draws N m) (roam Q.draws N m n)
    Q.paid X D i (r+1) x
  have actual(t:ℝ):P.eval t=unripe Q.draws Q.paid N m
      (tested Q.draws Q.paid N (m+1) (t/η)) n i (r+1) x:=by
    rw [evaluated t]
    dsimp only [D];rw [smul_smul,←div_eq_mul_inv];rfl
  have bill:=pay P K η degree positive small.le unit (fun t clock=>by
    rw [actual t]
    simpa only [pruce_down] using nodes N date n η t small clock ticket x)
  have start:tested Q.draws Q.paid N (m+1) (0/η)=emera (actionW Q.draws Q.paid N (m+1)):=by
    funext u;simp [WilsonVacuumPreResetWindingNodes.tested,WilsonVacuumPreResetWindingNodes.inlet]
  have finish:tested Q.draws Q.paid N (m+1) (η/η)=(story Q.draws Q.paid N (m+1)).1:=by
    funext u;simp only [WilsonVacuumPreResetWindingNodes.tested,div_self small.ne',one_smul];abel
  rwa [actual η,actual 0,start,finish] at bill

end YM.Integration.WilsonVacuumPreResetWindingTransfer
end
