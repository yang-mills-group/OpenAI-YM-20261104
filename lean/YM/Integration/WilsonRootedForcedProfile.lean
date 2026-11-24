import YM.Integration.WilsonLongContactPriorGasRooted
import Mathlib.Algebra.Polynomial.Coeff

/-! A single scratch variable on the complete original forced cover.
The ordinary squarefree labels and all compatible partners remain in each coefficient. -/
noncomputable section
set_option autoImplicit false
set_option quotPrecheck false
namespace YM.Integration.WilsonRootedForcedProfile
open Lattice RG Wilson Marker Merge Finset Polynomial
open scoped BigOperators Classical
variable {G:Gauge}{n:Side}{V:Type}[DecidableEq V]{Γ:Census V}
variable (A:Activities G n)(P:BudgetPoint)(w:V→ℝ)(f k:ℕ→Poly Γ)
local notation "Y" => fun i=>(A.forced i).support

def letter(i:ℕ):Polynomial (Poly Γ):=C (f i)+C (k i)*X

def cover(U:Config G n)(s:Finset ℕ):Polynomial (Poly Γ):=
  if A.admissible P U s then ∏i∈s,letter f k i else 0

def charge(ρ:ℝ)(i:ℕ):ℝ:=Poly.price w (f i)+ρ*Poly.price w (k i)

private theorem slots(i:ℕ):(letter f k i).coeff 0=f i ∧ (letter f k i).coeff 1=k i:=by
  simp [letter,Polynomial.coeff_add,Polynomial.coeff_mul_X]

private theorem score(s:Finset ℕ):(∏i∈s,letter f k i).coeff 0=∏i∈s,f i:=by
  induction s using Finset.induction_on with
  | empty=>simp [Polynomial.coeff_one]
  | insert i s hi ih=>rw [prod_insert hi,prod_insert hi,Polynomial.mul_coeff_zero,(slots f k i).1,ih]

theorem quiet (U:Config G n)(s:Finset ℕ):(cover A P f k U s).coeff 0=Photo.fronts A f U P s:=by
  by_cases live:A.admissible P U s
  · simpa only [cover,Photo.fronts,if_pos live] using score f k s
  · simp [cover,Photo.fronts,live]

theorem counting (c:ℕ→ℂ)(U:Config G n)(s:Finset ℕ):
    (cover A P f (fun i=>c i • f i) U s).coeff 1=(∑i∈s,c i) • Photo.fronts A f U P s:=by
  by_cases live:A.admissible P U s
  · simp only [cover,Photo.fronts,if_pos live]
    clear live
    induction s using Finset.induction_on with
    | empty=>simp [Polynomial.coeff_one]
    | insert i s hi ih=>
      rw [prod_insert hi,prod_insert hi,sum_insert hi,Polynomial.mul_coeff_one,ih,(slots f _ i).1,(slots f _ i).2,score]
      simp only [mul_smul_comm,smul_mul_assoc,add_smul,add_comm]
  · simp [cover,Photo.fronts,live]

private theorem cash (hw:∀v,0<w v){ρ:ℝ}(rp:0≤ρ)(s:Finset ℕ):
    let z:=∏i∈s,letter f k i
    Poly.price w (z.coeff 0)+ρ*Poly.price w (z.coeff 1)≤∏i∈s,charge w f k ρ i:=by
  induction s using Finset.induction_on with
  | empty=>simp [Polynomial.coeff_one]
  | insert i s hi ih=>
    let z:=∏j∈s,letter f k j
    simp only [prod_insert hi,Polynomial.mul_coeff_zero,Polynomial.mul_coeff_one,(slots f k i).1,(slots f k i).2]
    have q:=Poly.multiplication hw (f i) (z.coeff 0)
    have qf:Poly.price w (f i*z.coeff 1+k i*z.coeff 0)≤
        Poly.price w (f i)*Poly.price w (z.coeff 1)+Poly.price w (k i)*Poly.price w (z.coeff 0):=
      (Poly.addition hw _ _).trans (add_le_add (Poly.multiplication hw ..) (Poly.multiplication hw ..))
    have pay:=add_le_add q (mul_le_mul_of_nonneg_left qf rp)
    have pos:0≤charge w f k ρ i:=add_nonneg (Poly.nonnegative hw _) (mul_nonneg rp (Poly.nonnegative hw _))
    refine pay.trans (le_trans ?_ (mul_le_mul_of_nonneg_left ih pos))
    dsimp [charge]
    nlinarith only [mul_nonneg (mul_nonneg (sq_nonneg ρ) (Poly.nonnegative hw (k i))) (Poly.nonnegative hw (z.coeff 1))]

private theorem receipt (hw:∀v,0<w v){ρ:ℝ}(rp:0≤ρ)(U:Config G n)(s:Finset ℕ):
    ρ*Poly.price w ((cover A P f k U s).coeff 1)≤
      Poly.price w (Photo.fronts A (fun i=>(charge w f k ρ i:ℂ) • (1:Poly Γ)) U P s):=by
  by_cases live:A.admissible P U s
  · simp only [Photo.fronts,cover,if_pos live]
    rw [Finset.prod_smul,prod_const_one,Poly.adapted,Poly.one_price,mul_one,norm_prod]
    have pos (i):0≤charge w f k ρ i:=add_nonneg (Poly.nonnegative hw _) (mul_nonneg rp (Poly.nonnegative hw _))
    simp only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pos _)]
    exact (le_add_of_nonneg_left (Poly.nonnegative hw _)).trans (cash w f k hw rp s)
  · simp [Photo.fronts,cover,live]

theorem clear (U:Config G n)(none:flags P.threshold U=∅)(s:Finset ℕ):
    (cover A P f k U s).coeff 1=0:=by
  by_cases adm:A.admissible P U s
  · have empty:s=∅:=by
      by_contra h
      obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr h
      obtain ⟨x,hit⟩:=(A.forced i).inventory_ne
      have seen:x∈flags P.threshold U:=adm.2 ▸ Finset.mem_biUnion.mpr ⟨i,hi,hit⟩
      simp [none] at seen
    rw [cover, if_pos adm, empty, prod_empty, Polynomial.coeff_one, if_neg one_ne_zero]
  · simp [cover,adm]

theorem original (hw:∀v,0<w v){ρ η:ℝ}(rp:0<ρ)(small:η≤1)(U:Config G n)
    (hit:∀(x:Site n)(L:Finset ℕ),∑i∈Ac.buds Y L {x},charge w f k ρ i≤η):
    Summable (fun s=>(cover A P f k U s).coeff 1) ∧
    Poly.price w (∑'s,(cover A P f k U s).coeff 1) ≤ (if (flags P.threshold U).Nonempty then η/ρ else 0):=by
  classical
  let owners:=fun i=>(charge w f k ρ i:ℂ) • (1:Poly Γ)
  have pos(i):0≤charge w f k ρ i:=add_nonneg (Poly.nonnegative hw _) (mul_nonneg rp.le (Poly.nonnegative hw _))
  have fee(x:Site n)(L:Finset ℕ):∑i∈Ac.buds Y L {x},Poly.price w (owners i)≤η:=by
    simpa only [owners,Poly.adapted,Poly.one_price,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (pos _)] using hit x L
  have certified:=WilsonLongContactPriorGasSum.original A P w owners hw U η small fee
  have full:=certified.1.mul_right ρ⁻¹
  have paid:=Poly.budgeted hw full (f:=fun s=>(cover A P f k U s).coeff 1) (fun s=>by
    apply (le_div_iff₀ rp).2
    rw [mul_comm]
    exact receipt A P w f k hw rp.le U s)
  refine ⟨paid.1,?_⟩
  by_cases rough:(flags P.threshold U).Nonempty
  · rw [if_pos rough]
    have cap: (∑'s,Poly.price w (Photo.fronts A owners U P s))≤η:=by simpa only [if_pos rough] using certified.2.2.1
    exact paid.2.trans (by rw [tsum_mul_right,←div_eq_mul_inv];exact div_le_div_of_nonneg_right cap rp.le)
  · rw [if_neg rough]
    simp only [clear A P f k U (Finset.not_nonempty_iff_eq_empty.mp rough),tsum_zero,Poly.zero_price,le_refl]

def seat (i:ℕ):Site n:=Classical.choose (A.forced i).inventory_ne

theorem owned (i:ℕ):seat A i∈(A.forced i).inventory:=Classical.choose_spec (A.forced i).inventory_ne

theorem profile (hw:∀v,0<w v){η:ℝ}(small:2*η≤1)(U:Config G n)
    (hit:∀(x:Site n)(L:Finset ℕ),∑i∈Ac.buds Y L {x},Poly.price w (f i)≤η)
    (h:Site n→ℂ)(cap:∀x,‖h x‖≤1):
    let H:=fun s:Finset ℕ=>(∑i∈s,h (seat A i)) • Photo.fronts A f U P s
    Summable H ∧ Poly.price w (∑'s,H s) ≤ (if (flags P.threshold U).Nonempty then 2*η else 0):=by
  intro H
  let k:=fun i=>h (seat A i) • f i
  have income(x:Site n)(L:Finset ℕ):∑i∈Ac.buds Y L {x},charge w f k 1 i≤2*η:=by
    refine (Finset.sum_le_sum (g:=fun i=>2*Poly.price w (f i)) (fun i _=>?_)).trans ?_
    · change Poly.price w (f i)+1*Poly.price w (h (seat A i) • f i)≤_
      rw [Poly.adapted,one_mul]
      nlinarith only [mul_nonneg (sub_nonneg.mpr (cap (seat A i))) (Poly.nonnegative hw (f i))]
    · rw [←Finset.mul_sum];exact mul_le_mul_of_nonneg_left (hit x L) (by norm_num)
  have issued:=original A P w f k hw zero_lt_one small U income
  simpa only [k,counting,div_one,H] using issued
end YM.Integration.WilsonRootedForcedProfile
