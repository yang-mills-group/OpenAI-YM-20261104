import YM.Integration.WilsonThermometerRegisteredCenteredInvoice

/-! The restoring price for the true connected reading needs only the three
singleton means and the proper modes of its independently declared inverse. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerRegisteredCenteredWallet
open Finset Marker Extra.Trajectories Primitives.GCC.Anchor Comparison.RG02
open WilsonThermometerCenteredAlgebra WilsonThermometerCenteredScalar WilsonThermometerRegisteredSingletonCenter
open WilsonFiniteOrdinaryInverse
open scoped Classical BigOperators
local notation "J" => Stock.census (Fin 3)

def shortened (Q:Poly J):Poly J:=inverseMass Q-Poly.send full ((inverseMass Q).part full)

private theorem quiet_solo (v:Fin 3):face {v}≠(J).quiet:=by fin_cases v <;> decide
private theorem incomplete (v:Fin 3):face {v}≠full:=by fin_cases v <;> decide

private theorem short (Q:Poly J) (s:(J).Mode) (away:s≠full):(shortened Q).part s=(inverseMass Q).part s:=by
  change (inverseMass Q).part s-(Poly.send full ((inverseMass Q).part full)).part s=_
  rw [Poly.part_send,if_neg away,sub_zero]

theorem cheap (w:Fin 3→ℝ) (pos:∀v,0<w v) (Q:Poly J):
    Poly.price w (shortened Q)≤Poly.price w (inverseMass Q):=by
  unfold Poly.price
  apply Finset.sum_le_sum
  intro s _
  by_cases top:s=full
  · subst s
    change Poly.toll w full*‖(inverseMass Q).part full-(Poly.send full ((inverseMass Q).part full)).part full‖≤_
    rw [Poly.part_send,if_pos rfl,sub_self,norm_zero,mul_zero]
    exact mul_nonneg (Poly.worth pos _).le (norm_nonneg _)
  · rw [short Q s top]

theorem single (w:Fin 3→ℝ) (pos:∀v,0<w v) (Q:Poly J)
    (qu:Q.part (J).quiet=1) (v:Fin 3):w v*‖read Q {v}‖≤Poly.price w (shortened Q):=by
  have one:(1:Poly J).part (J).quiet=1:=by rw [Poly.one_part,if_pos rfl]
  have signed:=singleton (1:Poly J) Q one qu v
  change (1*inverseMass Q).part (face {v})=(1:Poly J).part (face {v})-(Q.part (face {v})) at signed
  rw [one_mul,Poly.one_part,if_neg (quiet_solo v),zero_sub] at signed
  have hit:=Poly.member pos (face {v}) (shortened Q)
  rw [short Q _ (incomplete v),signed,norm_neg] at hit
  simpa [Poly.toll,face,WilsonThermometerCenteredScalar.read] using hit

private theorem negPrice (w:Fin 3→ℝ) (a:Poly J):Poly.price w (-a)=Poly.price w a:=by simp [Poly.price,Poly.part_neg]

private theorem subtraction (w:Fin 3→ℝ) (pos:∀v,0<w v) (a b:Poly J):
    Poly.price w (a-b)≤Poly.price w a+Poly.price w b:=by
  rw [sub_eq_add_neg];exact (Poly.addition pos a (-b)).trans_eq (congrArg (fun k=>Poly.price w a+k) (negPrice w b))

theorem correction_price (w:Fin 3→ℝ) (pos:∀v,0<w v) (e:Fin 3→ℂ) (T:ℝ) (covered:∀v,w v*‖e v‖≤T):
    Poly.price w (correction e)≤1+3*T+2*T^2:=by
  let a(v:Fin 3):=Poly.send (face {v}) (e v)
  let c:=Poly.send (face {1,2}) (2*e 1*e 2)
  have head(v):Poly.price w (a v)≤T:=by simpa [a,Poly.solo,Poly.toll,face] using covered v
  have pay:(∏ i ∈ ({1,2}:Finset (Fin 3)),w i)=w 1*w 2:=by
    rw [Finset.prod_insert (show (1:Fin 3)∉({2}:Finset (Fin 3)) by decide),Finset.prod_singleton]
  have joined:Poly.price w c=2*(w 1*‖e 1‖)*(w 2*‖e 2‖):=by norm_num [c,Poly.solo,Poly.toll,face,norm_mul,pay];ring
  have pair:Poly.price w c≤2*T^2:=by
    rw [joined,pow_two]
    exact (by have z:=mul_le_mul (covered 1) (covered 2) (mul_nonneg (pos 2).le (norm_nonneg _))
                ((mul_nonneg (pos 1).le (norm_nonneg _)).trans (covered 1))
              linarith )
  have a₀:=subtraction w pos (1:Poly J) (a 0)
  have a₁:=subtraction w pos (1-a 0) (a 1)
  have a₂:=subtraction w pos (1-a 0-a 1) (a 2)
  have end₀:=Poly.addition pos (1-a 0-a 1-a 2) c
  change Poly.price w (1-a 0-a 1-a 2+c)≤_
  rw [Poly.one_price] at a₀
  linarith only [a₀,a₁,a₂,end₀,head 0,head 1,head 2,pair]

open private annihilates from YM.Integration.WilsonThermometerCenteredAlgebra

private theorem coefficients (F Q:Poly J) (s:(J).Mode) (live:s≠full):
    (invoice F Q).part s=((shortened Q)*correction (WilsonThermometerRegisteredSingletonCenter.shift F Q)).part s:=by
  let e:=WilsonThermometerRegisteredSingletonCenter.shift F Q
  let M:=correction e
  let tail:=Poly.send full ((inverseMass Q).part full)
  have blank:(M-1).part (J).quiet=0:=by change M.part _-(1:Poly J).part _=0;rw [quiet e,Poly.one_part,if_pos rfl,sub_self]
  have vanishes:(M-1)*tail=0:=annihilates _ blank _
  have whole:tail*M=tail:=by calc
    _=tail+(M-1)*tail:=by ring
    _=tail:=by rw [vanishes,add_zero]
  change ((inverseMass Q)*M).part s=(((inverseMass Q)-tail)*M).part s
  rw [sub_mul,whole]
  change _=((inverseMass Q)*M).part s-tail.part s
  dsimp only [tail];rw [Poly.part_send,if_neg live,sub_zero]

theorem bound (w:Fin 3→ℝ) (pos:∀v,0<w v) (F Q:Poly J) (qu:Q.part (J).quiet=1)
    (S V:ℝ) (physical:∀v,w v*‖read F {v}‖≤S) (filed:Poly.price w (shortened Q)≤V):
    WilsonThermometerRegisteredCenteredInvoice.restoration w F Q≤
      2*(1+V*(1+3*(S+V)+2*(S+V)^2)):=by
  have seated(v):w v*‖WilsonThermometerRegisteredSingletonCenter.shift F Q v‖≤S+V:=by
    unfold WilsonThermometerRegisteredSingletonCenter.shift
    calc
      _≤w v*(‖read F {v}‖+‖read Q {v}‖):=mul_le_mul_of_nonneg_left (norm_sub_le ..) (pos v).le
      _≤S+V:=by rw [mul_add];exact add_le_add (physical v) ((single w pos Q qu v).trans filed)
  have co:=correction_price w pos _ (S+V) seated
  rw [WilsonThermometerRegisteredCenteredInvoice.charge w F Q qu]
  suffices root: (∑s:(J).Mode with s≠full ∧ s≠(J).quiet, Poly.toll w s*‖(invoice F Q).part s‖)≤
       V*(1+3*(S+V)+2*(S+V)^2) by linarith
  calc
    _ = ∑s:(J).Mode with s≠full ∧ s≠(J).quiet, Poly.toll w s*‖(shortened Q*correction (WilsonThermometerRegisteredSingletonCenter.shift F Q)).part s‖:=by
      apply Finset.sum_congr rfl
      intro s hs;rw [coefficients F Q s (Finset.mem_filter.mp hs).2.1]
    _ ≤ Poly.price w (shortened Q*correction (WilsonThermometerRegisteredSingletonCenter.shift F Q)):=Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
      (fun s _ _=> mul_nonneg (Poly.worth pos s).le (norm_nonneg _))
    _ ≤ Poly.price w (shortened Q)*Poly.price w (correction (WilsonThermometerRegisteredSingletonCenter.shift F Q)):=Poly.multiplication pos .. 
    _ ≤ _:=mul_le_mul filed co (Poly.nonnegative pos _) ((Poly.nonnegative pos _).trans filed)

theorem material (w:Fin 3→ℝ) (pos:∀v,0<w v) (capped:∀v,w v≤1) (F Q:Poly J) (qu:Q.part (J).quiet=1)
    (means:∀v,‖read F {v}‖≤1) (income:Poly.price w (inverseMass Q)≤fee J):
    WilsonThermometerRegisteredCenteredInvoice.restoration w F Q≤
      2*(1+fee (J)*(1+3*(1+fee (J))+2*(1+fee (J))^2)):=
  bound w pos F Q qu 1 (fee (J)) (fun v=>(mul_le_of_le_one_left (norm_nonneg _) (capped v)).trans (means v))
    ((cheap w pos Q).trans income)

end YM.Integration.WilsonThermometerRegisteredCenteredWallet
