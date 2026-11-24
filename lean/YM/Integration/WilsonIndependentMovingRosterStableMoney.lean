import YM.Integration.WilsonIndependentMatchedRosterMoney

/-! Only the external slot changes angular and engineering rulers. The
combined rate retains its full finite grade and the number of stable slots. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentMovingRosterStableMoney

open WilsonCoeffUV WilsonCoeffUV.Mer
open WilsonIndependentMatchedRosterTariff WilsonIndependentMatchedRosterPowers
open scoped BigOperators

variable {n:ℕ}

def fees (u b:ℕ)(d w:Fin (n+1)→ℕ)(A B:Fin (n+1)→ℝ)(z δ x T:ℝ):Fin (n+1)→ℝ:=
  Fin.cons (α:=fun _=>ℝ) (offer u b (d 0) (w 0) z (δ/T) (x/T) (A 0) (B 0))
    (fun i=>offer u b (d i.succ) (w i.succ) z δ x (A i.succ) (B i.succ))

theorem charge (u b d w:ℕ)(z δ x T A B:ℝ)(zoom:1≤T) :
    offer u b d w z (δ/T) (x/T) A B=T^d*offer u b d w z δ x A B:=by
  have ht:T≠0:=(zero_lt_one.trans_le zoom).ne'
  have same:(δ/T)/(x/T)=δ/x:=by rw [div_div_div_cancel_right₀ ht]
  rw [offer,weight,same,div_pow,inv_div];unfold offer weight
  ring

theorem original (u b:ℕ)(d w:Fin ((n+1)+1)→ℕ)(A B:Fin ((n+1)+1)→ℝ)(δ x T z t:ℝ)
    (C:ℝ)(zoom:1≤T)(box:0≤z):
    let a:=fees u b d w A B z δ x T
    let amount:=Fin.cons (α:=fun _=>ℝ) (T^u*a 0) (Fin.tail a)
    let home:=fun s=>offer u b (d s) (w s) z δ x (A s) (B s)
    pearlB u b (4*max z (T*z)) t*nuP C (n+1) amount =
      T^(d 0+u+u)*(pearlB u b (4*z) t*nuP C (n+1) home):=by
  intro a amount home
  have far:a 0=T^(d 0)*home 0:=charge u b (d 0) (w 0) z δ x T (A 0) (B 0) zoom
  have tail:Fin.tail amount=Fin.tail home:=by
    funext i
    rfl
  have leading:amount 0=T^u*(T^(d 0)*home 0):=by
    change T^u*a 0=_
    rw [far]
  have cap:max z (T*z)=T*z:=max_eq_right (le_mul_of_one_le_left box zoom)
  have geom:pearlB u b (4*(T*z)) t=T^u*pearlB u b (4*z) t:=by
    unfold pearlB
    rw [show 4*(4*(T*z))=T*(4*(4*z)) by ring,mul_pow]
    ring
  rw [cap,geom,nuP,nuP,tail,leading]
  simp only [pow_add]
  ring

end YM.Integration.WilsonIndependentMovingRosterStableMoney
