import YM.MSbar.CrossH.Gaunt
set_option autoImplicit false
noncomputable section
namespace YM.MSbar.CrossH
open Function Filter Whisk Lis Measuring Cacao Push Uniform Lattice
open scoped Topology BigOperators ContDiff Classical
variable {σ ι:Type}[Fintype σ][DecidableEq σ]
open Polynomial MvPolynomial
local notation "P"=> Cacao.Pot σ
local notation "∆"=>PowerSeries.coeff
variable {n:Side}{l:σ→Site n}{a b w t u:ℝ}{f g:PowerSeries (Cacao.Pot σ)}{m s k r v p:ℕ}(z:σ→σ→ℝ)
local notation "K!"=>Tin l a s m w
namespace Tin
variable (hg:Kind f)(hh:Kind g)(h:∀ i,i<r→PowerSeries.coeff i f=PowerSeries.coeff i g)
include hg hh h
lemma chainAll (i y:ℕ)(he:i<r): Ride f z i y=Ride g z i y:=by
    induction y using Nat.strong_induction_on generalizing i with
    | h x ih=> cases x with
               | zero=> rw [Ride,Ride,began hg,began hh,h _ he]
               | succ x=> rw [lamp i x _ hg,lamp i x _ hh, ih x (by omega) _ he]; refine congrArg (_ • ·) (congrArg (_ + ·) (?_: tolly f z i x= tolly g z i x))
                          unfold tolly; refine Finset.sum_congr rfl fun j hj=> Finset.sum_congr rfl fun p hp=>?_ ; have hk : j.1+j.2=i:=Finset.HasAntidiagonal.mem_antidiagonal.mp hj; have hp':p.1+p.2=x:= Finset.HasAntidiagonal.mem_antidiagonal.mp hp
                          rw [ih p.1 (by omega) j.1 (by omega), ih p.2 (by omega) j.2 (by omega)]
omit hg hh h in
lemma layer0 (hf:Kind f) (x:ℕ): Ride f z 0 x=0:=by
    change (∆ 0 (normalized z f)).coeff x=_; rw [(airy hf).1]; simp
lemma match_ge (q:ℕ) : tolly f z r q = tolly g z r q:=by
    unfold tolly; refine Finset.sum_congr rfl fun i hi=> Finset.sum_congr rfl fun j hj=> ?_; have he:i.1+i.2=r:=Finset.HasAntidiagonal.mem_antidiagonal.mp hi
    by_cases hx:i.1=0
    · rw [hx,layer0 z hg, layer0 z hh]; simp [juncture]
    by_cases ht:i.2=0
    · rw [ht,layer0 z hg,layer0 z hh]; simp [juncture]
    rw [chainAll z hg hh h _ _ (by omega), chainAll z hg hh h _ _ (by omega)]
noncomputable def evened (r x:ℕ)(p:Pot σ) (f:PowerSeries (Cacao.Pot σ)): Cacao.Pot σ:= Ride f z r x
lemma charge(x:ℕ): Ride f z r (x+1)-Ride g z r (x+1)= (x+1:ℝ)⁻¹ • (stove z (Ride f z r x- Ride g z r x)):=by
    rw [lamp r x _ hg, lamp r x _ hh,match_ge z hg hh h, ← smul_sub,map_sub,add_sub_add_right_eq_sub]
variable (hk:1≤w)(hv:0≤a)(hx:LoopNet l a s z b) (hp:Tin l a s (m+2*v) w (PowerSeries.coeff r f-PowerSeries.coeff r g) t)
include hk hv hp hx
lemma opened (i:ℕ)(he:i≤ v): Tin l a s (m+2*(v-i)) w (Ride f z r i -Ride g z r i) ((b/w^2)^i*t):=by
   have hw:0<w:=zero_lt_one.trans_le hk; induction i with
   | zero=> rw [Ride,Ride,began hh,began hg,Nat.sub_zero,pow_zero,one_mul]; exact hp
   | succ k ih=>
      have ht := ih (by omega); rw [show m+2*(v-k)=m+2*(v-(k+1))+2 from (by omega)] at ht; have he:= weather z hw hv hx ht; let K':= (k+1:ℝ); rw [charge z hg hh h]; refine (Tin.real hw K'⁻¹ he).it hw ?_ le_rfl; apply (mul_le_of_le_one_left he.1 (show |K'⁻¹| ≤ 1 from (by rw [abs_inv,abs_of_nonneg (by unfold K'; positivity)]; exact inv_le_one_of_one_le₀ (by unfold K';simp)))).trans_eq; ring
lemma burn (he: v= Whisk.ribbon p k)(hE:Expanse f p k)(hV:Expanse g p k)(hr:r≤k): let G:=PowerSeries.coeff r f- PowerSeries.coeff r g; Tin l a s m w (PowerSeries.coeff r (confect z f)- PowerSeries.coeff r (confect z g)-G) ((∑ i∈ Finset.range v,b^(i+1))*(t/w^2)):=by
   let S:= Finset.range v; have hw:0<w:=zero_lt_one.trans_le hk; let F(i):= Ride f z r (i+1)- Ride g z r (i+1); have hB:=hx.hope; have hT:= hp.dec
   have h(i)(hi:i∈S): Tin l a s m w (F i) (b^(i+1)*(t/w^2)):=by
       have hv':i+1≤v:=Finset.mem_range.mp hi
       refine (opened z hg hh h hk hv hx hp _ hv').it hw ?_ (by omega)
       have he:w^2≤ (w^2)^(i+1):=by have ht:=pow_le_pow_right₀ (one_le_pow₀ (n:=2) hk) (Nat.le_add_left 1 i : 1≤ i+1); rwa [pow_one] at ht -- type annotate
       rw [div_pow]; exact (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < w^2) he) hT).trans_eq (by ring)
   have hz:= Tin.pool (t:=fun i=>b^(i+1)*(t/w^2)) hw F S h; rw [← Finset.sum_mul] at hz; intro G; convert hz using 1; rw [stands hg hE hr,stands hh hV hr,← Finset.sum_sub_distrib, ← he,Finset.sum_range_succ', show Ride f z r 0-Ride g z r 0=G from ?_,add_sub_cancel_right]; exact (by rw [Ride,Ride,began hg,began hh]) -- inspect
end Tin
end YM.MSbar.CrossH
