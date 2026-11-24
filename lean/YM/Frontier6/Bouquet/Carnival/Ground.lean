import YM.Frontier6.Bouquet.Carnival.Teams

/-! Flight price comparisons. Keep positive bandwidth after all projected keys,
 also main residual when deeper. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier
open Function Set Finset Ensemble MeasureTheory Normal Filter Road Forest Tale Spec Curtains Prescription Metric Audit Submodule Fareway
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff Matrix.Norms.Frobenius
open scoped YM.Frontier6.Bouquet
variable {I J L Y: Type}{G:Gauge}{C:Family G}{F:Extraction.Order}{S:Table C.book}
variable [NormedAddCommGroup Y][NormedSpace ℂ Y][NormedSpace ℝ Y][IsScalarTower ℝ ℂ Y]
variable (K:Final C F S){P Q:Ensemble}{d:Slot →ℕ}(i:P) (M:Pod→ℝ) (p:Part d i) (R: Air (S:=S) P I L Y)(B:ℝ)(z: Swing i p R B)
variable {ε δ:ℝ}
set_option quotPrecheck false
local notation "Φ" => landscape K i M p R B
local notation "x"=>z.here
local notation "t"=> R.lengths x i
local notation "q"=> z.radius/t
local notation "σ"=> R.route.floor x

def swingW:= (slope i p:ℝ)+ difference i.val d
lemma overhead : 1 ≤ swingW i (d:=d) none:=by
    let a:=i.val.horizon d; let b:=i.val.arityD d; let c:= dim (normal i.val); have he:a+c≥ 1+b:=by have he:(a:ℤ)> b-(c:ℤ):= horizon_power (i:=i); omega
    change (1:ℝ) ≤ a+((c:ℝ)-b); linarith only [(Nat.cast_le (α:=ℝ).mpr he : ((1+b:ℕ):ℝ) ≤ (↑(a+c):ℝ)), Nat.cast_add (R:=ℝ) a c, Nat.cast_add (R:=ℝ) 1 b,(Nat.cast_one (R:=ℝ))] -- name
lemma swung (w:i.val.Horizon d): swingW i (some w)= -(i.val.track d w:ℝ):=by
    unfold swingW slope difference; dsimp only; have he:= congr_arg (Nat.cast (R:=ℝ)) (horoscope d w); push_cast at he; linarith only [he]
lemma stargaze (d:Slot→ℕ) (r:P→ℝ)(a:ℝ)(ha:0<a)(hr:0<r i): stars d P (update r i a)= stars d P r*(a/r i)^difference i.val d:=by
    let F(j:P):= r j ^ difference j.val d; let g(j:P):= update r i a j ^ difference j.val d; change ∏ j:P,g j=(∏ j:P,F j)*_; have he j (hj:j∈Finset.univ.erase i): g j=F j:= by unfold g; rw [update_of_ne (ne_of_mem_erase hj)]
    rw [← Finset.prod_erase_mul _ g (mem_univ i),← Finset.prod_erase_mul _ F (mem_univ i), Finset.prod_congr rfl he, mul_assoc]; congr 1; unfold g F; rw [update_self,mul_comm, Rate_up a (r i) ha hr]
lemma burden (ε:ℝ): (Φ).freight d z ε= (R.account x * stars d P (R.lengths x)) * (q)^swingW i p * (min σ z.radius)^(-ε):=by
    unfold Air.freight; rw [techno, stargaze i d _ _ z.pos (R.length_pos ..)]; change (R.account x*(q)^slope i p)*_*_= _*_*(min σ z.radius)^(-ε); unfold Audit.Ribbon.ruin swingW; rw [Real.rpow_add (div_pos z.pos (R.length_pos ..)),Real.rpow_natCast]; dsimp only [landscape,roads]; ring
section
variable (he: R.Welkin M) (hd:0<δ)
include he hd
lemma membranes (hδ: 2*δ≤ε): Tempo i p (q)*(Φ).freight d z δ ≤ Tempo i p (q)*(q)^swingW i p*(q)^(-δ)* R.freight d x ε:=by
    rw [burden]; unfold Air.freight Audit.Ribbon.ruin; let r:=z.radius
    let A:=R.account x; let C:= stars d P (R.lengths x); let V:=(q)^swingW i p; let D:=Tempo i p (q); have ht:0<t:=R.length_pos ..; have hP:0<r:=z.pos; have hr: r≤1:=z.edge; have hz:= R.route.ground x; have h:σ≤ t:= (R.route.covered ..|>.1); have hx:0<σ:= hz.1
    have hh:min σ z.radius≥ σ*r:= le_min (by nlinarith only [hr,hx]) (by nlinarith only [hP,hz.2])
    have he' : (min σ r)^(-δ) ≤ σ^(-δ)*r^(-δ):= (Real.rpow_le_rpow_of_nonpos (mul_pos hx hP) hh (neg_nonpos.mpr hd.le)).trans_eq (Real.mul_rpow hx.le hP.le)
    have hβ: (min σ r)^(-δ) ≤ (q)^(-δ)* σ^(-ε):=by
        apply he'.trans; rw [Rate_up r t hP ht]; calc
         _ ≤ (q)^(-δ) * (σ^(-δ)* σ^(-δ)):=by apply le_trans (b:= σ^(-δ)*((q)^(-δ) * σ^(-δ))) _ (le_of_eq (by ring)); exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hx h (by linarith only [hd])) (Real.rpow_nonneg (div_pos hP ht).le _)) (Real.rpow_nonneg hx.le _)
         _ ≤ _:= by rw [← Real.rpow_add hx]; exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hx hz.2 (by linarith only [hδ])) (Real.rpow_nonneg (div_pos hP ht).le _)
    change D*(A*C*V*(min σ r)^(-δ)) ≤ D*V*(q)^(-δ)*(A*C*σ^(-ε))
    rw [show D*(A*C*V*(min σ r)^(-δ))=D*V*A*C*(min σ r)^(-δ) by ring,show D*V*(q)^(-δ)*(A*C*σ^(-ε))=D*V*A*C*((q)^(-δ)*σ^(-ε)) by ring]; exact mul_le_mul_of_nonneg_left hβ (mul_nonneg (mul_nonneg (mul_nonneg (tempo_nonneg i p (div_pos hP ht).le) (Real.rpow_nonneg (div_pos hP ht).le _)) (he.pos _).le) (stars_pos d P _ (R.length_pos _)|>.le))
omit he hd
lemma lowering {u:ℝ}(hh: t ≤ z.radius): (Φ).delta z u=R.delta x u:=by
   change (u/min σ z.radius)^(1/4:ℝ)=_; rw [min_eq_left (le_trans (R.route.covered ..|>.1) hh)]; rfl
lemma lending_up {u:ℝ}(hu:0<u)(hr:z.radius≤t): (Φ).delta z u≤ R.delta x u * (q)^(-(1/4:ℝ)) :=by
    let a:=(1/4:ℝ); let r:=z.radius; have hp:0<r:= z.pos; have hx:= R.route.footing x; have hh:σ≤ t:= (R.route.covered ..|>.1); have h':0<t:=hx.trans_le hh; have h:σ*(q) ≤ min σ r:= le_min (mul_le_of_le_one_right hx.le ((div_le_one h').2 hr)) (by apply le_trans (mul_le_mul_of_nonneg_right hh (div_pos hp h').le); exact le_of_eq (by field_simp))
    change (u/min σ r)^a≤ (u/σ)^a*(q)^(-a)
    rw [Real.rpow_neg (div_pos hp h').le, ← div_eq_mul_inv, ← Real.div_rpow (div_pos hu hx).le (div_pos hp h').le, div_div]; exact Real.rpow_le_rpow (div_pos hu (lt_min hx hp)).le (div_le_div_of_nonneg_left hu.le (mul_pos hx (div_pos hp h')) h) (by unfold a; norm_num)
end
end YM.Frontier6.Bouquet.Atelier
