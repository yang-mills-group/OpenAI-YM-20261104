import YM.RGComparison.Core16.Silk.Voile
/-!
# Conditional germ at g by curvature realization. Physical product valuation identification
trick for visibility margins: Taylor Price earns formal comparison to **any** fixed order then
synthesize its Aspiration certificate. Thus remains local Wick prescription from Ingredient (and
matrix prices real-side from estimator), not diagnostic of true path at same report couplings.
Station θ retained at all t (g param); no `ExpWeights` license in this lemma to use other blocked history.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RGComparison.Core16.Silk
open Function Filter Lattice RG Tree Wilson MeasureTheory Metric Lumen Lumen.Planet Forge
open PertExtension PertExtension.Series Tested Radial
open Precision Finset
open scoped Topology ContDiff PowerSeries Classical BigOperators InnerProductSpace
variable (r w t:ℕ) (x:ℝ) (U:ℕ→Cost) (V:ℕ→Roll)

-- reusable maturity ~ emissivity starts at w (positive conditioning loss paid below), not related to design F orientation.
def shiftFront (r:ℕ)(x:Roll):=PowerSeries.X^r*x

def dawn (V:ℕ→Roll) (w t:ℕ) := ∑ i∈range (t+1), shiftFront (w+i) (V i)
def day (V:ℕ→Roll) (w:ℕ) := PowerSeries.mk (fun n=>nth n (dawn V w n))
def dawnValue (U:ℕ→Cost)(w t:ℕ) : Cost:=∑ i∈range (t+1),(fun x:ℝ=>x^(w+i))* U i

def day_ticket (u:Cost)(w n:ℕ) := Bill (w+n+1) u
lemma shifts (H:train (U t) (V t)): train (fun x=>x^r*U t x) (shiftFront r (V t)):=by
     apply (show train (fun x=>x^r) ((PowerSeries.X : Roll)^r) from ?_).produces H
     convert! train.mono r 1 using 1
     · ext; simp only [mul_one]
     ext n; rw [PowerSeries.coeff_X_pow,PowerSeries.coeff_monomial]
lemma player (h:∀ i,train (U i) (V i)) : train (dawnValue U w t) (dawn V w t):= train.join _ _ _ (fun i _=>shifts (w+i) i _ _ (h i))

variable {U V r w t}
lemma advisor {t' j:ℕ}(h:t≤ t')(h': j≤w+t) : nth j (dawn V w t)=nth j (dawn V w t'):= by
     unfold nth dawn; rw [map_sum,map_sum]; exact sum_subset (range_mono (by omega)) (fun i _ he=> by
         have hv : ¬ i<t+1:= mt mem_range.mpr he; rw [shiftFront,PowerSeries.coeff_X_pow_mul',if_neg (show ¬w+i ≤ j from by omega)])
lemma vogue {j :ℕ}(H:j≤w+t): nth j (day V w)=nth j (dawn V w t):=by
     rw [nth, day,PowerSeries.coeff_mk]; exact (le_total t j).elim (fun ht=> (advisor ht H).symm) (fun ht=>advisor ht (Nat.le_add_left ..))
lemma receipt {f : Cost}(hu:∀ i,train (U i) (V i))(h: ∀ r,day_ticket (f-dawnValue U w r) w r) : train f (day V w) := by
    intro n
    have he: peval (term (day V w)) n=peval (term (dawn V w n)) n:= funext fun t=> Finset.sum_congr rfl (fun i hi=> congr_arg (fun u : ℝ=>t^i • u) (vogue (show i≤w+n by simp only [mem_range] at hi; omega)))
    rw [he, show f-peval _ _ =(f-dawnValue U w n)+(dawnValue U w n-peval (term (dawn V w n)) n) from (sub_add_sub_cancel ..).symm]; exact bill_add (bill_ge (h n) (by omega)) (player w n U V hu n)
variable {G:Gauge}{S:Side}{ι k T A D L : Type}[Fintype ι][Fintype k][Fintype T][Fintype A][Fintype D][Fintype L]
variable {X:Shelf G A D} {P:Planet X S ι k T} {p:Stuff G ι L} {ψ:(L→G.Color)→ℝ}
variable (w:Rail G ι){f:Melody G ι}(H:P.Steady) {N a:ℕ} {b:ℝ} (he:Visible X ψ f p N b) (hψ:ContDiffAt ℝ ∞ ψ 0)
include H he
omit [Fintype A] in
lemma stamped (t:ℕ) (g:ℝ)(hg:amen X g) : sight P w (Error t f ψ p) g = sight P w f g - ∑ i∈range t, g^i * sight P w (tale p ψ i) g:= Error.tribute H he hg t w
include hψ
omit [Fintype A] in
private lemma sheen (r:ℕ):Bill r (sight P w (Error (r+1) f ψ p)):=by
   have hb:0≤b:= (abs_nonneg _).trans (he.price 0 ⟨le_rfl,H.prices.thick.2.1.le⟩ 1)
   obtain ⟨C,hC,h0⟩:=Error.motion H.prices ψ hψ (r+1) w.length N b hb
   refine ⟨C,hC,Fk.tollLess ?_⟩; let k:=4*(r+1+w.length); filter_upwards [h0,(Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).eventually (gt_mem_nhds zero_lt_one)] with x h hx; let g:=dollar x; have hp:0<g:= dollar_pos _
   change |sight P w _ g| ≤ _; refine (h S _ _ _ _ _ _ P H f p he w le_rfl).trans ?_
   change x^k*g^(r+1)*C ≤ C * g^r; rw [pow_succ,show x^k*(g^r*g)*C=x^k*g*(C*g^r) from by ring]; exact mul_le_of_le_one_left (by positivity) (show x^k*g<1 from hx).le
lemma dim (r:ℕ): Bill r (sight P w (Error r f ψ p)):=by
   let U:=sight P w (tale p ψ r); have hu:= Aspiration.bounded (solder P p ψ H w r)
   let v x:= (x^r:ℝ)*U x; have hv:Bill r v:= by convert! bill_mul (bill_mon (1:ℝ) r le_rfl) hu using 1; simp; rfl
   apply rail_bill (bill_add (sheen w H he hψ r) hv); filter_upwards [Fk.tollLess (willing H.prices)] with x hx; rw [Pi.add_apply, stamped w H he r x hx, stamped w H he (r+1) x hx,sum_range_succ]; unfold v U; abel

lemma prelude : train (sight P w f) (day (night p ψ (price P) w) 0) := by
    let U i:=sight P w (tale p ψ i)
    refine receipt (U:=U) (solder P _ _ H w) ?_
    intro i; unfold day_ticket; rw [Nat.zero_add]; refine rail_bill (dim w H he hψ (i+1)) ?_
    filter_upwards [Fk.tollLess (willing H.prices)] with x hx; rw [stamped w H he (i+1) x hx]; simp only [dawnValue, Pi.sub_apply,Finset.sum_apply,Pi.mul_apply,Nat.zero_add]; rfl
-- Strict positive coupling error. Choose n first from caller. Spell explicit taylor-index shift, no assuming vanish of preceding slots.
def hiccup (P:Planet X S ι k T)(w:Rail G ι)(p:Stuff G ι L)(ψ:(L→ G.Color)→ℝ)(f:Melody G ι) (g:ℝ):= (sight P w (Error 2 f ψ p) g)/g

lemma stumble : train (hiccup P w p ψ f) (day (fun i=> night p ψ (price P) w (2+i)) 1):=by
    let U i:= sight P w (tale p ψ (2+i)); refine receipt (U:=U) (fun i=>solder P _ _ H w (2+i)) ?_
    intro r; have h:=dim w H he hψ (2+(r+1)); obtain ⟨c,hc,h⟩:=h; let u:=hiccup P w p ψ f; let F:=dawnValue U 1 r; refine ⟨c,hc,?_⟩
    filter_upwards [h,Fk.tollLess (willing H.prices), Tested.eventually_pos] with x h ht hp
    have hx : (u x-F x)*x= sight P w (Error (2+(r+1)) f ψ p) x:= by
       unfold u hiccup; rw [sub_mul,div_mul_cancel₀ _ hp.ne', stamped w H he 2 x ht, stamped w H he _ _ ht,sum_range_add _ 2 (r+1),sub_add_eq_sub_sub]; unfold F dawnValue; rw [Finset.sum_apply,sum_mul]; congr 1; refine sum_congr rfl (fun i hi=>?_); change x^(1+i)* U i x * x = x^(2+i) * U i x; rw [show 2+i=1+i+1 by omega,pow_succ]; ring
    rw [← hx, norm_mul,Real.norm_of_nonneg hp.le] at h
    change ‖u x-F x‖≤_; apply le_of_mul_le_mul_right _ hp; refine h.trans_eq ?_; rw [show 2+(r+1)=(1+r+1)+1 by omega,pow_succ]; ring
end YM.RGComparison.Core16.Silk
