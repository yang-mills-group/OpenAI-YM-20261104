import YM.FormalBulk08.Broc.Heron

/-!
If the previous orders match, the linearized Ward encounters each rank
separately. Here at every period to price the all-leg theorem (including rank two),
all through precisely the Charter orders given.
-/
noncomputable section
set_option autoImplicit false
namespace YM.FormalBulk08.Broc
open Function Filter Lattice RG Laurent Bloch Exterior
open Reef Lava Gorge Mesa Shore Lotus Orb Wick Series Jets PowerSeries North
open Stationary hiding shine Rays
open scoped Topology ENNReal Matrix BigOperators Classical ContDiff
variable {I J:Type}{G:Gauge}{n:Side}{s:Signed}{t e r E:ℕ}{A σ:ℝ}

section
variable [Fintype I]
def blur (T:Tile I r) (x:Jets.Rays I):= traceP x (facade r T)
def airs (v:chain I r):= ∏ j:Fin r, (fun x:Jets.Rays I=>x (v j))
lemma blueprint (T:Tile I r): blur T=∑ v:chain I r,(fun _=>T v)*airs v:= by
    funext x; simp [blur,traceP,facade_eq,airs,Lava.cards,Finset.sum_apply,Finset.prod_apply]
lemma airs_shine (v:chain I r): ContDiffAt ℝ ω (airs v) 0:= by
    unfold airs; rw [show (∏ j:Fin r, (fun x:Jets.Rays I=>x (v j)))= fun x:Jets.Rays I=>∏ j,x (v j) from funext fun x=> by simp [Finset.prod_apply]]; fun_prop
lemma blueprint_diff (T:Tile I r): ContDiffAt ℝ ω (blur T) 0:= by
    rw [blueprint]; rw [show (∑ v:chain I r,_)=fun x=>∑ v:chain I r,T v*airs v x from ?_]; apply ContDiffAt.sum (fun i _=> contDiffAt_const.mul (airs_shine i))
    funext; simp [Finset.sum_apply]
lemma blueprint_price (T:Tile I r): paste (blur T)= X^r*C (facade r T):= by
    have he (v:chain I r) : paste (airs v)= X^r*C (cards v):= by
        unfold airs; rw [shaving _ _ (fun i _=> contDiffAt_apply ..)]; simp_rw [paste_index,Finset.prod_mul_distrib,cards,map_prod, Finset.prod_const, Finset.card_univ,Fintype.card_fin]
    rw [blueprint, garter (fun v=>(fun _=>T v)*airs v) _ (fun i _=> contDiffAt_const.mul ((airs_shine i).of_le le_top)),facade_eq, map_sum,Finset.mul_sum];apply Finset.sum_congr rfl; intro v _
    rw [paste_mul _ _ (contDiffAt_const (c:=T v)) ((airs_shine v).of_le le_top),paste_flat,map_mul,he]; ring
lemma blur_inj (T S:Tile I r)(h:Agate T)(hp: Agate S)(he: blur T=blur S): T=S:= facade_unique h hp (orbit_ext fun x=>congr_fun he x)
variable [Fintype J]
def dew (f:Jets.Rays J→Jets.Rays I)(p:TypeR I):= coeff 0 (roam ℝ (motor f) (C p))
lemma blur_pull (T:Tile I r)(f:Jets.Rays J→Jets.Rays I)(h:f 0=0)(H:ContDiffAt ℝ ∞ f 0): coeff r (paste (blur T ∘ f))=dew f (facade r T):= by
    rw [paste_steps _ f ((blueprint_diff T).of_le le_top) H h, blueprint_price,map_mul, map_pow]; rw [show roam ℝ _ X=X from change_X _]; rw [coeff_X_pow_mul']; simp [dew] -- should match
lemma blur_polar (T:Tile I r)(f:Jets.Rays J→Jets.Rays I)(h:f 0=0)(H:ContDiffAt ℝ ∞ f 0): (dew f (facade r T)).IsHomogeneous r := by rw [←blur_pull T f h H]; exact paste_grade ..
lemma blur_low (T:Tile I r)(f: Jets.Rays J→Jets.Rays I)(h:f 0=0)(H:ContDiffAt ℝ ∞ f 0) (i:ℕ)(hi:i<r): coeff i (paste (blur T ∘ f))=0:= by
    rw [paste_steps _ f ((blueprint_diff T).of_le le_top) H h, blueprint_price,map_mul, map_pow,show roam _ _ X=X from change_X _,coeff_X_pow_mul']; simp [not_le.mpr hi]
omit [Fintype I] [Fintype J] in lemma dew_scion (z:I→Pap J)(T:Pap I)(h:∀ i,i<e→coeff i T=0): coeff e (roam ℝ z T)=coeff 0 (roam ℝ z (C (coeff e T))):= by
   -- divide by X^e
   nth_rw 1 [← after_rope T e h]; rw [map_mul,map_pow,show roam ℝ z X=X from change_X _,coeff_X_pow_mul']; simp only [le_refl,↓reduceIte, tsub_self]; rw [roam_first _ _,roam_first _ _,coeff_zero_C,after_one,add_zero]
end

-- rank projection irrespective of Valence, when in sow list
lemma dew_rank (T:Pot G)(n:Side)(f:Link G n→Link G n)(h:f 0=0)(H:ContDiffAt ℝ ∞ f 0)(hx:t<e+2): MvPolynomial.homogeneousComponent (t+1) (dew f (coeff e (stone T n)))= dew f (facade _ (cum 0 n (T e (t+1)))):= by
   rw [sow_coeff,sow];simp_rw [dew,map_sum]; change (∑ i∈Finset.range (e+2), MvPolynomial.homogeneousComponent _ (dew f (facade _ (cum 0 n (T e (i+1))))))= _; simp_rw [MvPolynomial.homogeneousComponent_of_mem (blur_polar _ f h H)]; simp [hx,dew]

def stripeK (T:Pot G)(n:Side)(e t):= blur (cum 0 n (T e (t+1)))
lemma choir (T:Pot G)(v:Site n)(h:Charter (stone T n) E)(he:e≤E)(hh:t<e+2)(hw:∀ i < e,coeff i (stone T n)=0)(p q:Link G n→Link G n)(a: Link G n→Site n→ G.El)(hp: p 0=0)(hq:q 0=0)(hz:∃ g:G.El,a 0=fun _=>g)(ha: Army a 0)(P:ContDiffAt ℝ ω p 0)(Q:ContDiffAt ℝ ω q 0)(ht:∀ᶠ x in 𝓝 0,input G n (q x)=Lattice.gauge (a x) (pull s v (input G n (p x)))):
    coeff (t+1) (paste (stripeK T n e t ∘ p)) = coeff (t+1) (paste (stripeK T n e t ∘ q)) := by
    have hd:= h s v (Lines G n 1) p q a hp hq P Q ha hz ht e he; rw [dew_scion _ _ hw,dew_scion (motor q) _ hw] at hd; rw [stripeK, blur_pull _ p hp (P.of_le le_top),blur_pull _ q hq (Q.of_le le_top)]; exact ((dew_rank T n p hp (P.of_le le_top) hh).symm.trans (congr_arg _ hd)).trans (dew_rank T n q hq (Q.of_le le_top) hh)
lemma linear_blur (T:Tile (Lines G n 1) r)(f:Link G n→L[ℝ]Link G n) : blur T ∘ f = fun x=> traceP x (coeff r (paste (blur T∘ f))):= by
   funext x; rw [trace_paste]; let g:=blur T
   have he := wired f (f:=g) (x:=0) (by rw [map_zero]; exact (blueprint_diff T).analyticAt) r (fun _=>x); rw [map_zero] at he
   have hh:=trace_paste (f x) g r; unfold PertExtension.Series.Radial.jet; rw [he]; change _=PertExtension.Series.Radial.jet g r (f x); rw [←hh,show coeff r (paste g)=facade r T by rw [show paste g=_ from blueprint_price T,coeff_X_pow_mul']; simp]; rfl
-- maybe goals
end YM.FormalBulk08.Broc
