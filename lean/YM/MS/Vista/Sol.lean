import YM.MS.Orbit.L_Ready
/-!
# Slowly increasing frames (certain terminal intervals also), supports spinning. Trigger PMC.Clock.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Filter Function Finset Real MeasureTheory Metric
open Koszul Plane Landau Detect Book Convolve Momentum Tone Frame Latch Job Belt Wind City Fiddle Osc Osc.Snap
open Wire Rake Geo Heat Flux Orbit
open scoped Topology ContDiff Interval
variable {G:Gauge}{I A E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{ P: Belt I }{F H: Glade G I}{a:I→ℝ}
abbrev monoY (P:Belt I)(A:P.time→ℝ): Prop:= ∀ x y:P.time,x.1=y.1→tstart x≤ tstart y→ A x≤ A y
structure Accel (P:Belt I)(a:I→ℝ): Prop where
    begin (i:I): a i∈ P.slot i -- extra.Transfer
    min t:Set.Icc (a t.1) (tstart t)=P.stream t
    quote x:tstart x-a x.1≤P.price.basic x
    mon : monoY P P.price.basic
    step : monoY P P.price.length
namespace Accel
lemma time (h:Accel P a)(x:P.time): a x.1 ≤ tstart x:= by
    have hx : tstart x∈ P.stream x:= ⟨ x.2.property,Set.mem_Iic.mpr le_rfl ⟩; rw [ ← h.min x ] at hx; exact hx.1
-- pressure.full
omit [NormedSpace ℝ E] in
lemma bpay (h:Accel P a)(x y:P.time)(he:x.1=y.1)(hv:tstart x≤ tstart y)(p:E): P.price.full.cheap x p ≤ P.price.full.cheap y p:= by unfold Scale.full Scale.weight; dsimp only; refine mul_le_mul (h.mon x y he hv) ?_ (P.price.weight_pos x p|>.le) (P.price.basic_pos y|>.le); gcongr; exact h.step _ _ he hv
omit [NormedSpace ℝ E] in
lemma sub (P:Belt I) (p:E)(t:P.time): P.price.basic t≤ P.price.full.cheap t p:= le_mul_of_one_le_right ( P.price.basic_pos t|>.le ) ( P.price.one_le_weight t p )
end Accel
abbrev stride (F:Glade G I)(i:I)(j:ℕ)(w:Wire (BH G) E QP) (p:E)(t:ℝ):= iteratedFDeriv ℝ j (fieldVal (F i t) w) p
structure LookS (F:Glade G I)(H: Glade G I) : Prop where
    modal: Orbit.Modal F H
    act (i:I): TouchF (F i)
    der (i:I): TouchF (H i)
lemma rangeS (hx:LookS F H)(i:I)(j:ℕ)(w:Wire (BH G) E QP)(p:E)(t:ℝ): HasDerivAt (stride F i j w p) ( stride H i j w p t ) t:= by
    let V:ℝ×E→ℂ:= fun x=> fieldVal ( H i x.1 ) w x.2; have hC:ContDiff ℝ ∞ V:= jointWay (hx.der i) w; have he(t):F i t=(F i 0)+coast (H i) t:= congr_fun ( term_account (hx.act i) (hx.der i) (hx.modal.pace i) ) t; -- no implicit t? yes.
    have hv(t x): fieldVal (F i t) w x= fieldVal (F i 0) w x +desk V (t,x):= by nth_rw 1 [he]; rfl
    have hT : ContDiff ℝ j (fieldVal (F i 0) w):= (( hx.act i |>.routine w 0 ) : ContDiff ℝ ∞ (fieldVal (F i 0) w) ).of_le (by exact_mod_cast le_top);
    let T:= stride F i j w p 0; have hζ (s:ℝ): ContDiff ℝ ∞ (fun p:E=> desk V (s,p)):= (park hC).comp ( f:=fun p:E=>(s,p) ) (by fun_prop)
    have hX (s:ℝ): stride F i j w p s=T+iteratedFDeriv ℝ j (fun x:E=>desk V (s,x)) p:= by unfold stride; rw [show fieldVal (F i s) w= fieldVal (F i 0) w + fun x:E=> desk V (s,x) from funext (hv s),iteratedFDeriv_add hT (( hζ s ).of_le (by exact_mod_cast le_top)) ]; rfl
    rw [funext hX]; exact (deskD_iter hC j t p).const_add _
-- envelope station using direct growth, no exp Lens Slide.Friendly.
variable {w:Wire (BH G) E QP}{A: P.time→ℝ}
def LaunchF (P:Belt I)(a:I→ℝ)(F: Glade G I)(t:P.time): Law G:= F t.1 (a t.1)
lemma slowing (ht:LookS F H)(h:Accel P a)(hv: monoY P (Qbud w P.price A))(he:nn A)(hf:Cape P.price (plug H) A w): Cape P.price (fun i=>plug F i - LaunchF P a F i) A w:= by
    let V:= Qbud w P.price A; have hP : nn V:= pos_nn _ he P.price; let U(i:I)(t:ℝ):=fieldVal (F i t) w; have hs(i t): ContDiff ℝ ∞ ( U i t ) := ( ht.act i ).routine w t; change Bound _ _ V; have hEq(t:P.time) : Chart (fun i=> Job.plug F i- LaunchF P a F i) w t = U t.1 (tstart t)-U t.1 (a t.1):= rfl; rw [funext hEq]; -- often η.S.Count.
    refine ⟨fun i=> (hs _ _).sub (hs _ _), fun j=>?_⟩; obtain ⟨C,hC,k,hk⟩:= hf.quoted j; refine ⟨C,hC,k+1,fun t p hh=>?_ ⟩; let S:=P.price; let L:=stride F t.1 j w p; let X:=stride H t.1 j w p; let B:= S.full.cheap t p; let A:=a t.1; let z := tstart t; have hxθ (a:ℝ):= rangeS ht t.1 j w p a; have hS := S.pos t; have hU:=hP t; have h0:1≤B:= S.full.one_le t p hh
    let Y:=C*B^k*( V t*S.length t^j ); have hE:Y≥0:=by unfold Y; positivity
    dsimp only; rw [ iteratedFDeriv_sub ((hs _ _).of_le (by exact_mod_cast le_top)) ((hs _ _).of_le (by exact_mod_cast le_top)), Pi.sub_apply ]; change ‖L z - L A‖≤ C * B ^ (k+1)*(V t*S.length t^j ); apply le_trans ( norm_image_sub_le_of_norm_deriv_le_segment' (f:= L) (f':=X) (C:=Y) (fun x _=> ( hxθ x ).hasDerivWithinAt) ?X₀ z (Set.right_mem_Icc.mpr ( h.time _ )) ); swap;
    · intro x hx; have hu:x ∈ P.stream t:= (h.min t) ▸ Set.Ico_subset_Icc_self hx; let q:P.time:=⟨t.1,x,hu.1⟩; apply ( hk q p trivial ).trans; change C*(S.full.cheap q p)^k*( V q*S.length q^j)≤ Y; unfold Y; have ht:S.length q≤S.length t:= h.step _ _ rfl hx.2.le; have hh:= S.pos q; have hK:V q≤V t:= hv q t rfl hx.2.le; have hb:= hP q; gcongr; · exact ( S.full.cheap_pos (p:=p) (i:=q) trivial ).le
      exact h.bpay q t rfl hx.2.le p
    apply (mul_le_mul_of_nonneg_left (le_trans (h.quote t) ( Accel.sub P p t )) hE )|>.trans_eq; unfold Y B S; ring
variable {b c:Bool}
lemma slowC (hp: LookS F H)(h:Accel P a)(hv:monoY P (Qbud w P.price A))(he:nn A)(hf:Cape P.price (plug H) A w)( hx:Cape P.price (LaunchF P a F) A w ) : Cape P.price (plug F) A w:= by obtain hz := slowing hp h hv he hf; convert Cape.plus hz hx using 1; ext; simp -- Cape.Prop not defeq Cancel point.Linear
end YM.MS.Vista
