import YM.MS.SpaceOut.Venue
/-!
# Actual price.Bulkρ high and clamped-at-zero bounds.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.SpaceOut
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Vista
open scoped Topology ContDiff Interval
variable {G:Gauge}{W I:Type}{L:I→Side}{M:Visa I}{P:Belt I}{S:Scale I}{ K:I→Latch.Edge G}{u v s:I→ℝ}{D:I→Set QP}
lemma S0h (h:∃ C:ℝ,∀ i,‖s i‖≤C): Benefit S D (fun i (_:QP)=>(s i:ℂ)) := by obtain ⟨C,h⟩:= h; refine Costs.scalar ⟨max C 1, lt_max_of_lt_right zero_lt_one,0,fun i p hp=>?_ ⟩; rw [ pow_zero,mul_one,mul_one ]; exact le_max_of_le_left (by simpa using h i : ‖(( s i :ℝ):ℂ)‖ ≤ C)
abbrev Frost (S: Scale I)(K:I→Latch.Edge G)(h:I→ℝ): Prop:=∀ i j:BH G, Line S located (fun x=>K x i j) fun x=> S.length x ^ ( (4:ℤ) - wfield i-wfield j ) * h x
lemma d_frost (hx:Frost S K u)(hp:∀ i,1≤ S.length i): Frost S (fun i=> dope (K i)) u := by
   intro i j; let F t:= flag i t*flag j (-t); let B:= S.strict (located ( I:=I)); apply Deposit ( g:=fun _ x=>F x ) (hx i j); have hF:ContDiff ℝ ∞ F:= (flag_sm id contDiff_id i).mul ( flag_sm _ contDiff_id.neg j ); exact sun_b hp _ ( isCompact_closedBall _ _ ) hF -- `dope` unification.
lemma image_frost (hx:Frost S K u)(hp:∀ i,1≤ S.length i): Frost S (fun i=> valueI ( K i )) u := by
    intro i j; refine Eq.mp ?_ (Deposit ( g:=fun t p=> switch (j,-p) ) ( hx i j ) ?_ ); · congr! 1; ext; unfold valueI; rw [mul_comm]
    exact sun_b hp _ (isCompact_closedBall ..) ( (switch_sm j).comp ( show ContDiff ℝ ∞ (fun p:QP=> -p) from contDiff_id.neg) )
-- from midpoint unit.Any.L.Size
abbrev Origin (G: Gauge)(r:ℝ): Latch.Edge G:= (( (1+r:ℝ):ℂ) ) • Cpu G r
lemma DawnG (i j:BH G) (hp:∀ i, S.length i=u i) (hx:∀ i,1 ≤ u i): Line S located ( fun x=> Origin G (u x) i j ) (fun x=>S.length x ^ ( (4:ℤ)-wfield i-wfield j )):= by
   have hL z:1 ≤ S.length z:= hp z |>.symm ▸ hx z; let a(i):= Real.log (u i); have he(i:I):0<u i:= lt_of_lt_of_le zero_lt_one (hx i); have hl i: exp (a i)=u i:= Real.exp_log (he i); obtain h:= visited hL (fun i=> (hl i).trans ( hp i |>.symm )) ( z:=phaseDiff S ) (fun i=>le_rfl) i j |>.lattice; let q(i):=1+(u i)⁻¹; have hq:∃ C:ℝ,∀ i, ‖q i‖ ≤ C:=by refine ⟨2,fun i=>?_⟩; have ht:= inv_le_one_of_one_le₀ ( hx i ); have hp:0<(u i)⁻¹:= inv_pos.mpr ( he i ); unfold q; rw [Real.norm_of_nonneg (by linarith)]; linarith
   convert Deposit h ( S0h hq ) using 1; funext p x; simp only [ q,Origin, scaleL, Pi.smul_apply, hl,smul_eq_mul ]; push_cast; rw [← mul_assoc]; obtain h:=he p; congr 1; field_simp [(show ((u p:ℝ):ℂ)≠0 by exact_mod_cast h.ne')]; ring
lemma SmallC (i j:BH G)(hp:∀ i,‖u i‖≤1)(hu:∀ i,S.length i=1): Line S located (fun x=>Origin G (u x) i j) (fun x=> S.length x ^ ((4:ℤ)-wfield i-wfield j)):= by
    let F r:= Origin G r i j; let D:= firstZone Axis; have hf:ContDiff ℝ ∞ (Function.uncurry F):= ContDiff.smul (Complex.ofRealCLM.contDiff.comp (contDiff_const.add contDiff_fst)) ( main_f G i j ); intro b; refine ⟨ fun u=> (hf.comp ( f:=fun x=>((_:ℝ),x) ) (contDiff_const.prodMk contDiff_id)), fun k=>?_ ⟩; obtain ⟨C,hC,hK⟩:= Villa.compact hf 1 k ( show IsCompact D from isCompact_closedBall .. ); refine ⟨C*(1+π)^b,by positivity,0, fun i p h=>(hK (u i) (hp i) p h).trans ?_ ⟩; simp only [pow_zero,one_pow,mul_one,Scale.weight,hu,one_zpow, one_mul]; rw [ mul_assoc C ]; apply le_mul_of_one_le_right hC.le; have hv : 1+‖p‖≤1+π:= add_le_add_right (norm_zone p |>.mp h) 1; rw [one_div, ← div_eq_mul_inv, one_le_div ]; gcongr; positivity
lemma originΦ (hp:∀ i, S.length i=max 1 ( u i ))(hP:nn u): Frost S (fun i=> Origin G (u i)) 1:= by
    intro i j; simp_rw [Pi.one_apply,mul_one]; let V(i):= 1≤u i; refine SplitLine (v:=V) _ _ S _ ( DawnG i j (u:=fun i:Subtype V=> u i.1) (fun i=> ?_) (fun i=> i.2) ) ( SmallC i j (u:=fun i: Subtype (fun x=> ¬ V x)=> u i.1) (fun i=> by rw [Real.norm_of_nonneg (hP i.1)]; exact le_of_not_ge i.2 ) ?_ ); -- defeq leftS
    · change S.length i.val=_; rw [ hp,max_eq_right ( i.2 ) ]
    intro i; change S.length i.val= _; rw [ hp,max_eq_left ( le_of_not_ge i.2 ) ]
lemma forkη {b:Bool}(hx:∀ i,1≤S.length i)(hp:Frost S K u)(ht:PerK K): Fund S (fun i=> ηbone b ( K i )) u:= by
   cases b; · exact Mentor hx ht hp
   exact Mentor hx (fun i=> picture (ht i)) ( image_frost hp hx )
-- linking actual clock
lemma origin_ge (S:Belt I)(h:∀ i:S.time,0≤ tstart i)(hp:∀ i,S.price.length i= Vista.lamp ( tstart i )): Piece S (uniform G I) 1:= by
    let x (i:S.time):=τ (tstart i); let Q (i:S.time):= dope ( Origin G (x i))
    have hT(i:I)(t:ℝ): zoom ( Orbit.uniform G I ) i t= dope (Origin G ( Vista.τ t )):= by funext a b p; simp only [Vista.τ, Origin, zoom, Orbit.uniform, LaceL, dope,show 1+(exp t-1) = exp t from (by abel),Pi.smul_apply]; simp only [smul_eq_mul]; ring -- syntax `one_add_sub_cancel`
    have hS i:1 ≤ S.price.length i:= hp i |>.symm ▸ lamp_l _; have hv:nn x:= fun i=> sub_nonneg.mpr ( Real.one_le_exp (h i)); obtain hK:Frost S.price Q 1:= d_frost ( originΦ hp hv ) hS; intro b; unfold Prune PaintP; simp_rw [ hT ]; apply forkη hS hK; intro i; dsimp only [Q,Origin]; apply Orbit.speak_d; intro v u z p; simp_rw [Pi.smul_apply, smul_eq_mul,L_stamp ( x i ) v u z p ]; ring
end YM.MS.SpaceOut
