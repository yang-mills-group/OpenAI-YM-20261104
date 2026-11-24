import YM.SchemeConversionRG11.FirstW.Fold.Vase
/-! Super-power image transfer done at selected cutoff. -/
noncomputable section
set_option autoImplicit false
namespace YM.RG11.FirstW.Deck
open Function MeasureTheory Filter Set Metric Lattice Pert Align Position Maxwell RawLabels MvPolynomial Warp SchemeConversionRG11
open scoped BigOperators Classical Topology Matrix
variable {G:Gauge}{F:Labels.Frames G}{T:Itinerary}{r:ℕ} {Q:Wash}{R:ℝ}
structure Diorama (T:Itinerary)(o:∀ i,Full.Grid (T.period i) r)(v:Points r): Prop where
 ht : v∈conf r
 hs : ∀ j, Home T (fun i=>o i j) (v j)
 hdiv : ∀ i,4 ∣ (T.period i).val
variable {o:∀ i,Full.Grid (T.period i) r} {v:Points r} (d:Diorama T o v)
include d
lemma orientedD (x y:At G r 6)(he:x.1 ≠ y.1): Fleck T (fun i=>dues (o i) (T.gap i) x y - radar (o i) (T.gap i) x y) := by
 let f(i) :=o i x.1; let g(i):=o i y.1
 have h:= river_tip y.2.val g f (remote_from d.hdiv f g (d.hs _) (d.hs _)); have H:= letter_glide h x.2.val
 have eq (i:ℕ): dues (o i) (T.gap i) x y= tape x.2.val (T.gap i) (f i) (river (T.gap i) y.2.val (g i)+reflectT G (T.period i) (river (T.gap i) y.2.val (g i))) := by
   unfold dues; have hh : dues (o i) (T.gap i) x y= dues (o i) (T.gap i) y x:= by
     apply Complex.ofReal_injective; rw [←silver,←silver]; unfold coins; exact integral_congr_ae (Eventually.of_forall fun z=> mul_comm ..)
   unfold dues at hh; rw [hh,corrected,if_neg (Ne.symm he),sub_zero, aura_eq]
 simp_rw [eq,map_add]; unfold f g at *; simp only [radar,arise,add_sub_cancel_left]; simp_rw [tape_scales x.2.val (T.gap _) (o _ _),LinearMap.smul_apply]; exact H.sale _
lemma compass (x y:At G r 6): Dear T (fun i=> (↑(dues (o i) (T.gap i) x y):ℂ)):= Dear.given (Complex.continuous_ofReal.continuousAt.tendsto.comp (corrected_limit T o v d.ht d.hs d.hdiv x.1 y.1 x.2.val y.2.val))
lemma compassD (x y:At G r 6)(he:x.1≠y.1): Dear T (fun i=> (↑(radar (o i) (T.gap i) x y):ℂ)):= by
 let V i:= (↑(dues (o i) (T.gap i) x y):ℂ); let P i:=(↑(radar (o i) (T.gap i) x y):ℂ)
 have ht: Fleck T (fun i=> V i-P i) := by simp_rw [V,P,← Complex.ofReal_sub]; exact (orientedD d x y he).push Complex.ofRealCLM
 have hp : Dear T (fun i=> V i + -(V i-P i)) := Dear.roll (compass d _ _) (Dear.lump ht.minus)
 simp only [← sub_eq_add_neg,sub_sub_cancel] at hp; exact hp
lemma pass_part (Z:ℕ→Pack F)(hz:Level (fun i=> T.gap i • Z i))(p:Players G r 6)(k:E F 6)(s:Fin r): let B(v:ℕ):=cloak F ((twistC (T.gap v) (Z v)).val k)
    Fleck T (fun i=> echoSelf p (o i) (T.gap i) s (B i)) ∧
    Fleck T (fun i=>echoesP p (o i) (T.gap i) s (B i) (dues (o i) (T.gap i))-echoesP p (o i) (T.gap i) s (B i) (radar (o i) (T.gap i))) := by
 intro B; let q x (i j:At G r 6):ℂ:= ↑(dues (o x) (T.gap x) i j); let F x (i j:At G r 6):ℂ:= ↑(radar (o x) (T.gap x) i j)
 let L:= ContinuousLinearMap.mul ℝ ℂ
 have hx(i j:Who G 6): Dear T (fun t=> (1/2:ℂ)*loot (B t) i j):= Dear.pair (Dear.given (tendsto_const_nhds)) (dear_chips k Z hz i j) L
 constructor
 · unfold echoSelf; refine Fleck.with (B:=L) ?_ (zeroth_thin d.hdiv o (air p s) v d.ht d.hs); apply Fleck.collect; intro a _; apply Fleck.collect; intro b _
   have he : Fleck T (fun t=> q t (s,a) (s,b)) := (self_fleck a.val b.val o v d.ht d.hs d.hdiv s).push Complex.ofRealCLM
   exact he.with (hx a b) L.flip
 unfold echoesP; simp_rw [←Finset.sum_sub_distrib]
 refine Fleck.collect (fun i hi=> Fleck.collect fun j hj=>?_); simp_rw [← sub_mul]; refine Fleck.with (B:=L) ?_ (zeroth_thin d.hdiv _ (dict j (dict i (air p s))) v d.ht d.hs)
 simp_rw [← Finset.sum_sub_distrib]; apply Fleck.collect; intro a _; apply Fleck.collect; intro b _; simp only [←mul_sub,Complex.ofReal_mul]; refine Fleck.with (B:=L.flip) ?_ (hx a b)
 have hd(i j:At G _ 6)(h:i.1≠j.1): Fleck T (fun t=> q t i j-F t i j):=by simp_rw [q,F,←Complex.ofReal_sub]; exact (orientedD d i j h).push Complex.ofRealCLM
 have h1:s≠i.1:= (Finset.mem_filter.mp hi).2.symm; have h2:s≠j.1:= (Finset.mem_filter.mp hj).2.symm
 have e(t:ℕ): q t (s,a) i*q t (s,b) j-F t (s,a) i*F t (s,b) j = (q t (s,a) i-F t (s,a) i)*q t (s,b) j+ (F t (s,a) i)*(q t (s,b) j-F t (s,b) j) := by ring
 change Fleck T (fun t => q t _ i*q t _ j-F t _ i *F t _ j); simp_rw [e]; exact Fleck.roll ((hd _ i h1).with (compass d (s,b) j) L) ((hd _ j h2).with (compassD d (s,a) i h1) L.flip)
lemma looked (s j:Fin r) : sails T (fun i=>o i j-o i s) (v j-v s) := by
 let S (i:Fin r): StepPath T:= fun t=> o t i-Full.center _
 have h(i:Fin r): sails T (S i) (v i):=d.hs i
 rw [show (fun i=>o i j-o i s)=S j-S s from _root_.funext (fun i=>by simp [S])]; exact sails_sub (h j) (h s)
lemma prints (s:Fin r)(x:At G r 6)(hQ: Q.rOut < R)(ht:8*R < ‖v x.1-v s‖) : Coal T Q R (fun i=> radX s (o i) (T.gap i) 6 x) := by
 have he {n:Side}(a:Labels.Key G)(x y:Site n)(q:ℝ): terms x (river q a y)=terms 0 (river q a (y-x)) := by
   have H (A:FullT G n): terms 0 (tracing x A) = terms x A:= _root_.funext (fun t=>by simp only [terms,tracing,LinearMap.pi_apply,LinearMap.proj_apply,add_zero]);
   rw [river,river,← consumes, map_smul,map_smul,H]
 let u := fun i=> terms (0:Site (T.period i)) (river (T.gap i) x.2.val (o i x.1-o i s)); rw [show (fun i=>radX s (o i) (T.gap i) 6 x) = u from _root_.funext fun i=> by unfold u radX arise; exact he ..]; exact cab _ _ (looked d s x.1) hQ ht
end YM.RG11.FirstW.Deck
