import YM.FVA2.O.Rough.Level
/-!
# Scalar limit pointwise for any `Response`, and zero for any exact response

See `closeQ`: still need control of the generator from `Response`, rather
than arbitrary choices in calling such an array exact. No OPE-separation
hypotheses required in this lemma.
-/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Rough
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land O.Hue
open scoped Topology ContDiff Interval
variable { E I α : Type } { G : Gauge } {a η:I→ℝ}{R: IntervalFamily I}{n j k:ℕ}{b:ℤ}
variable { x:α→ℝ } {B:Deck G} {K: Booked B} {M:MS_Data G K}{X:T ( Glade G I )}{Y:T ( Glade G I )}{θ:E→ I}
abbrev compose0 (θ:E→I)(X:T ( Glade G I )): T ( Glade G E ):= fun i j=> X i ( θ j )
lemma tail_bank (h:Banks X b): Banks (compose0 θ X) b:= by
    intro k; obtain ⟨n,H⟩:= (h k).heat; exact ⟨ ⟨ fun i=> (h k).cross.cost ( θ i ), fun i=> ( h k ).cross.walk ( θ i ) ⟩, ⟨ n,fun i=> H ( θ i ) ⟩, fun i=> (h k).tone (θ i)⟩
lemma nick : nav M (η ∘ θ) ( compose0 θ X )= compose0 θ ( nav M η X ):= by
    funext n i t; change peek ( nav _ _ _) i t n= peek ( nav _ _ _ ) _ t n; rw [steers,steers]; rfl
lemma wheel : helm M (η∘θ) ( compose0 θ X )=compose0 θ ( helm M η X ):= by
    funext n i t; change peek ( helm _ _ _) i t n= peek ( helm _ _ _ ) _ t n ; rw [leads,leads]; rfl
lemma dresser (h:Response X M η b) (θ:E→I): Response ( compose0 θ X ) M (η∘ θ) b:= ⟨ tail_bank h.life,by rw [wheel]; exact fun n i=> h.vital n ( θ i ) ⟩
lemma gauge_frame {F:Glade G I}(hp:taxi ( face R ) F ( peak R eps_gain a ) 0) (hx:Every R)(i:I): Tendsto ( bare F i ) atTop ( 𝓝 0 ):= by
    obtain ⟨C,hC,k,h⟩:= offers hp hx; apply tendsto_zero_iff_norm_tendsto_zero.mpr; refine squeeze_zero' (Eventually.of_forall fun _=> norm_nonneg _) ((eventually_ge_atTop (R.beg i)).mono ( h i )) ?_; simpa only [mul_zero] using (LogTime.vanishes p_gain k).const_mul ( C* R.logPart i^k*wake R eps_gain a i )
lemma ζnav (hp: liveP ( face R ) η)(hr: Response X M η b)(he:nn a)(hx:∀ m≤ n,totalT (initial R) ( X m ) a true): taxi ( face R ) ( nav M η X n ) ( peak R eps_gain a ) 0 := by
    obtain h:= upper hp hr he (n:=n+1) (fun i hi=> hx i (by omega)); apply Well.stays ( nav_bill hp (hr.life n|>.cross) (Well.cram (h n (by omega)) (fun _=> by omega)) (fun i hi=> h i (by omega)) (pays_p he) ); intro p; apply mul_le_of_le_one_left (pays_p he p); exact inv_le_one_of_one_le₀ ( Real.one_le_exp ( (R.beg_nn _).trans p.ge ) ) -- name unknown
lemma live_v (h: allowance R η): liveP (face R) η:= allotted h
abbrev frame (y:ℝ):= Station ( Tide.frameF Unit y )
lemma price0 {U:Glade G I}(p:I)(h: Warm U false)(c:Bool): totalT ( initial ( frame ( η p ))) (fun (_:Unit) t=> U p t) 1 c:= by
    intro E _ _ w hv; let P':=frame (η p); let S:= P'.dawn; obtain hp:= h.cost p 1 zero_le_one; have hr(i:Unit): S.length i =1:= Real.exp_zero; obtain he:= constant_at hp (⟨ (), 0, show (0:ℝ)∈ Set.Icc (-1) 1 from by norm_num ⟩:camp 1) S ( fun i=>(hr i).ge ) w (fun i=>Bool.noConfusion i) (fun i=>Bool.noConfusion i); refine Cost.Le.trans he.norm_cost (Cost.of_le fun i x hx=>?_ ); change 1≤ S.length i^pitch w*1; rw [hr,one_zpow,mul_one]
lemma allowances (p:I)(η:I→ℝ): allowance ( frame (η p) ) (fun _=>η p):= liveS.allow
lemma total_peak (h:Response X M η b)(p:I)(n:ℕ): Allow (X n) p := by
    let θ(_i:Unit):= p; let V:=frame ( η p ); let Y:= compose0 θ X; have hp := dresser h θ; obtain he:= helm_up (M:=M) (live_v (allowances p η)) hp ( fun i=> zero_le_one ) (n:=n+1) ( a:=1 ) (fun m hm=> price0 p ( h.life m|>.cross) true) n (by omega); exact ( low_count (Well.cram he (fun i=> Bool.noConfusion i)) ( hp.vital n ) (fun _=> zero_le_one) (fun i=>rfl) ).1 ()
lemma closeQ (h:Response X M η b)(p:I)(n:ℕ): blade ( nav M η X n ) p=0:= by
    let θ(_i:Unit):= p; let V:=frame ( η p ); let Y:= compose0 θ X; have hp := dresser h θ; refine Tendsto.limUnder_eq (f:=atTop) (g:= bare ( nav M η X n ) p) ?_; obtain he:= gauge_frame (F:=nav M (η∘ θ) Y n) (ζnav ( a:=1 ) ( live_v (allowances p η )) hp (fun _=>zero_le_one) (fun m hm=> price0 p (h.life m|>.cross) true)) (fun i=> rfl) (); unfold Y at he; rw [nick] at he; exact he
end YM.FVA2.O.Rough
