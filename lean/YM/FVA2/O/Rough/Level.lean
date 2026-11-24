import YM.FVA2.O.Rough.Frontier
/-!
# Positive ranks sustained & scalar limit estimate from initial matching fees
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Rough
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve O.Pad Vane High Detect
open MS.Local.Physical MS.Land
open scoped Topology ContDiff Interval
variable { E I α : Type } { G : Gauge } {a η:I→ℝ}{R:IntervalFamily I}{n j k:ℕ}{b:ℤ}
variable {x:α→ℝ} {S:Home α I}
variable {B:Deck G} { K:Booked B } { M:MS_Data G K } {X:T ( Glade G I )}{F H:Glade G I}
lemma upper (hp: liveP (face R) η)(he:Response X M η b)(hv:nn a)(ht:∀ m<n,totalT (initial R) ( X m ) a true) : ∀ m<n,totalT (face R) ( X m ) (peak R eps_gain a) true:= by
    intro m; induction m using Nat.strong_induction_on with | h m ih=>
       intro hm; let U:= X m; let Y:= helm M η X m; have hU:= he.life m|>.cross; obtain ⟨k,h⟩:= ( he.life m ).heat; apply form_of; suffices H :∀ k':ℕ,∀ t:ℕ,k≤k'+t→taxi ( face R ) U ( peak R eps_gain a ) ( t+1 ) from fun t ht=> ( ( Nat.succ_pred_eq_of_pos ( ht rfl ) ) ▸ H k (t-1) (by omega) ); intro k'; induction k' with
       | zero=> intro t ht; exact captive ( j:=t+1 ) h (by omega) hv
       | succ k' IH=> intro t hr; obtain hS:= helm_size hp hU (m:=t+1) ( IH ( t+2 ) ( by omega ) ) (fun i hv=> ih i hv ( hv.trans hm ) ) (pays_p hv); exact fountain hU ((( plenary M ).lives he.life m)|>.cross) ( he.vital m ) hv hS ( Well.cram ( ht m hm ) (fun _=>Nat.succ_pos _) ) -- t+2+1 defeq t+1+2
lemma helm_up (hp: liveP (face R) η)(he:Response X M η b)(hv:nn a)(ht:∀ m<n,totalT (initial R) (X m) a true)(m:ℕ)(h:m<n): totalT (face R) ( helm M η X m ) (peak R eps_gain a) false:= by
    have hh:= upper hp he hv ht; exact form_of (fun k _=> helm_size hp (( he.life m ).cross) ( Well.cram (hh m h) (fun _=> Nat.succ_pos _) ) (fun i hi=>hh i (hi.trans h)) (pays_p hv))
-- scalar row Body
abbrev bare ( F:Glade G I )(i:I)(t:ℝ):= F i t []
abbrev bareS (S:Home α I)(F:Glade G I):= fun x=> bare F ( S.pick x) ( S.t x )
lemma here' (he:taxi S F x 0): paid S.toScale (fun i=> ‖bareS S F i‖) x:= by obtain ⟨C,hC,k,h⟩:= he ℝ [] rfl; refine ⟨ C,hC,k,fun i=>?_⟩; specialize h i 0 trivial; simp only [ Scale.full, Scale.weight_zero,mul_one, Qbud,pitch,fieldDim,List.map_nil,List.sum_nil,zpow_zero,one_mul ] at h; exact h
lemma offers (hp:taxi (face R) F (peak R eps_gain a) 0) (hT:Every R): ∃ C:ℝ,0<C∧∃ k:ℕ,∀ i,∀ t≥R.beg i, ‖bare F i t‖ ≤ C*R.logPart i^k*wake R eps_gain a i * LogTime.polyExp eps_gain k t:= by
    obtain ⟨C,hC,k,h⟩:= here' hp; refine ⟨ C,hC,k,fun i t ht=>( h ( R.choose i t (by rwa [hT]) ) ).trans_eq ?_ ⟩; unfold face peak wake LogTime.polyExp; dsimp only [ IntervalFamily.primary, IntervalFamily.choose,index,IntervalFamily.t ]; rw [mul_pow]; rw [show -eps_gain*(t-R.beg i)= eps_gain*R.beg i + (-eps_gain*t) by ring, Real.exp_add ]; ring
lemma low_count (hp: taxi (face R) H (peak R eps_gain a) 0)(hv:Velocity F H)(hx:nn a)(hT:Every R) : (∀ i,Allow F i) ∧ paid ( initial R ).toScale (fun i=> ‖blade F i - bare F i ( R.beg i )‖ ) a:= by
    obtain ⟨C,hC,k,h⟩:= offers hp hT; let K i:= C* R.logPart i^k*wake R eps_gain a i; have hK(i:I):0 ≤ K i:= by unfold K; have hz:=R.lg i; have hu:= wake_nn (R:=R) (u:=eps_gain) hx i; positivity;
    obtain he:∀ i,Allow F i:= by
       intro i; obtain ⟨l,h⟩:= limits p_gain ( R.beg_nn i ) ( hK i ) k (bare F i) (bare H i) (fun t ht=> ( hv i t [] ).hasDerivWithinAt ) (h i); obtain he:blade F i=l:= Tendsto.limUnder_eq h; unfold Allow; rw [he]; exact h
    obtain ⟨b,hb,hB⟩:= LogTime.backward_cost ( E:=ℂ ) p_gain k; refine ⟨ he, C*b,by positivity,k,fun i=>?_⟩; let p:= R.beg i ; have hu(t:ℝ) (ht:p≤t): dist ( bare F i p ) ( bare F i t ) ≤ _ := hB _ _ _ ( R.beg_nn i ) ht ( hK i ) _ _ (fun s hs=> ( hv i s [] ).hasDerivWithinAt ) ( fun r hr=> h i r hr.1 );
    dsimp only; rw [← dist_eq_norm,dist_comm]; refine le_trans (le_of_tendsto ( tendsto_const_nhds.dist (he i)) ((eventually_ge_atTop p).mono hu)) ( le_of_eq ?_ ); unfold K LogTime.polyExp wake initial; simp only [neg_mul,exp_neg ]; rw [mul_pow]; field_simp
-- scalar reading through scale at seams and nulls
lemma inclusive (he:Response X M η b)(hp: liveP (face R) η) (ht: Every R)(hv:∀ m<n,totalT ( initial R ) ( X m ) a false)(ha:nn a): ∀ m<n, paid R.dawn (fun i=> ‖blade ( X m ) i‖) a:= by
    intro m hm; obtain H:= helm_up hp he ha (fun m hm=> FormP.part (hv m hm)) m hm; obtain hh:= Well.cram H ( n:=0 ) (fun i=> Bool.noConfusion i);
    obtain ⟨hP,C,hC,k,h⟩ := low_count hh ( he.vital m ) ha ht; obtain ⟨U,hU,l,hL⟩:= here' ( S:=initial R ) ( Well.cram ( hv m hm ) (fun i=> Bool.noConfusion i)); refine ⟨ C+U,add_pos hC hU,k+l,fun i=>?_⟩; let Q:= bare (X m) i ( R.beg i ); let V:= blade (X m) i; -- ambiguity
    change ‖_‖≤_; obtain hk:= norm_add_le (V-Q) Q; rw [sub_add_cancel] at hk; apply hk.trans ( (add_le_add (h i) (hL i)).trans ?_ ); have hw:= R.dawn.one_le i; have hA:= ha i; unfold initial at *; rw [ add_mul C, add_mul ]; gcongr <;> omega
end YM.FVA2.O.Rough
