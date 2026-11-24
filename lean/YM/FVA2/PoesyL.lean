import YM.FVA2.MovingMark
/-!
# Derivative of pinned branch. Translation-covariant derivative accounts for root changes

 Along a single moving source. Extend iterated. Purpose rate.
 -/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.FVA2.Poesy
open YM.MS Function Set Filter Topology MeasureTheory Real Metric
open MS.Plane MS.Koszul MS.Landau Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Breeze MS.Book MS.Book.Convolve Flux
open MS.Osc MS.Osc.Snap MS.City MS.Rake.Geo MS.Land MS.Local.Physical MS.Port MS.Tide MS.Vista MS.Vane MS.Dial MS.Wind MS.High MS.Fiddle Wire Belt Finset
open scoped BigOperators ContDiff Classical
variable {G: Gauge} {I W: Type} [LinearOrder W] {v:ℝ}
variable {A: Deck G}{B:Booked A}{S:MS_Data G B}
variable {x: Position W ℝ}{U V: Rake.Dance G ℝ W}{a: W→Choice v S}
variable (h:Mesh (frameF ℝ v) x)(hu:Frozen a U x) 
variable (g: W) (d:QP)
local notation "Υ"=> frameF ℝ v
local notation "Δ"=> constantP G ℝ (PlanetD G)
variable (hv:Frozen ( awaken g a d ) V x)
variable {Z: Set ℝ}(H:IsOpen Z)
variable (hA:PathAlong g d x Z)
variable {w y: Finset W}
local notation "Ψ"=> field (Landau.parity (A:=Axis) (C:=G.ColorIndex))
omit [LinearOrder W] in
lemma balanceUX (η:ℝ){F:Glade G I}{r:ℕ}(hp: Verdict (frameF I η) r 0 F): TendstoUniformly (fun t i=>F i t []) (Vane.blade F) atTop:= by -- Paint
    let P:= frameF I η; obtain ⟨ C,hC,k,hk⟩:= hp.2.1; have hb:= norm_of_nonneg (hC.le); obtain ⟨A,hA,hB⟩:= capped High.p_gain k; let r':ℝ := C*(1+|η|)^k; have hr : 0≤ r':= by unfold r'; positivity
    let B(t:ℝ):= r'*A*exp ( -(High.eps_gain/2)*t ); have ht (t:ℝ)(hp:0≤t)(x:I): dist (F x t []) (Vane.blade F x ) ≤ B t:= by
        rw [ dist_comm, dist_eq_norm ]; let T:Vane.Vista P:= ⟨ x,t, hp ⟩; obtain h:= hk T; apply h.trans; change C*((1+|η|)*(1+|t|))^k*( exp (((-(r:ℝ))-0)*0)* exp (-High.eps_gain*(t-0)))≤_; rw [abs_of_nonneg hp, mul_zero,exp_zero,one_mul,sub_zero, mul_pow ]; exact le_trans ( b:= r'*( (1+t)^k*exp (-High.eps_gain*t))) ( le_of_eq (by unfold r'; ring) ) ((mul_le_mul_of_nonneg_left (hB t hp) hr).trans_eq (by unfold B; ring))
    have hV:Tendsto B atTop (𝓝 0):= by simpa only [mul_zero] using! (tendsto_exp_atBot.comp ((tendsto_const_mul_atBot_of_neg (show -(High.eps_gain/2)<0 from by unfold High.eps_gain; norm_num)).mpr tendsto_id)).const_mul ( r'*A )
    apply Metric.tendstoUniformly_iff.mpr; intro ε hε; filter_upwards [hV.eventually (gt_mem_nhds hε),eventually_ge_atTop 0] with i hi hI; intro t; rw [dist_comm]; exact (ht _ hI _).trans_lt hi
include h hu
lemma bal (w: Finset W)(n:ℕ): TendstoUniformly ( fun t i=> U w n i t [] ) ( blade ( U w n ) ) atTop:= by
    rcases w.eq_empty_or_nonempty with rfl|H; · rw [hu.1]; simp only [Pi.zero_apply]; simp_rw [show blade (0:Glade G ℝ)=fun _=>0 from funext fun i=> (Fleet.allow_zero i).2]; exact Metric.tendstoUniformly_iff.mpr (fun ε h=>Eventually.of_forall (fun i j=>by simpa))
    exact balanceUX v (walletCast _ h hu H _)
include hv H hA
variable {g d}
lemma shipped (w: Finset W)(n:ℕ) : direct Z (liftP w g) 0 (blade ( U w n )) (blade ( V w n )):= by
    intro t ht; rw [zero_mul,sub_zero]; apply hasDerivAt_of_tendstoUniformlyOn (f:=fun q i=> U w n i q [] ) ( f':= fun q i=> liftP w g * ( V w n i q [] )) (g':=fun t=> liftP w g * blade ( V w n ) t) H ?_ ?_ (fun x _=> (bal h hu w n).tendsto_at _) ht
    · by_cases hx:g∈w; · simp_rw [liftP,if_pos hx,one_mul]; exact ( bal h hv w n ).tendstoUniformlyOn -- name
      simp_rw [liftP,if_neg hx,zero_mul]; exact Metric.tendstoUniformlyOn_iff.mpr (fun ε h=>Eventually.of_forall (fun i j _=>by simpa))
    exact Eventually.of_forall (fun n x hx=> by obtain hp:= movement h hu hv H hA w _ [] n x hx; simpa only [ net,List.map_nil,List.sum_nil, map_zero,zero_mul,sub_zero ] using hp)
omit h hu hv H hA
lemma pathWin [Fintype W] (o:ℝ){P: ℝ→W→QP}(hP:Injective (P o))(T:Set ℝ)(h:IsOpen T)(hx:o∈T)(hF:ContinuousAt P o)(hv:PathAlong g d (fun i p=> P p i) T) (L:W→Choice v S) (w: Finset W)(n:ℕ): HasDerivAt (fun p=> priceZ L (P p) w n) (liftP w g * priceZ (awaken g L d) ( P o ) w n) o:= by
    obtain ⟨ε,hε,hM⟩:= Metric.mem_nhds_iff.mp ((hF.tendsto.eventually (earlyW hP)).and ( h.mem_nhds hx )); -- he is eventually Clamp.E
    let Y:= ball o ε; let K(i:W)(k:ℝ):= Window i ( P o ) (P k); let Q:= pointI K; obtain hL:= turnH hP v; have he : Mesh Υ K:= fun i j hi=> by
         obtain ⟨⟨c,hc,hM⟩,⟨q,hq,h⟩⟩:= hL i j hi; exact ⟨⟨c,hc,fun i=> hM ( P i )⟩,⟨q,hq,fun i=>h ( P i )⟩⟩
    have ht(q) (hq:q∈Y): Q q=P q:= funext (fun i=> by unfold Q pointI K Dial.Window; rw [ if_pos ( show Clamp ( P o ) (P q) from ( hM hq ).1 ) ]); have hFX:PathAlong g d K Y:= fun i t hp=> (hv i t (( hM hp ).2)).congr_of_eventuallyEq (Eventually.mono ( isOpen_ball.mem_nhds hp ) (fun q hq=> congr_fun (ht q hq) i));
    obtain ⟨U,hU⟩:= footing L he; obtain ⟨V,hV⟩:= footing ( awaken g L d ) he; have hlo : o∈Y:= mem_ball_self hε; obtain hC := shipped he hU hV isOpen_ball hFX w n o hlo; have hInv:= solveZ _ he hV o w n; rw [show pointI K o=P o from ht o hlo] at hInv; rw [ zero_mul,sub_zero,hInv ] at hC; exact hC.congr_of_eventuallyEq (Eventually.mono (isOpen_ball.mem_nhds hlo) (fun p hp=> by show priceZ L (P p) _ _=_; exact (( solveZ _ he hU p w n ).trans ( congr_arg (fun r: W→QP => priceZ L r w n) (ht p hp) ) ).symm ))
lemma alongC [Fintype W] (g:W)(d:QP) (w:Finset W)(a:W→Choice v S)(x: W→QP)(hv:Injective x)(p:ℕ) : HasLineDerivAt ℝ (fun x=>priceZ a x w p) (liftP w g * priceZ (awaken g a d) x w p) x (Pi.single g d):= by
    let Y(t:ℝ):W→QP:= x+t• ( Pi.single g d:W→QP ); have ht: Y 0=x:= by unfold Y; simp
    have hp:= ( show Injective ( Y 0 ) by rw [ht]; exact hv );
    have hx : PathAlong g d (fun i p=>Y p i) Set.univ:= by
         intro i t hm; unfold Y; by_cases hi:i=g; · subst i; simp only [Pi.add_apply, Pi.smul_apply, ↓reduceIte,Pi.single_eq_same ]; exact hasDerivAt_id' t|>.smul_const d|>.const_add (x g) |>.congr_deriv (by simp)
         simp only [ hi,Pi.add_apply,Pi.smul_apply,Pi.single_eq_of_ne hi, ↓reduceIte, smul_zero,add_zero ]; exact hasDerivAt_const ..
    have he:= pathWin ( g:=g ) ( P:=Y ) 0 hp Set.univ isOpen_univ (Set.mem_univ 0) ( show Continuous Y from continuous_const.add (continuous_id.smul continuous_const) ).continuousAt hx a w p; rw [ht] at he; exact he
end YM.FVA2.Poesy
