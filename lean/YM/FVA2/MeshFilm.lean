import YM.FVA2.CastMark
/-!
# Uniform time on marking.Poesy.L∞
 -/
set_option autoImplicit false
set_option maxHeartbeats 470000
noncomputable section
namespace YM.FVA2.Poesy
open YM.MS Function Set Filter Topology MeasureTheory Real Metric
open MS.Plane MS.Koszul MS.Landau Detect MS.Heat MS.Tone MS.Latch MS.Latch.Job MS.Rake MS.Orbit MS.Breeze MS.Book MS.Book.Convolve Flux
open MS.Osc MS.Osc.Snap MS.City MS.Rake.Geo MS.Land MS.Local.Physical MS.Port MS.Tide MS.Vista MS.Vane MS.Dial MS.Wind MS.High Wire Belt
open scoped BigOperators ContDiff
variable {G: Gauge} {I W: Type} [LinearOrder W] {v:ℝ}
variable {A: Deck G}{B:Booked A}{S:MS_Data G B}
local notation "Υ" => frameF I v
local notation "Δ"=> constantP G I (PlanetD G)
section belts
variable {x: Position W I}{U: Rake.Dance G I W}{a: W→Choice v S}
variable (h:Mesh (frameF I v) x)(hu:Frozen a U x) {w: Finset W}
def season (t:ℝ)(T:Belt I):= ∃ F: ∀ i, t∈T.slot i, let K(i:I):T.time:= ⟨i,t,F i⟩; Sheet T.price 1 ( plug (constantP G I ( PlanetD G )) ) ∧ (∀ i j, T.price.basic (K i)=T.price.basic (K j) ∧ T.price.length (K i)= T.price.length (K j)) ∧ ∀ w:Finset W,w.Nonempty→∀n,∃ v:T.time→ℝ, nn v ∧ Here false true T ( U w n ) v ∧ ∀ i j,v (K i)=v (K j) -- U binder not present add
include h hu
lemma pension (t:ℝ) : ∃ T:Belt I, season ( U:=U ) t T:= by
    rcases le_total t 0 with H|H;
    · refine ⟨ east Υ false, fun i=> H, Dial.power0, fun i j=>⟨rfl,rfl⟩, fun w z n=> ?_⟩; obtain ⟨d,hT⟩:= tip0 ( passage a h ) hu z (n:=n); exact ⟨ _, rateC _ _,hT.2.2, fun i j=> rfl ⟩
    exact ⟨ West Υ, fun i=>H, ( moneyCast a _ westV ).χ, fun i j=>⟨rfl,rfl⟩, fun _ z n=>⟨_, FarBasis _ _ _, farther (passage a h) (moneyCast a _ gulfG) ( moneyCast a _ westV ) hu z n, fun i j=> rfl ⟩⟩
lemma frontIn (hv:2≤w.card)(n:ℕ) : Came Υ false ( rhs x (fun _=>planeF) Δ Δ ( approach Υ S ) U w n ):= by
    refine let T:= passage a h; let V:= masterD G I Υ; let Y:= U w n; let L:= ∑ i∈ Domain.paths n 0, expJ Δ ( approach Υ S ( n-i ) ) ( U w i ); ?_; -- Domain namespace
    obtain hc : Came Υ false Y := emerged T hu hv n; obtain Hx : Came Υ false L:= seamount (fun i hi=> cone V (emerged T hu hv i) ( T.energy (n-i) (by obtain hp:i<n:= (Finset.mem_Ico.mp hi).2; omega)) );
    let R:= ∑ i∈ picks w, ∑ j∈ Finset.antidiagonal n, regionC (fun _=>planeF) ( rootX x i-rootX x w ) Δ ( U i j.1 ) (U (w\i) j.2 ); have H: Came Υ false R:= by
       apply seamount; intro i hi; apply seamount; intro j hj; obtain ⟨d,hd⟩:= tip0 T hu ( n_small hi |>.2.1 ) ( n:=j.1 ); obtain ⟨e,he⟩:= tip0 T hu ( n_small hi |>.2.2.1 ) ( n:=j.2 ); exact Geo.touch V ( Rake.space h hi ) hd he
    have hh:= Dial.CameZ hc; exact ⟨ hh.1.add (Hx.1.add H.1), collect_p hh.2 ( collect_p Hx.2 H.2 )⟩
omit h hu [LinearOrder W]
end belts
section domination
variable {F:Glade G I}{r:ℕ}
-- Uniform integrability (separate geometry not continuity).
def Sec {V:Type} (F:I→V→ℂ)[MeasurableSpace V](m:Measure V): Prop:= (∀ i, Integrable ( F i ) m ) ∧ ∃ B: V→ℝ, Integrable B m∧∀ᵐ u ∂m,∀ i,‖ F i u‖≤ B u
lemma DomT (h52:Came Υ false F)(hx:Fed Υ r 0 F)(l:Legs (Lane4 G)) (t:ℝ): Sec (fun i s=> F i s l) (volume.restrict ( Iic t )):= by
   refine ⟨ fun i=> h52.1.trainS ( born Υ G false ) i t _ (fun x=>Bool.noConfusion x),?_⟩; obtain ⟨m,hm,h⟩:=boxX F h52 l; by_cases H:t ≤ 0; · exact ⟨ m,hm.mono_set ( Iic_subset_Iic.mpr H ), ( ae_restrict_mem measurableSet_Iic ).mono (fun u hu i=> h i u ( le_trans hu H )) ⟩;
   -- compact bound on West through upper endpoint (g uniform)
   let K:= West Υ; obtain ⟨C,hC,k,hk⟩:= ( hx ℝ ( ray l ) ( fun i=>Bool.noConfusion i ) ( fun i=> Bool.noConfusion i ) ).norm_cost; let p:ℤ:= pitch ( ray l ); let f(s:ℝ):= C*((1+|v|)*(1+|s|)*(1+exp s*1))^k * ((exp s)^p); have hv(i:I)(s:ℝ)(ht:0≤s) : ‖ F i s l‖ ≤ f s:= by
       let c: K.time := ⟨ i,s,ht⟩; specialize hk c 1 trivial; dsimp only at hk; rw [show Chart ( plug (J:= K.slot) F ) (ray l) c 1=F i s l from ?_] at hk; swap; · unfold Chart; rw [ ray_sail ]; rfl
       apply hk.trans; rw [ show (K).price.full.cheap c (1:ℝ)= _ from ?_, today c ]; -- hidden term needs explicit; inspect
       unfold f; gcongr
       apply mul_le_of_le_one_right (zpow_nonneg (exp_pos _|>.le) _); unfold far ace; rw [show (frameF I v).θ c.fst=0 from rfl] -- rewrite c.fst
       rw [mul_zero,exp_zero,one_mul]; exact expoW c
       unfold Scale.full Scale.weight; dsimp only; rw [norm_one]; rfl
   let M(q:ℝ):= if q≤0 then m q else f q; refine ⟨ M,?_, ( ae_restrict_mem measurableSet_Iic ).mono (fun u hu i=>by unfold M; split; exact h i u (by assumption); exact hv i u (by linarith)) ⟩; apply IntegrableOn.mono_set (t:= ( Set.Iic 0 ) ∪ ( Set.Ioc 0 t )) ?_ ?_; -- signature
   · refine IntegrableOn.union ( hm.congr_fun (fun i hi=> Eq.symm (if_pos hi)) measurableSet_Iic ) ?_; have hc:Continuous f:=by unfold f; fun_prop (disch := (intro a; left; exact (exp_pos _).ne'))
     apply (( hc.continuousOn.integrableOn_compact ( μ:=volume ) ( isCompact_Icc ( a:=0 ) (b:=t) ) ).mono_set ( Set.Ioc_subset_Icc_self ) ).congr_fun _ measurableSet_Ioc; exact fun i hi=> Eq.symm (if_neg (not_le_of_gt hi.1))
   rintro x hx; by_cases hh: x≤0; exact Or.inl hh; exact Or.inr ⟨by linarith,hx⟩
variable {E:Type}[NormedAddCommGroup E][ NormedSpace ℝ E ] {P:Belt I}
lemma DomR [Nonempty I]{ f:P.time→ QP × E→ℂ} {a:P.time→ ℝ}{ K:I→ P.time} (h:∀ i j, P.price.basic (K i)= P.price.basic (K j) ∧ P.price.length (K i)=P.price.length (K j)) (hp:pole P.price f a)(hv:∀ i j,a (K i)=a (K j))(v:E): Sec (fun i q=> f (K i) (q,v)) planeF:= by
    let p:I:= Classical.arbitrary I; obtain ⟨C,hC,n,hx⟩:= hp.dominates 0 5; simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at hx; let W:= C * P.price.full.cheap (K p) v ^ n * a (K p); let A(q:QP):= W* P.price.dust 5 (K p) q; have hA:Integrable A planeF:= (( Vane.beacon _ ).integrable (K p)).const_mul W; have hq i q : ‖f (K i) (q,v)‖≤ A q:= by apply (hx (K i) q v trivial ).trans; apply le_of_eq; unfold A W Scale.dust Scale.full Scale.weight; dsimp only; rw [ hv i p, (h i p).1,( h i p ).2 ];
    exact ⟨ fun i=> hA.mono' (((hp.smooth ( K i ) ).continuous.comp (f:=fun q:QP=>(q,v)) (by fun_prop)).aestronglyMeasurable) (Eventually.of_forall (hq i)),A,hA,Eventually.of_forall (fun q i=>hq i q) ⟩
end domination
end YM.FVA2.Poesy
