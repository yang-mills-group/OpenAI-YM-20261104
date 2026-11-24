import YM.MS.Vista.Motion
/-!
# Mark difference, geometry charge. include rank-zero. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Filter Function Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{b c:Bool}
  {V: Visa I}{ P:Belt I}{L:I→Side}{K H:Planet G I}{D D':H_defect G I}{X Y:Rake.Site G I}
 {M N:Rake.Dance G I W}{A:I→Cover}{F:ℕ→I→Law G}{ Q:Seeds G I W} {n k:ℕ}{T: Finset W}
local notation "Ξ"=> Mid V L
local notation "Σ∅"=>outside L
local notation "Ϝ"=>enterV L b
local notation "ν"=> Ap Ξ (tickA L)
abbrev RateΔ ( M:Visa I )(L:I→Side)(n:ℕ):= Beef (Mid M L) * gainQ ( Mid M L ) L n
lemma plotΔ ( V:Visa I )( L:I→ Side)(i:ℕ): nn (RateΔ V L i):= joy ( biteZ ( Mid V L) ) ( gain_pos _ _ _ ) -- linearorder unused
abbrev marketS (P:Belt I)(X:Rake.Dance G I W): Prop:= ∀ s:Finset W,s.Nonempty→∀ i,MarkT P (X s i)
variable (S: Orbit.LogReal.Circuit (enterV L b) K F A Q X D M)(S': Circuit ( outside L ) H F A Q Y D' N)
   (P0:Piece ( Mid V L ) K 1) (hv: stepOne V L K H)(hV: bulk ( Mid V L) X)(he: ∀ n,0<n → DoubleB V L true true ( X n-Y n ))(hD:Cushion ( Mid V L ) D)
 (hM:marketS (Mid V L) M) (hN:marketS (Mid V L ) N) (hZ:∀ z,TPaid ( Mid V L ) ( μF ( Mid V L ) L ) ( Ap ( Mid V L ) (tickA L) ) ( loci (enterV L b) z ) A)(hω: RepT V L A)
include S S' P0 hv hV he hD hM hN hZ hω
abbrev ΔMark (M: Visa I)(L:I→Side)(b:Bool)(H: Glade G I): Prop := ∀ n,WarpHere false b ( Mid M L ) H (RateΔ M L n)
lemma Progress (hs:T.Nonempty)(n:ℕ)(hp:∀ s⊂ T,s.Nonempty→∀ k,ΔMark V L true (M s k-N s k))( hx:∀ i<n,ΔMark V L true (M T i-N T i) )(l:ℕ): HandC false false Ξ (campus Ϝ A K X D ( M T ) M T n-campus Σ∅ A H Y D' (N T) N T n) (RateΔ V L l):= by
    have Hζ:= M_vel ( b:=b ) P0; have hz:=( plotΔ V L l ); unfold campus; rw [ add_sub_add_comm, idle_d (deadD rfl S'.defect), ( show ∀ x y z:Glade G I,x+y-(z+0)= (x-z)+y from fun x y z=>by abel) ]; refine beauty ( beauty ?_  ?_  ) ?_ 
    · unfold lonely; rw [← Finset.sum_sub_distrib]; refine Cuba _ hz fun i hi=>?_ ; obtain hr:=early _ _ _ hi; exact step_acc P0 hv ( hV (n-i) (by omega) ) ( he _ (by omega) l ) ( hN T hs i ) ( hx i hr.2 l ) ( biteZ _ ) ( gain_pos _ _ _ )
    · refine Cuba _ hz fun j hj=> Cuba _ hz fun i hi=>?_ ; obtain hi:=early _ _ _ hi; obtain ht:0<n-i:= (by omega); obtain hc:= cabin_T Hζ (hZ j) ( hD j ( n-i ) ht ) ( hM T hs i ) ( S.fund j ( n-i )|>.1 ) ( S.port T i|>.1 ) (fun i=>zero_le_one) ( biteZ Ξ ) l; rw [ one_mul,one_mul,growth_μ ] at hc; exact hc
    unfold archB; rw [← Finset.sum_sub_distrib]; refine Cuba _ hz fun i hi=> ?_ ; rw [← Finset.sum_sub_distrib]; refine Cuba _ hz fun j hj=>?_ ; obtain ⟨Q,hU,hW,h⟩:= n_small hi; unfold zip2; rw [ show adjust (outside L).orbit (feeling Σ∅ true A A H ( N i j.1 ) ( N ( T\i ) j.2 ))=0 from rfl ]; rw [add_zero,add_sub_right_comm]; refine beauty ?_ ( adjustL _ hz ( t_self P0 hω ( S.port i j.1 |>.1 ) (S.port _ _ |>.1 ) (hM i hU j.1) (hM (T\i) hW j.2) l ) ) -- Σ∅. bug use `(outside L).orbit`. proof rewrite h.N
    exact curveδ P0 hv ( S.port i _|>.1 ) (S'.port ..|>.1 ) ( S.port ..|>.1 ) ( S'.port ..|>.1 ) l ( hN i hU _ ) (hN _ hW _) (hM _ hW _) (hp i Q hU j.1 l) (hp _ h hW j.2 l)
omit hZ he hV hD in -- Lens Progress.Clock.self includes p_remote
lemma imageSelf (i k:ℕ)(h:T.Nonempty){r:ℕ}(hx:SpanW false Ξ ( M T i-N T i ) ( RateΔ V L k ) (r+2)): Spd false Ξ (zip0 Ϝ K A (M T i) - zip0 Σ∅ H A (N T i)) (RateΔ V L k) r:= by -- needs hN for plateau H.; don't omit hN
    rw [ flat_zip0 Σ∅ rfl ]; have hh:= plateau (b:=b) (biteZ Ξ) P0 hv ( S.port T i|>.1 ) ( S'.port T i|>.1 ) hx ( pinch ( hN T h i ) ( r:= r+2 ) (fun _=> by omega) ); unfold zip0; rw [add_sub_right_comm]; unfold Spd coinF; rw [map_add]; apply Lens.plus hh; -- second case
    cases hc : (enterV L b).orbit; · rw [ adjust, if_neg (by decide :¬false=true), map_zero ]; exact pinch (b:=false) (c:=false) (Lease.zero (plotΔ V L k)) (fun h=>Bool.noConfusion h)
    rw [ adjust,if_pos rfl]; change Lens false (Ξ).price ( plug (bend G I (click Ϝ true ( Vary A ) K ( M T i )))) _ _; rw [wc_click]; obtain hp:= p_remote hω.pay ( M_vel (b:=b) P0 |>.1 ) ( P0 true ) ( footage ( M T i ) (S.port T i|>.1 ) ) (p:=true) (fun _=>rfl : true=true→false=false ) ( pinch ( hM T h i ) ( r:=r+2 ) (fun _=> by omega) ) ( fun i=>zero_le_one ) (biteZ Ξ) k; apply Lens.up hp; exact fun x=>by simp only [ Pi.one_apply,one_mul,Pi.mul_apply, coinV ]; rfl
include hZ he hV hD hN -- ensure.W robust
lemma O_motion (h:T.Nonempty)(hk:Glow K)(hg:Glow H)(n:ℕ): ΔMark V L false (M T n-N T n) := by
    induction T using Finset.strongInductionOn generalizing n with | _ T ih=>
      induction n using Nat.strong_induction_on with| h n hρ=>
         intro k; let X':= M T n-N T n; let v:= k+1; let U:= RateΔ V L v; have hm:= hot S hk h n; obtain he':= hot S' hg h n; unfold fort at hm he'; have ht:= steered _ _ _ _ _ _ hm he';
         have hz:= Progress S S' P0 hv hV he hD hM hN hZ hω h n ( fun i hi hk n k=>Lease.highp ( ih i hi hk n k ) ) (fun i hi v=> Lease.highp ( hρ i hi v )) v;
         apply Lease.sticks ( a:=U ) _ (fun i=>mul_le_mul_of_nonneg_left ( gain_le (show k≤v from (by unfold v; omega)) i ) ( biteZ Ξ i)); refine kernel (a:=0) nextM.acc ht ( colony nextM.acc v (by unfold v eps_gain; push_cast; norm_num; linarith [Nat.cast_nonneg (α:=ℝ) k] )) ( plotΔ V L v ) (no_credit _ ( plotΔ V L v ) ?origin ) ?lens;
         case origin=> intro i; change X' i (τ 0)=0; unfold X'; simp_rw [τ0,Pi.sub_apply, S.crew.2 T h n |>.1 i,S'.crew.2 T h n|>.1 i,sub_self]
         case lens=> intro r hr hF; unfold coinF; rw [ map_add ]; exact Lens.plus ( imageSelf S S' P0 hv hM hN hω n v h hF ) ( pinch hz (fun h=>Bool.noConfusion h) )
end YM.MS.Vista
