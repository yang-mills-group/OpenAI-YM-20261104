import YM.MS.Vista.Arena
/-!
# Mark normal bounds at finite & infinite: allow any stencils. Uniform.Separate comparison below. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type}{P:Belt I}{ L:I→Side}{V:Visa I}{Z:Lin I}{K:Planet G I}
    { F:Rake.Site G I}{ S0:I→ℝ} {p:I→Cover}{ T Y:Glade G I} { A B:I→Cover}{u v:P.time→ℝ}{g:ℕ→I→Law G}{b c:Bool}{ν:P.time→Measure QP}
lemma blend0 : adjust b (0:Glade G I)=0:= by unfold adjust; split_ifs <;> rfl
lemma color0 (Z:Lin I)(X:Glade G I): zip2 Z K A B 0 X=0:= by
   unfold zip2; have he(i): feeling Z i A B K 0 X=0:= by funext i t l; unfold feeling PairV; simp only [viν, Pi.zero_apply, mul_zero,zero_mul, integral_zero,Finset.sum_const_zero, mul_zero ]; exact map_zero ( allocate _ l )
   rw [he,he,blend0,add_zero]
lemma tree_nil (F:Glade G I): expJ K F 0=0:= funext fun i=> funext fun t=> (map_zero ( boulevard parity ( K i t ) ( F i t )))
variable {D: H_defect G I}
lemma idle_d (H:D=0)(k n) : foam Z K D F A k n=0:= by rw [ H ]; unfold foam; refine Finset.sum_eq_zero fun i hi=> Finset.sum_eq_zero fun j hj=>?_ ; exact color0 ..
lemma deadD (h:Z.orbit=false)(T: RecipeD Z K F D): D=0:= by
    refine soloX T (X:=D) (Y:=0) (fun i=> ⟨rfl,fun n he=>?_⟩); rw [HCur,idle_d (Z:=Z) (K:=K) rfl, adjust,h ]; simp only [ Bool.false_eq_true, ↓reduceIte,smul_zero,zero_add,add_zero, Pi.zero_apply ]; rw [show groups K F 0 n=0 from Finset.sum_eq_zero fun j hj=> tree_nil _ ]; refine ⟨ fun _=>rfl,?_⟩; rw [(engineV .. ).empty, add_zero ]; exact ⟨ ⟨0,fun _ _ _ _=>rfl⟩,fun _ _ _=> hasDerivAt_const .. ⟩
abbrev Beef (P:Belt I): P.time→ ℝ:= goodM P eps_gain
lemma biteZ (P:Belt I): nn ( Beef P ):= pay_m P _
lemma Biff (he: Vel P Z K ν u)(i:P.time): Beef P i ≤ 1:= Real.rpow_le_one_of_one_le_of_nonpos ( ( he.2.1 false ).room i ) ( neg_nonpos.mpr p_gain.le ) -- name?
lemma PaceF (a:I→ℝ)(h:Accel P a): Adjuster (G:=G) P false true (Beef P):= level h (show eps_gain ≤ (if true=true then 1 else (0:ℝ)) from s_gain.le)
-- Photon membership
variable {W:Type}[LinearOrder W]{ S:Finset W}{Q:Seeds G I W}{X:Rake.Dance G I W}
abbrev MarkT (P:Belt I)(F:Glade G I) := WarpHere false true P F ( Beef P )
abbrev fort (Z:Lin I)(v:I→Cover)(K:Planet G I)(X:Rake.Site G I)(Y:H_defect G I)(U:Rake.Dance G I W)(p:Finset W)(n:ℕ): Glade G I:= zip0 Z K v (U p n)+campus Z v K X Y ( U p ) U p n
-- Mark estimate. Use signed Theta weights.K.Flag.D always all if exists.
abbrev Presence (P:Belt I)(Z:Lin I)(ν:P.time→Measure QP)(T:H_defect G I)(A:I→Cover): Prop:= T=0 ∨ (Cushion P T ∧ ∃ s:P.time→ℝ,∀ z:Half,TPaid P ν s (loci Z z) A)
variable (hf: Circuit Z K g A Q F D X)(ht:Glow K)(he:bulk P F)(hx:Presence P Z ν D A)
include hf he hx
lemma lunch (hV:Vel P Z K ν u)(k:ℕ)(hs:∀ q' ⊂ S,q'.Nonempty→∀ j, MarkT P ( X q' j ))(hX:∀ i<k,MarkT P ( X S i )): HandC false false P (campus Z A K F D ( X S ) X S k) (u*Beef P) := by
   let v:= u*Beef P; have hh:nn v:= joy (hV.2.2) ( biteZ _ ); refine beauty (beauty ( Cuba _ hh (fun i hi=>?_)) ?D) (Cuba _ hh (fun i hi=>?_)); · exact step_F ( he ( k-i ) (by obtain hz:=early _ _ _ hi; omega)) ( hX i ( early _ _ _ hi|>.2) ) hV.2.1 ( biteZ _ ) hV.2.2
   · rcases hx with hx|⟨hτ,s,hS⟩; · rw [idle_d hx]; unfold HandC; rw [map_zero]; exact Lease.zero hh
     refine Cuba _ hh (fun i hi=> Cuba _ hh (fun j hj=>?_)); obtain h0:=early _ _ _ hj; obtain hz:0<k-j:= (by omega); simpa only [mul_one] using easy_T hV (hS i) ( hτ i _ hz ) ( hX j h0.2 ) ( hf.fund ..|>.1 ) ( hf.port S j|>.1 ) (fun i=>zero_le_one) ( biteZ _ ) -- Circuit.fund may order n? inspect
   obtain ⟨Q,hm,hU,H⟩:= n_small hi; refine Cuba _ hh fun j hj=>?_ ; obtain hz:= spin_d ( A:=A ) hV ( hs _ Q hm j.1 ) ( hs _ H hU j.2 ) (hf.port i j.1|>.1) ( hf.port (S\i) j.2 |>.1) ( biteZ _ ) ( biteZ _ ); apply Lease.sticks hz; exact fun i=>mul_le_of_le_one_right ( hh i ) ( Biff hV i ) -- intrinsic growth
include ht
omit hx he in
lemma hot (H:S.Nonempty)(k:ℕ): LookS (warp0 G I ( X S k )) (bend G I ( fort Z A K F D X S k )):= hooked ( hf.port S k|>.1 ) (( knit_plus ( LiftE.knit ( gen_zip0 _ ht _ ) (hf.port S k) ) ( campusK ht hf.finances (fun i k=>hf.fund k i) (fun v _=> hf.port v) k (fun i _=> hf.port S i) ) ) |>.1 ) (hf.crew.2 S H k|>.2)
lemma cabinet (hV: Vel P Z K ν 1)(hB: Accel P S0)(hP:∀ (S:Finset W), S.Nonempty →∀ n, Lease false true P.price ( LaunchF P S0 (warp0 G I ( X S n )) ) ( Beef P ))(hS:S.Nonempty)(k:ℕ): MarkT P ( X S k ):= by
   induction S using Finset.strongInductionOn generalizing k with| _ S ih=> induction k using Nat.strong_induction_on with| h k hz=>
       refine kernel hB ( hot hf ht hS k ) ( PaceF S0 hB ) ( biteZ _ ) ( hP _ hS _ ) ?_; intro r he' hX; obtain hs:= lunch hf he hx hV k ih hz; rw [one_mul] at hs; unfold fort coinF; rw [map_add]; have ht:= Bolt ( A:=A ) hV hX ( hf.port S k|>.1 ) ( biteZ _ ); rw [ one_mul ] at ht; exact Lens.plus ht (pinch hs (fun h=>Bool.noConfusion h))
omit ht in
lemma drive_budget (hx':Vel P Z K ν u)(hv:∀ S,S.Nonempty→∀ n,MarkT P ( X S n ))(hS:S.Nonempty)(k:ℕ): HandC false false P (fort Z A K F D X S k ) (u*Beef P):= by apply beauty _ ( lunch hf he hx hx' k (fun v _=>hv v) (fun i _=>hv S hS i) ); apply poses; intro r h0; exact Bolt hx' (pinch (hv S hS k ) (fun _=>by omega)) (hf.port S k|>.1) ( biteZ _ )
end YM.MS.Vista
