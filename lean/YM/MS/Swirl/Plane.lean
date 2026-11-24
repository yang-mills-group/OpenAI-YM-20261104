import YM.MS.Swirl.Sits
/-!
# Projected and unprojected finite Wick rule. Normalization cancellation.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Orbit Cog Orbit.LogReal Book Convolve Program Puff Engine SplitP Actors Dynamics Puff.Mom
open scoped Topology ContDiff Interval
variable {A E I:Type} {p:Sector A}[Fintype A]{L:Lines A} -- placeholder
variable {S:Cog p}{K:Grain A}{b:Bool}{Q V G':SpecB A}{n:ℕ} {X: T ℂ}{F:BL A}
local notation "T"=> PermV p
local infix:70 " ⋆ "=> Actors.core (PermV p)
local infix:70 " ⚘ "=> Actors.core Trunk
local notation "W"=> ℶV ( imageV S b K )
abbrev ReadP (S:Cog p)(b:Bool):= pointL ℕ ( S.readerV b )
local notation "P"=> ReadP S b
-- need no Symm for scalar but needed for projecting costs.
omit [Fintype A] in
lemma acuity (S:Cog p)(u v:ℂ)(z:ℂ): S.wheel u v (coin z)= coin z:= by
    apply ext_D; · exact Cog.wheel_nil ..
    intro i; rw [wheel_rule,blend_at,Cylinder.coin_nod,Cylinder.coin_nod,map_add,smul_zero,smul_zero,map_zero,add_zero]
lemma readSym (S:Cog p)(hp:Symm p F)(u v:ℂ): Symm p ( S.wheel u v F ) := by
   let Ψ:= S.wheel u v; let Δ(x:A):= S.blend u v x; have ht ( F:BL A )(i j:A)(hp:Symm p F): Δ j ( Δ i F )=(cross (p i) (p j):ℂ) • Δ i ( Δ j F ):= by
       simp_rw [ Δ,blend_at,map_add,map_smul ]; rw [ hp.commute j i,hp.commute ( S.mode j ) i, hp.commute j ( S.mode i ), hp.commute ( S.mode j ) ( S.mode i ), S.vivid, S.vivid ]; module -- simplification maybe LinearMap map after Δ inputs.
   intro l i j s; induction l generalizing F with| nil=> change D j ( D i (Ψ F)) s=_*D i ( D j (Ψ F)) s; unfold Ψ; simp_rw [wheel_rule]; change S.wheel u v ( Δ j ( Δ i F ) ) s=_; rw [ht _ _ _ hp,map_smul]; rfl| cons a l ih=>
       change D a ( S.wheel u v F ) _= _ * D a (S.wheel u v F) _; rw [ wheel_rule ]; refine ih ?_; rw [ blend_at ]; exact ( Symm.smul _ ( hp.drop a ) ).add ( Symm.smul _ (hp.drop _) )
lemma readFee (S:Cog p) (b:Bool) (he:F∈FeeP p): readerV S b F∈ FeeP p := by
    cases b; exact he
    obtain ⟨h,k,hk⟩:= fee_spec he; exact ⟨ readSym S h _ _,minH ( (gl_read S true).lap _ _ hk ) ⟩
lemma soldΓ (h:Γ Q p): Γ (P Q) p:= fun i _=> readFee S b ( h i ( Set.mem_univ _ ) )
lemma lore : Tether P ( T ) ( T ):= by
    suffices H:Tether ( readerV S b ) (actor p) (actor p) from H.Extrapolation useN; cases b; · exact ⟨ rfl,fun _ _=> rfl ⟩
    exact ⟨ acuity S _ _ _,fun _ _=> S.rotate_p .. ⟩
-- Wick-to-ordinary ratio.Z q series.Holes
lemma readOne (h:S.phase K)(hv:F∈Mini A): View (imageV S b K) ( readerV S b F )= View (imageV S b K) F:= by
   obtain ⟨k,hk⟩:= hv; let J:= imageV S b K; let V:= readerV S b; have he n (F:BL A): tep J n (V F)= V ( tep J n F ):= by induction n with| zero=> rw [rise]; rfl| succ n ih=> rw [teen,ih,teen,map_smul, read_pc S b h ]
   change Shot J _ []= Shot J _ []; rw [ dawn J ( (gl_read S b).lap _ _ hk ), dawn J hk, effect,LinearMap.sum_apply,LinearMap.sum_apply ]; change (∑ j∈ Finset.range (k+1), (tep J j) ( V F ) ) []=_; simp_rw [ he, ← map_sum V ]; cases b; rfl; exact S.wheel_nil ..
lemma orderΦ (h:S.phase K)(hx:Γ V p): W (P V)= W V:= funext fun i=> readOne h ( fee_spec ( hx i ( Set.mem_univ _ ) ) ).2
lemma P_exp : P ( exp0 p G' )= exp0 p ( P G' ):= by funext i; refine ( show Tether (readerV S b) (actor p) (actor p) from ?_).figure useN _ _; cases b; exact ⟨rfl,fun _ _=>rfl⟩; exact ⟨ acuity S _ _ _,fun _ _=> S.rotate_p .. ⟩
def Endμ (K:Grain A)(p:Sector A)(Q V:SpecB A)(Z: ℕ→ℂ): Prop:= ℶV K ( ( PermV p ).core ( exp0 p Q ) V )= ℶV K ( exp0 p Q ) ⚘ Z -- notation overwritten K explicit? p shadow
lemma through (h:S.phase K)(he:Γ V p)(hp:Γ Q p): Endμ (imageV S b K) p Q V X↔ Endμ (imageV S b K) p ( P Q ) ( P V ) X:= by unfold Endμ; rw [← P_exp,← ( lore ( S:=S ) ).craft, orderΦ h (expΓ hp), orderΦ h (ΤΓ_pair ( expΓ hp ) he) ] -- orientation
-- normal
section scalar
variable [AddCommGroup E] [Module ℂ E]
omit [Module ℂ E] in
lemma lone_use (E:E): useN.refineV E 0=E:= by unfold refineV; exact if_pos rfl -- notation unaffected
variable (S0:Actors E){X U Y:ℕ→E}
lemma taut (h:X 0=S0.unit)(hp: ( S0.stack useN ).core X U=(S0.stack useN).core X Y): U=Y:= by
   funext n; induction n using Nat.strong_induction_on with
   | h n ih=>
      have hc:= congr_fun hp n; change useN.Lift S0.core X U n=useN.Lift S0.core X Y n at hc;
      let PY i:= Domain.paths i 0; have hl(n) (v:ℕ→E) : (∑ j∈antidiagonal n,S0.core (X j.1) ( v j.2 ))=v n+ ∑ j∈ PY n, S0.core (X ( n-j )) (v j) := by rw [Tone.Frame.canon_sub (fun i j=>S0.core ( X i ) (v j)),h,S0.identityK]
      change (∑ j∈antidiagonal n,S0.core (X j.1) ( U j.2 ))=∑ j∈antidiagonal n,S0.core (X j.1) ( Y j.2 ) at hc; rw [hl,hl] at hc; have hx : ∀ j∈ PY n,U j=Y j:= fun j hj=> ih j ( early _ _ _ hj |>.2 ); rw [Finset.sum_congr rfl ( fun j (hj:j∈ PY n)=> congr_arg ( S0.core ( X (n-j) )) ( hx j hj ) ) ] at hc; exact add_right_cancel hc
end scalar
lemma yetB (h:Q 0=0): ℶV K ( exp0 p Q ) 0=1:= ( congr_arg (View K) (Stencil.simple_E (actor p) Q useN h) ) |>.trans ( minView K _ )
lemma classicalμ {x y:ℕ→ℂ}(h:Q 0=0)(he:Endμ K p Q V x)(hp:Endμ K p Q V y): x=y:= taut Toy ( yetB h ) ( he.symm.trans hp )
end YM.MS.Swirl
