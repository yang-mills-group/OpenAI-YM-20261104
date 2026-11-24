import YM.FVA2.RealizationN
/-!
# Field generator transports. Formal only

Can use to identify `b0` and one-vertex result across our convention and MS. This section
literally transports generators of the independently prescribed correlation-sector dilations,
rather than assume them to compute scheme.
-/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 740000
namespace YM.FVA2.RadScale.Era
open Function Filter Topology Set MeasureTheory Finset
open Lattice Maxwell Maxwell.Free Pert Pert.Position Pert.RawLabels PositionX PositionX.Bend PositionX.Jet PositionX.Ribbon Elegant Verne Strat Panel ColorCode
open MS MS.Land MS.Landau MS.Menus MS.Tide MS.Tone Hop Ember Taper Forge
open Month Meter
open scoped Topology BigOperators Classical ContDiff
section vehicle
variable {G:Gauge}{F:Labels.Frames G}
variable {W Q:ℝ→Hop F} {A: Panel F}{D:(d:ℕ)→ Detector F d}{r:ℝ}{R: Booth r F}
variable (T:Month A W D R) (K:Hop F) (HK:gradedStep K) (H:Month (Hop.act A K) Q D R) (s:ℝ)(d n:ℕ)
-- formula from `Montage`. Ψ(detector f inverse). position vs MS in obvious order.
include H T HK
local notation "Bx"=> Month.B W D
local notation "Cx"=> Month.B Q D
lemma diagMotion : Strat.resume (Bx s) K.f * Strat.resume K.Z ( Month.ψ Q s )= K.Z * Cx s:= by
    obtain hp:= congr_arg Hop.Z ( link T K H s ); let b:= (Q s).Z; let a(X:Strat F):= Strat.resume X K.f; have hb:(Q s|>.Z)*Cx s=1:= Month.warm s Q D |>.2.2.2; have hk: a ( Bx s ) * a ( W s|>.Z )=1:= by unfold a; rw [ ← resumeT _ _ K.rooted, Month.warm s W D|>.2.2.1,resume0 ]; -- rfl a metav
    rw [Taper.beam s K HK, walkZ,walkZ ] at hp; let T:= Strat.resume K.Z ( Month.ψ Q s ); change Strat.resume (Month.B W D s) K.f*T= _; conv_lhs => rhs; rw [← mul_one T] ; rw [← hb]
    rw [← mul_assoc T, show T* ( Q s ).Z= _ from hp, ← mul_assoc,← mul_assoc,hk,one_mul ]
    -- ...
omit H T HK in
private lemma outer_v {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{t:ℝ}{f:ℝ→Word V}{u:Word V}(h:∀ i, HasDerivAt (fun z=>f z i) (u i) t)(v:Word ℝ)(ht:light v): HasDerivAt (fun x=>ren v (f x) n) (ren v u n) t:= by
   simp_rw [ RadScale.substitute v ht ]; exact HasDerivAt.fun_sum fun i _=> ( h i ).const_smul _
omit H T HK in
private lemma patron {V:Type*}[NormedAddCommGroup V][NormedSpace ℝ V]{t:ℝ} {f g:ℝ→V}{u w:V} (hp:f=g)(h:HasDerivAt f u t)(hv:HasDerivAt g w t): u=w:= (hp ▸ h: HasDerivAt g u t).unique hv
omit H T HK in
lemma void_l (X:Word ( Buffer F d )): crossW 0 X n=0:= Finset.sum_eq_zero fun _ _=> zero_lB _
omit H T HK in
lemma void_r (X:Word ( Buffer F d )): crossW X 0 n=0:= Finset.sum_eq_zero fun _ _=> zero_rB _
local infixl:70 "◆"=> luxury
local notation "Υx"=> generation W D d
local notation "Υy"=> generation Q D d
/-- Differential version of map preserving manuscript's scale law. Coupling & horizon natural,
 signs from increasing log μ. incl derivative PS B incl coupling law ∂g B. -/
lemma transports_B : let f:= K.f; let Z:=K.Z.wire d; ren f Υx n+ incline (Month.β Q) Z n + crossW (ren f Υx ) Z n = Υy n+ crossW Z Υy n:= by
    intro f Z; let φ(t:ℝ):= ren (Month.ψ Q t) Z; let b(x):=ren f (drive W D x d); let c(s:ℝ):=drive Q D s d;
    have hc:= congr_arg (fun t:ℝ→Strat F=> fun x=>(t x).wire d) (funext ( fun i=> diagMotion T K HK H i )); change (fun t=> b t◆ φ t)=(fun t=> Z ◆ c t) at hc;
    let dZ:= incline (Month.β Q) Z; let ν:= ren f Υx; have he:= rate n (s:=0) (a:=b) (b:=φ) ( x:=ν ) (y:=dZ) ( fun i=> by exact outer_v (V:=Buffer F d) i ( f:=fun x=> drive W D x d ) ( calendar T d ) f K.rooted ) ( fun i=> by exact ren_at ( V:=Buffer F d) Z i H.headB H.tentative₀.1 (fun s=>(Q s).rooted) );
    have ht:= rate n (s:=0) ( a:=fun _=>Z) (b:=c) ( x:=0 ) (y:= Υy) ( fun i=> by exact hasDerivAt_const (x:=( 0:ℝ )) ( c:=(Z i:Buffer F d) ) ) (calendar H d);
    obtain hp:= patron (V:=Buffer F d) (congr_arg (fun z:ℝ→ Word (Buffer F d)=> fun t=>z t n) hc) he ht; rw [ show b 0=0 from ?_, show φ 0= Z from ?_,void_l,void_l,Pi.zero_apply,zero_add,zero_add,add_zero ] at hp; exact hp
    · unfold φ; rw [H.tentative₀.1,Jet.ren_head (V:=Buffer F d) ];
    unfold b; rw [first T ]; exact Verne.renZ (V:=Buffer F d) _ -- ]
-- specialize to Unity coherence; no new assumptions.
variable {h:G.Simple}(V:Warehouse G) {O: Land.Booked (wings G)}(M:MS_Data G O){t:ℝ}(R:Booth t V.F)(v:ℝ)(hx:Pic.pass V h M R)
local notation "Xv"=> Pic.X V h M v R
local notation "pV"=> Forge.transfer V M R v hx
local notation "Sv"=> chooseN V M R v hx
local notation "K"=> nested V.F h ( BoxOffice.warehouse V )
omit H T HK in
lemma proves : let χ:= (pV).Z.wire d; let ν:= generation ( Forge.Mray V h M R v hx ) K d; let μ:= generation ( Forge.Cray V h M R v hx ) K d; let fν:= ren ((pV).f) ν;
    fν n+ incline (Month.β (Forge.Xray V h M R v hx)) χ n + crossW fν χ n= μ n + crossW χ μ n:= by
    intro χ ν μ fν; let g:= Forge.transfer V M R v hx; let ρ:= Pic.marked V M v; let X:=Forge.Xray V h M R v hx; let C':=Forge.Cray V h M R v hx;
    have hC : Month (Hop.act ρ g) C' K R:= Forge.agrees V M R v hx ▸ Forge.real_c V h M R v hx;
    rw [show Month.β X=Month.β C' from ?_ ]; exact transports_B ( Forge.real_ms V h M R v hx ) g ( Forge.gradedT V M R v hx ) hC d n
    funext i; unfold Month.β; congr 1;
end vehicle
end YM.FVA2.RadScale.Era
