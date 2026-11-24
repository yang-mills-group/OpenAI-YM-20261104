import YM.MS.Tide.Germ
/-!
# Combine Taylor-Matching, both regulator estimates and exact BV-decoupling on the cover

 Note physical projection issues: wave-only invariance uses established actual Hessian and trace.
 Inputs rental fees.Aperture. Output all s/n eventually (coefficientwise), not one err bound claiming
 across horizon. Actual torus computations in Endμ and CCOrb named. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian Paint High Wind Rake Rake.Geo Vista Vane City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{t:Team}
    {F:Finset W}{φ: LitBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
-- native input stencil
def ApplyM (V: LitBook B)(t:Team)(a:Land.Prescription B)(u:W→Label B): W→ Actor G:= fun i=> Menus.rent V t ( a.fees ( u i|>.h ) (( u i ).item) )
set_option quotPrecheck false
local notation "Yr"=> ApplyM φ A.team A u
local notation "Ur"=> ApplyM φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Qr"=> SeedsW c φ A u P
local notation "φX"=> PortEntry φ A ∘ u
omit [LinearOrder W] in
lemma billMenus (hc:G.Simple): ReadyP A.team Yr ∧ ReadyP A.team φX∧ Changes Yr Ur A.team ∧ ∀ w, Menu A.team ( (φX) w ) ( Yr w ):= by
   refine ⟨⟨ fun _=> billRent ..,fun w x=> rented φ A.team x _ hc ⟩,⟨fun _=> decor ..,fun w x=> Menus.law φ A.team x _ hc ⟩,fun w x=> rankV ..,fun w=>?_⟩
   let X:= u w; let K:= A.fees X.h X.item; refine ⟨ ⟨ Menus.prim K, ⟨ (fun i y=> ( K i ).proof.actual y ),(fun i=> ⟨ _,( K i ).proof.ranks ⟩ ),fun i y=> ( K i ).proof.calm y,fun i=>( K i ).proof.polyn,fun _ _ h=>Bool.noConfusion h⟩,?_ ⟩ ⟩; intro y; change Menus.motto A.team K y= Menus.score φ A.team K y - Menus.rent φ A.team K y; rw [score]; abel
lemma pointed (k:Terrify W I) (he:k ∅=0) : ∀ i,Happy ( marked W ) (fun s n=> k s n i ):= by intro i; funext n; rw [ show ( marked W ).origin=∅ from rfl ]; change k ∅ n i=0; rw [he]; rfl
lemma zeroZ (hp:X ∅=0): toZ X ∅=0:= by funext n i; rw [ Fleet.toZ, hp ]; exact ( allow_zero ( G:=G ) i ).2
lemma payTune (hE: Mesh P ( info c ))(ht:Tendsto P.θ l atTop): Sparse l c:= by
   intro i j hi; obtain ⟨a,ha,hx⟩:= hE i j hi|>.floor; refine tendsto_atTop_mono ?_ (( tendsto_exp_atTop.comp ht ).const_mul_atTop ha) -- name
   intro p; apply ( hx p ).trans_eq; simp only [Pi.sub_apply, emb_sub]; rfl
-- agenda cumulants. no axioms
structure Judge (P:Geo I)(c:Berth ( W:=W ) ( I:=I )) (V:Visa I)(U X:Terrify W I)(L:I→Side)(l:Filter I)(u:W→ℕ): Prop where
    blanks : U ∅=0 ∧ X ∅=0
    stamp: ∃ Y F:Terrify W I, Y ∅=0 ∧ F ∅=0 ∧ (∀ s:Finset W,s.Nonempty→∀ n,title P eps_gain ( Vane.charge u s ) (Y s n-X s n)∧title P 0 ( Vane.charge u s ) (Y s n)) ∧ (∀ s:Finset W,s.Nonempty→∀ n,cash_out V L ( U s n - F s n )) ∧ (∀ n (s:Finset W),F s n=ᶠ[l]Y s n)
-- goals.Small
lemma assembly (hc:G.Simple)(hp: Clearance L x)(he: Vista.width L x)(hm:WidthW V P.η c)(ht: Mesh P ( info c ))(hv: Sparse l c)(b:Bool)(hV: TaylorOK S φ A) : ∃ (Z:Terrify W I)(X:Rake.Dance G I W), CCOrb G P.η A.team x L Qa b Z ∧
  (∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur ( bury i s Z )) ∧ DOrd M P S u ( info c ) X ∧ Judge P c V Z ( toZ X ) L l ( Label.h ∘ u ) ∧ ∀ s:Finset W,s.Nonempty→∀ n,Verdict P ( Vane.charge ( Label.h ∘ u ) s ) 0 ( X s n ) := by
   obtain ⟨hK,hP,H,hmenu⟩:= billMenus u (φ:=φ) (A:=A) hc; have heo : FlowSet V Qa:= moneyM c hm (fun i=>⟨ false,0,hK.badge i ⟩); let t:=A.team; obtain ⟨F,f,hF,hf,hT,h0,hpay⟩:= Ωgo ( P:=x ) hV.bulk heo hm.proper b hp he; obtain ⟨Z,X0,hZ,hZ',hX,h',hx⟩:= Ωgo (P:=x) hV.bulk ( show FlowSet V Qr from moneyM c hm (fun i=>⟨ false,0,hP.badge i ⟩) ) hm.proper b hp he;
   obtain ⟨U',D,hU,hD,hr⟩:= Covers φ S A u P hc ht hV; refine ⟨ f,D,hf,fun i s=> κglyph c i hK.badge hf ( fun _=>billRent .. ) H,hD, ?_, fun s hs n=> hr s hs n |>.2.1 ⟩;
   have hUe : U'=voyage c Z:= Rake.perfect hU ( Boarding c (seedW_ok c) hZ (Fleet.fee hZ (moneyM c hm (fun i=> ⟨false,0,hP.badge i⟩))) ); have hΩ(s:Finset W)(hp:s.Nonempty)(n:ℕ): toZ Z s n=toZ U' s n:= by
       funext i; let v(t:ℝ):= (Z s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=v:= funext fun t=> by rw [ hUe, τv ]
       obtain HT:= ( hX s n i ).comp tendsto_exp_atTop; obtain HH:=hr s hp n|>.1.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique HT HH
   refine ⟨ ⟨h0,zeroZ hD.1⟩,⟨ toZ Z,toZ F, zeroZ hZ.1,zeroZ hF.1, fun s hs n=>?_,hpay, fun n s=>?_ ⟩ ⟩; · rw [ hΩ s hs n ]; obtain ⟨ h,hv,hu⟩:= hr s hs n; exact ⟨marketV h hv hu,h.2.2⟩
   let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let v i s n:= toZ F s n i; exact Filter.EventuallyEq.symm ( peaks (l:=l) (X:=a) (Y:=v) ( marked W ) Toy ( pointed _ (zeroZ hZ.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> Echo.quote hv hP hK hV.bulk hc hmenu hZ hF n s) s n ) -- Params order
end YM.MS.Tide
