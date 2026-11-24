import YM.FVAAlt2.Plus.Fleet
import YM.FVAAlt2.Plus.Native
import YM.MS.Tide.Stated

/-! RichBook generalization. Adapted from `MS/Tide/Coi`, `MS/Tide/Lion`, `MS/Tide/Stated`. -/

set_option autoImplicit false
noncomputable section

-- Tide/Coi
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian Paint High Wind Rake Rake.Geo Vista Vane City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{t:Team}
    {F:Finset W}{φ: RichBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
-- native input stencil
def ApplyMPl (V: RichBook B)(t:Team)(a:Land.Prescription B)(u:W→Label B): W→ Actor G:= fun i=> Menus.rentPl V t ( a.fees ( u i|>.h ) (( u i ).item) )
set_option quotPrecheck false
local notation "Yr"=> ApplyMPl φ A.team A u
local notation "Ur"=> ApplyMPl φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Qr"=> SeedsWPl c φ A u P
local notation "φX"=> PortEntryPl φ A ∘ u
omit [LinearOrder W] in
lemma billMenusPl (hc:G.Simple): ReadyP A.team Yr ∧ ReadyP A.team φX∧ Changes Yr Ur A.team ∧ ∀ w, Menu A.team ( (φX) w ) ( Yr w ):= by
   refine ⟨⟨ fun _=> billRentPl ..,fun w x=> rentedPl φ A.team x _ hc ⟩,⟨fun _=> decorPl ..,fun w x=> Menus.lawPl φ A.team x _ hc ⟩,fun w x=> rankVPl ..,fun w=>?_⟩
   let X:= u w; let K:= A.fees X.h X.item; refine ⟨ ⟨ Menus.prim K, ⟨ (fun i y=> ( K i ).proof.actual y ),(fun i=> ⟨ _,( K i ).proof.ranks ⟩ ),fun i y=> ( K i ).proof.calm y,fun i=>( K i ).proof.polyn,fun _ _ h=>Bool.noConfusion h⟩,?_ ⟩ ⟩; intro y; change Menus.motto A.team K y= Menus.scorePl φ A.team K y - Menus.rentPl φ A.team K y; rw [scorePl]; abel
lemma assemblyPl (hc:G.Simple)(hp: Clearance L x)(he: Vista.width L x)(hm:WidthW V P.η c)(ht: Mesh P ( info c ))(hv: Sparse l c)(b:Bool)(hV: TaylorOKPl S φ A) : ∃ (Z:Terrify W I)(X:Rake.Dance G I W), CCOrb G P.η A.team x L Qa b Z ∧
  (∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur ( bury i s Z )) ∧ DOrd M P S u ( info c ) X ∧ Judge P c V Z ( toZ X ) L l ( Label.h ∘ u ) ∧ ∀ s:Finset W,s.Nonempty→∀ n,Verdict P ( Vane.charge ( Label.h ∘ u ) s ) 0 ( X s n ) := by
   obtain ⟨hK,hP,H,hmenu⟩:= billMenusPl u (φ:=φ) (A:=A) hc; have heo : FlowSet V Qa:= moneyM c hm (fun i=>⟨ false,0,hK.badge i ⟩); let t:=A.team; obtain ⟨F,f,hF,hf,hT,h0,hpay⟩:= Ωgo ( P:=x ) hV.bulk heo hm.proper b hp he; obtain ⟨Z,X0,hZ,hZ',hX,h',hx⟩:= Ωgo (P:=x) hV.bulk ( show FlowSet V Qr from moneyM c hm (fun i=>⟨ false,0,hP.badge i ⟩) ) hm.proper b hp he;
   obtain ⟨U',D,hU,hD,hr⟩:= CoversPl φ S A u P hc ht hV; refine ⟨ f,D,hf,fun i s=> κglyph c i hK.badge hf ( fun _=>billRentPl .. ) H,hD, ?_, fun s hs n=> hr s hs n |>.2.1 ⟩;
   have hUe : U'=voyage c Z:= Rake.perfect hU ( BoardingPl c (seedW_okPl c) hZ (Fleet.fee hZ (moneyM c hm (fun i=> ⟨false,0,hP.badge i⟩))) ); have hΩ(s:Finset W)(hp:s.Nonempty)(n:ℕ): toZ Z s n=toZ U' s n:= by
       funext i; let v(t:ℝ):= (Z s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=v:= funext fun t=> by rw [ hUe, τv ]
       obtain HT:= ( hX s n i ).comp tendsto_exp_atTop; obtain HH:=hr s hp n|>.1.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique HT HH
   refine ⟨ ⟨h0,zeroZ hD.1⟩,⟨ toZ Z,toZ F, zeroZ hZ.1,zeroZ hF.1, fun s hs n=>?_,hpay, fun n s=>?_ ⟩ ⟩; · rw [ hΩ s hs n ]; obtain ⟨ h,hv,hu⟩:= hr s hs n; exact ⟨marketV h hv hu,h.2.2⟩
   let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let v i s n:= toZ F s n i; exact Filter.EventuallyEq.symm ( peaks (l:=l) (X:=a) (Y:=v) ( marked W ) Toy ( pointed _ (zeroZ hZ.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> Echo.quote hv hP hK hV.bulk hc hmenu hZ hF n s) s n ) -- Params order
end YM.MS.Tide

-- Tide/Lion
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {I W:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: RichBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I} {w:W→ℕ}
set_option quotPrecheck false
local notation "Yr"=> ApplyMPl φ A.team A u
local notation "Ur"=> ApplyMPl φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
-- P.roots= spacing^{-1}.
local notation "Cgx"=> lifted P c
local notation "g"=> (Label.h ∘ u)
variable (h:G.Simple)(hp:TaylorOKPl S φ A)(he: Clearance L x)(hv: Vista.width L x)(hw: WidthW V P.η c)(hm: Mesh P ( info c ))(hP: NearPlan l P V L μ)
include h hp he hv hw hm hP
lemma CCPPl (b:Bool): ∃ (Z:Terrify W I)(X:Rake.Dance G I W), ( Z ∅=0 ∧ Fleet.toZ X ∅=0 ∧ ∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur (bury i s Z)) ∧ DOrd M (frameF I μ) S u Cgx X ∧ (∀ s n,PeakT l P mildG (fare g P Z s n-toZ X s n)∧PeakT l P 0 ( Fleet.toZ X s n ))∧∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge g s ) 0 ( X s n ) := by
   have hs:= payTune c hm hP.vanish; obtain ⟨Ω,X,hQ,hX,hD,hK,hY⟩:= assemblyPl u c h he hv hw hm hs b hp; obtain ⟨Z,Y,H,hJ,hV⟩:= CoversPl φ S A u (frameF I μ) h (posed c hm) hp; refine ⟨ Ω,Y,⟨ hK.blanks.1,zeroZ hJ.1,hX ⟩,hJ, fun s n=>?_, fun s hs n=> hV s hs n |>.2.1 ⟩; obtain hh : fare g P ( toZ X )=toZ Y:= clockShape P Cgx u hP.dimm hJ ( by rw [ ← re_n ]; exact hD ) (fun s hs n=> hV s hs n|>.2.1.1 )
   refine ⟨ hh ▸ dealP c hK hP,?_ ⟩; by_cases hs:s.Nonempty; exact Verdict.economic _ _ (hV s hs n|>.2.1.2.2); rw [Finset.not_nonempty_iff_eq_empty.mp hs, zeroZ hJ.1]; exact PeakT.zero -- orientation ▸ may motive
end YM.MS.Tide

-- Tide/Stated
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: RichBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
set_option quotPrecheck false
local notation "Yr"=> ApplyMPl φ A.team A u
local notation "Ur"=> ApplyMPl φ ( Stripped A.team ) A u
local notation "g"=> (Label.h ∘ u)
open PeakT (ordZ)
-- hypotheses.No bank, specify origin-bounded positions; any cardinal W.
variable (h:Profile P c) (hx:∀ i, P.η i=μ-P.θ i)
   (hu:Tendsto P.θ l atTop)(hp: Super l L P.θ)
include h hx hu hp
structure scalePhysicsPl (P:Geo I)(M:Land.Booked B)(S:MS_Data G M)(μ:ℝ)(T':Land.Prescription B)(V:RichBook B)(u:W→Label B)(c:Berth ( W:=W ) ( I:=I ))(x: Faces I)(L:I→Side)(b:Bool)(l:Filter I) (Z:Terrify W I)(Y:Rake.Dance G I W): Prop where
     native : ∀ i s,PhysicalSum G T'.team ( P.η i ) (dimT L i) b s ( fun w=> c w i ) ( x i ) ( ApplyMPl V ( Stripped T'.team ) T' u ) (bury i s Z)
     empty : Z ∅=0
     scheme : DOrd M ( frameF I μ ) S u ( lifted P c ) Y
     huge : ∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge (Label.h ∘ u) s ) 0 ( Y s n ) -- `Verdict.economic` etc
     compares : ∀ s n, PeakT.twin l P mildG (fare ( Label.h ∘ u ) P Z s n) ( Fleet.toZ Y s n ) ∧ PeakT.twin l P mildG ( fare ( Label.h ∘ u ) P (ordZ Z) s n ) ( ordZ ( Fleet.toZ Y ) s n )
-- norm.
variable (hG:G.Simple) (hc:Clearance L x)(hw:Vista.width L x)(hm:Mesh P ( info c ))
include hG hc hw hm
lemma calledPl (hZ:TaylorOKPl S φ A)(b:Bool): ∃ Z Y,scalePhysicsPl P M S μ A φ u c x L b l Z Y:= by
    obtain ⟨V,hV,hV'⟩:= qualifies c h hx hu hp; obtain ⟨Z,Y,⟨hn,hU,hN⟩,hz,ht,hQ⟩:= CCPPl u c hG hZ hc hw hV hm hV' b
    refine ⟨Z,Y,hN,hn,hz,hQ, fun s n=>⟨(ht s n).symm,?_⟩⟩; rw [← funext (fun i=> PeakT.ν_norm g ( s:=s ) ( P:=P ) ( n:=n ) i Z) ]; exact PeakT.projection ht s n
omit hG hc hw hm h hx hu hp
-- one S.G.witness applies to every.
theorem removePl (ϕ:RichBook B)(S:MS_Data G M)(h:G.Simple) : ∃ A:Land.Prescription B, TaylorOKPl S ϕ A ∧ ∀ (I W:Type)(_ :LinearOrder W) (P:Geo I) (L:I→Side)(x:Faces I)(b:Bool)(l:Filter I) (v:W→Label B)(c:Berth ( W:=W ) ( I:=I ))(μ:ℝ), Profile P c→ (∀ i,P.η i=μ-P.θ i)→ Tendsto P.θ l atTop→ Super l L P.θ→ Clearance L x→Vista.width L x→Mesh P ( info c )→ ∃ Z Y,scalePhysicsPl P M S μ A ϕ v c x L b l Z Y := by
    obtain ⟨A,hA⟩:= High_stopsPl h S ϕ; refine ⟨ A,hA,fun I W _ P L x b l v c μ hK hS hp hF hN hY hm=>?_⟩; exact calledPl v c hK hS hp hF h hN hY hm hA b
end YM.MS.Tide
