import YM.FVA2.Full.Stated
import YM.WiderProfiles.Covers
/-!
WiderProfiles §F.1. Derivations extended from `YM/FVA2/Full/Stated.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
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
    {F:Finset W}{φ: FullBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}

set_option quotPrecheck false
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Qr"=> SeedsWF c φ A u P
local notation "φX"=> PortEntryF φ A ∘ u
lemma assemblyF_wide (hc:G.Simple)(hp: Clearance L x)(he: Vista.width L x)(hm:WidthW V P.η c)(ht: WMesh P ( info c ))(hv: Sparse l c)(b:Bool)(hV: TaylorOKF S φ A) : ∃ (Z:Terrify W I)(X:Rake.Dance G I W), CCOrb G P.η A.team x L Qa b Z ∧
  (∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur ( bury i s Z )) ∧ DOrd M P S u ( info c ) X ∧ Judge P c V Z ( toZ X ) L l ( Label.h ∘ u ) ∧ ∀ s:Finset W,s.Nonempty→∀ n,Verdict P ( Vane.charge ( Label.h ∘ u ) s ) 0 ( X s n ) := by
   obtain ⟨hK,hP,H,hmenu⟩:= billMenusF u (φ:=φ) (A:=A) hc; have heo : FlowSet V Qa:= moneyM c hm (fun i=>⟨ false,0,hK.badge i ⟩); let t:=A.team; obtain ⟨F,f,hF,hf,hT,h0,hpay⟩:= Ωgo ( P:=x ) hV.bulk heo hm.proper b hp he; obtain ⟨Z,X0,hZ,hZ',hX,h',hx⟩:= Ωgo (P:=x) hV.bulk ( show FlowSet V Qr from moneyM c hm (fun i=>⟨ false,0,hP.badge i ⟩) ) hm.proper b hp he;
   obtain ⟨U',D,hU,hD,hr⟩:= CoversF_wide φ S A u P hc ht hV; refine ⟨ f,D,hf,fun i s=> κglyph c i hK.badge hf ( fun _=>billRentF .. ) H,hD, ?_, fun s hs n=> hr s hs n |>.2.1 ⟩;
   have hUe : U'=voyage c Z:= Rake.perfect hU ( BoardingF c (seedW_okF c) hZ (Fleet.fee hZ (moneyM c hm (fun i=> ⟨false,0,hP.badge i⟩))) ); have hΩ(s:Finset W)(hp:s.Nonempty)(n:ℕ): toZ Z s n=toZ U' s n:= by
       funext i; let v(t:ℝ):= (Z s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=v:= funext fun t=> by rw [ hUe, τv ]
       obtain HT:= ( hX s n i ).comp tendsto_exp_atTop; obtain HH:=hr s hp n|>.1.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique HT HH
   refine ⟨ ⟨h0,zeroZ hD.1⟩,⟨ toZ Z,toZ F, zeroZ hZ.1,zeroZ hF.1, fun s hs n=>?_,hpay, fun n s=>?_ ⟩ ⟩; · rw [ hΩ s hs n ]; obtain ⟨ h,hv,hu⟩:= hr s hs n; exact ⟨marketV h hv hu,h.2.2⟩
   let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let v i s n:= toZ F s n i; exact Filter.EventuallyEq.symm ( peaks (l:=l) (X:=a) (Y:=v) ( marked W ) Toy ( pointed _ (zeroZ hZ.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> Echo.quote hv hP hK hV.bulk hc hmenu hZ hF n s) s n )
end YM.MS.Tide
end
