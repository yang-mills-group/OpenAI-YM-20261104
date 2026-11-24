import YM.MS.Tide.Coi
import YM.MS.Tide.Lion
import YM.MS.Tide.Stated
import YM.MS.Dial.Watch
import YM.MS.Dial.Signals
import YM.FVA2.Full.Source
/-! FVA_2 addition: `FullBook` with W-type shifts.
Module Stated. Relevant proofs extended from `LitBook` in
YM.MS.Tide.Coi
YM.MS.Tide.Lion
YM.MS.Tide.Stated
YM.MS.Dial.Watch
YM.MS.Dial.Signals.
Main stencils/rank/affordability modified in `YM.FVA2.Full.Glyph`.
Names with `F` suffix are generally for the adjusted versions. For example
now prove the regulator-removal comparison with `scalePhysicsF` & `coherentF`.
Use `check_tF` etc. to apply the comparison with a more specific tuning
than just those produced in `removeF` and `LPT_to_MSF` here.
No changes to `PhysicalSum`, BV prescription or `MS_Data`. -/
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

def ApplyMF (V: FullBook B)(t:Team)(a:Land.Prescription B)(u:W→Label B): W→ Actor G:= fun i=> Menus.rentF V t ( a.fees ( u i|>.h ) (( u i ).item) )
set_option quotPrecheck false
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Qr"=> SeedsWF c φ A u P
local notation "φX"=> PortEntryF φ A ∘ u
omit [LinearOrder W] in
lemma billMenusF (hc:G.Simple): ReadyP A.team Yr ∧ ReadyP A.team φX∧ Changes Yr Ur A.team ∧ ∀ w, Menu A.team ( (φX) w ) ( Yr w ):= by
   refine ⟨⟨ fun _=> billRentF ..,fun w x=> rentedF φ A.team x _ hc ⟩,⟨fun _=> decorF ..,fun w x=> Menus.lawF φ A.team x _ hc ⟩,fun w x=> rankVF ..,fun w=>?_⟩
   let X:= u w; let K:= A.fees X.h X.item; refine ⟨ ⟨ Menus.prim K, ⟨ (fun i y=> ( K i ).proof.actual y ),(fun i=> ⟨ _,( K i ).proof.ranks ⟩ ),fun i y=> ( K i ).proof.calm y,fun i=>( K i ).proof.polyn,fun _ _ h=>Bool.noConfusion h⟩,?_ ⟩ ⟩; intro y; change Menus.motto A.team K y= Menus.scoreF φ A.team K y - Menus.rentF φ A.team K y; rw [scoreF]; abel
lemma assemblyF (hc:G.Simple)(hp: Clearance L x)(he: Vista.width L x)(hm:WidthW V P.η c)(ht: Mesh P ( info c ))(hv: Sparse l c)(b:Bool)(hV: TaylorOKF S φ A) : ∃ (Z:Terrify W I)(X:Rake.Dance G I W), CCOrb G P.η A.team x L Qa b Z ∧
  (∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur ( bury i s Z )) ∧ DOrd M P S u ( info c ) X ∧ Judge P c V Z ( toZ X ) L l ( Label.h ∘ u ) ∧ ∀ s:Finset W,s.Nonempty→∀ n,Verdict P ( Vane.charge ( Label.h ∘ u ) s ) 0 ( X s n ) := by
   obtain ⟨hK,hP,H,hmenu⟩:= billMenusF u (φ:=φ) (A:=A) hc; have heo : FlowSet V Qa:= moneyM c hm (fun i=>⟨ false,0,hK.badge i ⟩); let t:=A.team; obtain ⟨F,f,hF,hf,hT,h0,hpay⟩:= Ωgo ( P:=x ) hV.bulk heo hm.proper b hp he; obtain ⟨Z,X0,hZ,hZ',hX,h',hx⟩:= Ωgo (P:=x) hV.bulk ( show FlowSet V Qr from moneyM c hm (fun i=>⟨ false,0,hP.badge i ⟩) ) hm.proper b hp he;
   obtain ⟨U',D,hU,hD,hr⟩:= CoversF φ S A u P hc ht hV; refine ⟨ f,D,hf,fun i s=> κglyph c i hK.badge hf ( fun _=>billRentF .. ) H,hD, ?_, fun s hs n=> hr s hs n |>.2.1 ⟩;
   have hUe : U'=voyage c Z:= Rake.perfect hU ( BoardingF c (seedW_okF c) hZ (Fleet.fee hZ (moneyM c hm (fun i=> ⟨false,0,hP.badge i⟩))) ); have hΩ(s:Finset W)(hp:s.Nonempty)(n:ℕ): toZ Z s n=toZ U' s n:= by
       funext i; let v(t:ℝ):= (Z s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=v:= funext fun t=> by rw [ hUe, τv ]
       obtain HT:= ( hX s n i ).comp tendsto_exp_atTop; obtain HH:=hr s hp n|>.1.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique HT HH
   refine ⟨ ⟨h0,zeroZ hD.1⟩,⟨ toZ Z,toZ F, zeroZ hZ.1,zeroZ hF.1, fun s hs n=>?_,hpay, fun n s=>?_ ⟩ ⟩; · rw [ hΩ s hs n ]; obtain ⟨ h,hv,hu⟩:= hr s hs n; exact ⟨marketV h hv hu,h.2.2⟩
   let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let v i s n:= toZ F s n i; exact Filter.EventuallyEq.symm ( peaks (l:=l) (X:=a) (Y:=v) ( marked W ) Toy ( pointed _ (zeroZ hZ.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> Echo.quote hv hP hK hV.bulk hc hmenu hZ hF n s) s n )
end YM.MS.Tide
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {I W:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: FullBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I} {w:W→ℕ}
set_option quotPrecheck false
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Cgx"=> lifted P c
local notation "g"=> (Label.h ∘ u)
variable (h:G.Simple)(hp:TaylorOKF S φ A)(he: Clearance L x)(hv: Vista.width L x)(hw: WidthW V P.η c)(hm: Mesh P ( info c ))(hP: NearPlan l P V L μ)
include h hp he hv hw hm hP
lemma CCPF (b:Bool): ∃ (Z:Terrify W I)(X:Rake.Dance G I W), ( Z ∅=0 ∧ Fleet.toZ X ∅=0 ∧ ∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur (bury i s Z)) ∧ DOrd M (frameF I μ) S u Cgx X ∧ (∀ s n,PeakT l P mildG (fare g P Z s n-toZ X s n)∧PeakT l P 0 ( Fleet.toZ X s n ))∧∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge g s ) 0 ( X s n ) := by
   have hs:= payTune c hm hP.vanish; obtain ⟨Ω,X,hQ,hX,hD,hK,hY⟩:= assemblyF u c h he hv hw hm hs b hp; obtain ⟨Z,Y,H,hJ,hV⟩:= CoversF φ S A u (frameF I μ) h (posed c hm) hp; refine ⟨ Ω,Y,⟨ hK.blanks.1,zeroZ hJ.1,hX ⟩,hJ, fun s n=>?_, fun s hs n=> hV s hs n |>.2.1 ⟩; obtain hh : fare g P ( toZ X )=toZ Y:= clockShape P Cgx u hP.dimm hJ ( by rw [ ← re_n ]; exact hD ) (fun s hs n=> hV s hs n|>.2.1.1 )
   refine ⟨ hh ▸ dealP c hK hP,?_ ⟩; by_cases hs:s.Nonempty; exact Verdict.economic _ _ (hV s hs n|>.2.1.2.2); rw [Finset.not_nonempty_iff_eq_empty.mp hs, zeroZ hJ.1]; exact PeakT.zero
end YM.MS.Tide
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: FullBook B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
set_option quotPrecheck false
local notation "Yr"=> ApplyMF φ A.team A u
local notation "Ur"=> ApplyMF φ ( Stripped A.team ) A u
local notation "g"=> (Label.h ∘ u)
open PeakT (ordZ)
variable (h:Profile P c) (hx:∀ i, P.η i=μ-P.θ i)
   (hu:Tendsto P.θ l atTop)(hp: Super l L P.θ)
include h hx hu hp

structure scalePhysicsF (P:Geo I)(M:Land.Booked B)(S:MS_Data G M)
      (μ:ℝ)(T':Land.Prescription B)(V:FullBook B)(u:W→Label B)
      (c:Berth ( W:=W ) ( I:=I ))(x: Faces I)
      (L:I→Side)(b:Bool)(l:Filter I)
      (Z:Terrify W I)(Y:Rake.Dance G I W): Prop where
     native : ∀ i s,PhysicalSum G T'.team ( P.η i ) (dimT L i) b s ( fun w=> c w i ) ( x i ) ( ApplyMF V ( Stripped T'.team ) T' u ) (bury i s Z)
     empty : Z ∅=0
     scheme : DOrd M ( frameF I μ ) S u ( lifted P c ) Y
     huge : ∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge (Label.h ∘ u) s ) 0 ( Y s n )
     compares : ∀ s n, PeakT.twin l P mildG (fare ( Label.h ∘ u ) P Z s n) ( Fleet.toZ Y s n ) ∧ PeakT.twin l P mildG ( fare ( Label.h ∘ u ) P (ordZ Z) s n ) ( ordZ ( Fleet.toZ Y ) s n )

variable (hG:G.Simple) (hc:Clearance L x)(hw:Vista.width L x)(hm:Mesh P ( info c ))
include hG hc hw hm
lemma calledF (hZ:TaylorOKF S φ A)(b:Bool): ∃ Z Y,scalePhysicsF P M S μ A φ u c x L b l Z Y:= by
    obtain ⟨V,hV,hV'⟩:= qualifies c h hx hu hp; obtain ⟨Z,Y,⟨hn,hU,hN⟩,hz,ht,hQ⟩:= CCPF u c hG hZ hc hw hV hm hV' b
    refine ⟨Z,Y,hN,hn,hz,hQ, fun s n=>⟨(ht s n).symm,?_⟩⟩; rw [← funext (fun i=> PeakT.ν_norm g ( s:=s ) ( P:=P ) ( n:=n ) i Z) ]; exact PeakT.projection ht s n
omit hG hc hw hm h hx hu hp

theorem removeF (ϕ:FullBook B)(S:MS_Data G M)(h:G.Simple)
      : ∃ A:Land.Prescription B, TaylorOKF S ϕ A ∧
      ∀ (I W:Type)(_ :LinearOrder W) (P:Geo I) (L:I→Side)
      (x:Faces I)(b:Bool)(l:Filter I) (v:W→Label B)
      (c:Berth ( W:=W ) ( I:=I ))(μ:ℝ),
      Profile P c→ (∀ i,P.η i=μ-P.θ i)→
      Tendsto P.θ l atTop→ Super l L P.θ→ Clearance L x→Vista.width L x→Mesh P ( info c )→
      ∃ Z Y,scalePhysicsF P M S μ A ϕ v c x L b l Z Y := by
    obtain ⟨A,hA⟩:= High_stopsF h S ϕ; refine ⟨ A,hA,fun I W _ P L x b l v c μ hK hS hp hF hN hY hm=>?_⟩; exact calledF v c hK hS hp hF h hN hY hm hA b
end YM.MS.Tide
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet
open Lattice
open scoped Topology ContDiff
open Vane PeakT Program Menus Swirl Swirl.Near
open Native Wilsonian
variable {W I:Type} {μ:ℝ}{n:ℕ}[LinearOrder W] {l:Filter I}
variable {G:Gauge}{B: Deck G}{M:Booked B}(S:MS_Data G M)(φ: FullBook B)(p:W→Label B)
   (T:Trial I W){A:Prescription B}
local notation "sV"=> p
local notation "gj"=> (Label.h ∘ p)
variable {V:Terrify W I}
def CutoffF (v:ℝ)(b:Bool)(A:Prescription B)(V:Terrify W I) : Prop:= ∀ i s,
      PhysicalSum G A.team ( v-T.profile.θ i) ( dimT T.side i ) b s (fun w=> T.off w i) ( T.head i )
        ( ApplyMF φ (Stripped A.team) A p ) (bury i s V)
structure coherentF (M:Booked B)(S:MS_Data G M)(φ: FullBook B)(p: W→Label B)
      (T:Trial I W)(v:ℝ)(b:Bool)(A:Prescription B)(l:Filter I)(V:Terrify W I): Prop where
    init: V ∅=0
    cost: CutoffF φ p T v b A V
    ready (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile V s n ) ( fun i=> book S p v ( testP T i ) s n )
    bouquet (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile ( ordZ V ) s n ) ( fun i=> tour S p v ( testP T i ) s n )
lemma check_tF (h:TaylorOKF S φ A)(U:Uses T l μ)(hp:G.Simple)(b:Bool): ∃ V:Terrify W I,coherentF M S φ p T μ b A l V:= by
    obtain ⟨ Z,Y,hY⟩:= Tide.calledF p T.off U.total U.reality U.upright U.super hp U.clear U.wind U.knit h b; have hv:=posed (μ:=μ) T.off U.knit; have hh(s:Finset W)(n:ℕ): Fleet.toZ Y s n=(fun i=> book S p μ ( testP T i ) s n):= funext fun i=> Point_t S p μ hv hY.scheme i s n;
    refine ⟨Z,hY.empty,fun i s=>?_,fun i u=> hh i u ▸ ( hY.compares i u ).1,fun i t=>?_ ⟩; exact U.reality i ▸ hY.native i s; rw [ ← show ordZ ( Fleet.toZ Y ) i t=(fun s=> tour S p μ ( testP T s ) i t) from funext fun s=> shape_f S p μ hv hY.scheme s i t ]; exact ( hY.compares i t|>.2 )
variable {b:Bool}
variable [Fintype W] {x:W→QP}
lemma profile_tF (h:coherentF M S φ p T μ b A l V)(ht:Uses T l μ)(he:Injective x)(hc:Tendsto (testP T) l (𝓝 x)) (s:Finset W)(n:ℕ): Tendsto ( fare gj T.profile V s n ) l (𝓝 ( book S p μ x s n )) ∧ Tendsto ( fare gj T.profile (ordZ V) s n ) l (𝓝 ( tour S p μ x s n )):= ⟨agrees T (h.ready s n) ht.upright (( contin S p x he s n μ|>.2 ).tendsto.comp hc), agrees T ( h.bouquet s n ) ht.upright (( contin S p x he s n μ|>.1).tendsto.comp hc)⟩
end YM.MS.Dial
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet
open Vane PeakT Program Menus Swirl Swirl.Near Native Wilsonian
open Puff Engine SplitP Actors Puff.Mom
open scoped Topology ContDiff
variable {W I:Type}{G:Gauge}{B:Deck G}[LinearOrder W] {F:Finset W}
   (φ: FullBook B)(L: W→Label B)(P:Trial I W){O:Booked B}{μ:ℝ} {b:Bool} {A:Prescription B} {V H:Terrify W I}
lemma measureF (F:Finset W) (hp: CutoffF φ L P μ b A V)(hx: CutoffF φ L P μ b A H) (i:I): bury i F V=bury i F H:= classicalμ ( τ_nil .. ) (hp i F ) ( hx i F )
lemma separateF (hp:CutoffF φ L P μ b A V)(hx: CutoffF φ L P μ b A H)(hv:V ∅=0)(he:H ∅=0): V=H:= by
   let t (v:Terrify W I)(i:I): Finset W→ T ℂ := fun s k=> v s k i; funext s n i; have hp1(y:Terrify W I)(hy:y ∅=0): Happy (marked W) (t y i):= Tide.pointed _ hy i;
   have hx1(y:Terrify W I)(x:y ∅=0): Puff.Log.Meter Trunk ( marked W ) (fun s=> bury i s y )= t y i:= Puff.Log.recheck _ _ _ (show t y i∈ allIndex _ _ from fun i _=> fun n _=> Submodule.mem_top ) ( hp1 y x );
   have hV := hx1 V hv; rw [funext (fun F=> measureF φ L P F hp hx i), hx1 H he] at hV; exact ( congr_fun ( congr_fun hV s ) n ).symm

omit [LinearOrder W]
theorem LPT_to_MSF {S:Gauge}{D:Deck S}{A:Booked D}
      (L:FullBook D)(F: MS_Data S A)(h:S.Simple)
      : ∃ Ξ: Prescription D, TaylorOKF F L Ξ ∧
      ∀ (W I:Type) (_:LinearOrder W)(P:Trial I W) (l:Filter I)
      (μ:ℝ)(u:W→Label D)(b:Bool), Uses P l μ →
       ∃! V:Terrify W I,coherentF A F L u P μ b Ξ l V:= by
   obtain ⟨Ξ,H⟩:= High_stopsF h F L; refine ⟨Ξ,H,fun W I _ P l μ u b hp=>?_⟩; obtain ⟨V,hV⟩:= check_tF F L u P H hp h b; exact ⟨V,hV, fun y hy=> separateF _ _ _ hy.cost hV.cost hy.init hV.init⟩
end YM.MS.Dial
end
