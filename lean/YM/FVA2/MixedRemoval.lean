import YM.FVA2.MixedInitial
import YM.MS.Tide.Coi
import YM.MS.Tide.Lion
import YM.MS.Tide.Stated
import YM.MS.Dial.Watch
import YM.MS.Dial.Signals
/-!
# Menus-coded source steps, extended to allow multi-rank bare `BookM`

These portions of `Tide` and `High` (see above imports from which individual
 wrappers and proofs are adapted/rebound) can't be applied as-is to exact
 calibration with lower raw-rank terms. This file only rebinds the Menus-dependent
 lemmas to the already present stronger formulation; no change to MS-data,
 adjusted score/physical ending prescriptions (except their binding to `BookM`),
 proofs of the momentum estimates, or geometric predicates. Keep analogous names with
 suffix M. `Uses`, `Rake.Geo`, etc. the same.
-/
set_option autoImplicit false
noncomputable section
-- adapted from Tide/Coi
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian Paint High Wind Rake Rake.Geo Vista Vane City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{t:Team}
    {F:Finset W}{φ: BookM B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
-- native input stencil
def ApplyMM (V: BookM B)(t:Team)(a:Land.Prescription B)(u:W→Label B): W→ Actor G:= fun i=> Menus.rentM V t ( a.fees ( u i|>.h ) (( u i ).item) )
set_option quotPrecheck false
local notation "Yr"=> ApplyMM φ A.team A u
local notation "Ur"=> ApplyMM φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Qr"=> SeedsWM c φ A u P
local notation "φX"=> PortEntryM φ A ∘ u
omit [LinearOrder W] in
lemma billMenusM (hc:G.Simple): ReadyP A.team Yr ∧ ReadyP A.team φX∧ Changes Yr Ur A.team ∧ ∀ w, Menu A.team ( (φX) w ) ( Yr w ):= by
   refine ⟨⟨ fun _=> billRentM ..,fun w x=> rentedM φ A.team x _ hc ⟩,⟨fun _=> decorM ..,fun w x=> Menus.lawM φ A.team x _ hc ⟩,fun w x=> rankVM ..,fun w=>?_⟩
   let X:= u w; let K:= A.fees X.h X.item; refine ⟨ ⟨ Menus.prim K, ⟨ (fun i y=> ( K i ).proof.actual y ),(fun i=> ⟨ _,( K i ).proof.ranks ⟩ ),fun i y=> ( K i ).proof.calm y,fun i=>( K i ).proof.polyn,fun _ _ h=>Bool.noConfusion h⟩,?_ ⟩ ⟩; intro y; change Menus.motto A.team K y= Menus.scoreM φ A.team K y - Menus.rentM φ A.team K y; rw [scoreM]; abel
lemma assemblyM (hc:G.Simple)(hp: Clearance L x)(he: Vista.width L x)(hm:WidthW V P.η c)(ht: Mesh P ( info c ))(hv: Sparse l c)(b:Bool)(hV: TaylorOKM S φ A) : ∃ (Z:Terrify W I)(X:Rake.Dance G I W), CCOrb G P.η A.team x L Qa b Z ∧
  (∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur ( bury i s Z )) ∧ DOrd M P S u ( info c ) X ∧ Judge P c V Z ( toZ X ) L l ( Label.h ∘ u ) ∧ ∀ s:Finset W,s.Nonempty→∀ n,Verdict P ( Vane.charge ( Label.h ∘ u ) s ) 0 ( X s n ) := by
   obtain ⟨hK,hP,H,hmenu⟩:= billMenusM u (φ:=φ) (A:=A) hc; have heo : FlowSet V Qa:= moneyM c hm (fun i=>⟨ false,0,hK.badge i ⟩); let t:=A.team; obtain ⟨F,f,hF,hf,hT,h0,hpay⟩:= Ωgo ( P:=x ) hV.bulk heo hm.proper b hp he; obtain ⟨Z,X0,hZ,hZ',hX,h',hx⟩:= Ωgo (P:=x) hV.bulk ( show FlowSet V Qr from moneyM c hm (fun i=>⟨ false,0,hP.badge i ⟩) ) hm.proper b hp he;
   obtain ⟨U',D,hU,hD,hr⟩:= CoversM φ S A u P hc ht hV; refine ⟨ f,D,hf,fun i s=> κglyph c i hK.badge hf ( fun _=>billRentM .. ) H,hD, ?_, fun s hs n=> hr s hs n |>.2.1 ⟩;
   have hUe : U'=voyage c Z:= Rake.perfect hU ( BoardingM c (seedW_okM c) hZ (Fleet.fee hZ (moneyM c hm (fun i=> ⟨false,0,hP.badge i⟩))) ); have hΩ(s:Finset W)(hp:s.Nonempty)(n:ℕ): toZ Z s n=toZ U' s n:= by
       funext i; let v(t:ℝ):= (Z s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=v:= funext fun t=> by rw [ hUe, τv ]
       obtain HT:= ( hX s n i ).comp tendsto_exp_atTop; obtain HH:=hr s hp n|>.1.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique HT HH
   refine ⟨ ⟨h0,zeroZ hD.1⟩,⟨ toZ Z,toZ F, zeroZ hZ.1,zeroZ hF.1, fun s hs n=>?_,hpay, fun n s=>?_ ⟩ ⟩; · rw [ hΩ s hs n ]; obtain ⟨ h,hv,hu⟩:= hr s hs n; exact ⟨marketV h hv hu,h.2.2⟩
   let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let v i s n:= toZ F s n i; exact Filter.EventuallyEq.symm ( peaks (l:=l) (X:=a) (Y:=v) ( marked W ) Toy ( pointed _ (zeroZ hZ.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> Echo.quote hv hP hK hV.bulk hc hmenu hZ hF n s) s n ) -- Params order
end YM.MS.Tide

-- adapted from Tide/Lion
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {I W:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: BookM B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I} {w:W→ℕ}
set_option quotPrecheck false
local notation "Yr"=> ApplyMM φ A.team A u
local notation "Ur"=> ApplyMM φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Cgx"=> lifted P c
local notation "g"=> (Label.h ∘ u)
variable (h:G.Simple)(hp:TaylorOKM S φ A)(he: Clearance L x)(hv: Vista.width L x)(hw: WidthW V P.η c)(hm: Mesh P ( info c ))(hP: NearPlan l P V L μ)
include h hp he hv hw hm hP
lemma CCPM (b:Bool): ∃ (Z:Terrify W I)(X:Rake.Dance G I W), ( Z ∅=0 ∧ Fleet.toZ X ∅=0 ∧ ∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur (bury i s Z)) ∧ DOrd M (frameF I μ) S u Cgx X ∧ (∀ s n,PeakT l P mildG (fare g P Z s n-toZ X s n)∧PeakT l P 0 ( Fleet.toZ X s n ))∧∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge g s ) 0 ( X s n ) := by
   have hs:= payTune c hm hP.vanish; obtain ⟨Ω,X,hQ,hX,hD,hK,hY⟩:= assemblyM u c h he hv hw hm hs b hp; obtain ⟨Z,Y,H,hJ,hV⟩:= CoversM φ S A u (frameF I μ) h (posed c hm) hp; refine ⟨ Ω,Y,⟨ hK.blanks.1,zeroZ hJ.1,hX ⟩,hJ, fun s n=>?_, fun s hs n=> hV s hs n |>.2.1 ⟩; obtain hh : fare g P ( toZ X )=toZ Y:= clockShape P Cgx u hP.dimm hJ ( by rw [ ← re_n ]; exact hD ) (fun s hs n=> hV s hs n|>.2.1.1 )
   refine ⟨ hh ▸ dealP c hK hP,?_ ⟩; by_cases hs:s.Nonempty; exact Verdict.economic _ _ (hV s hs n|>.2.1.2.2); rw [Finset.not_nonempty_iff_eq_empty.mp hs, zeroZ hJ.1]; exact PeakT.zero -- orientation ▸ may motive
end YM.MS.Tide

-- adapted from Tide/Stated
namespace YM.MS.Tide
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Lattice Land Frame Latch Job Heat Detect Book Convolve Program
open Native Wilsonian High Wind Rake Rake.Geo Vista Vane Port City Orbit Cog Orbit.LogReal
open Puff Engine SplitP Actors Dynamics Puff.Mom
open Fleet Swirl Swirl.Near SpaceOut Menus Echo
open scoped Topology ContDiff Interval
variable {W I:Type}{P:Geo I}{V:Visa I}{L:I→Side}{x: Faces I}{G:Gauge}{b:Bool} [LinearOrder W]
    {B:Local.Physical.Deck G}{M:Land.Booked B}{F:Finset W}{φ: BookM B}{A: Land.Prescription B}{S: MS_Data G M}{n:ℕ}{μ:ℝ}
    (u:W→Label B)(c:Berth ( W:=W ) ( I:=I )) {l: Filter I}
    {X:Rake.Dance G I W}{Z:Terrify W I}
set_option quotPrecheck false
local notation "Yr"=> ApplyMM φ A.team A u
local notation "Ur"=> ApplyMM φ ( Stripped A.team ) A u
local notation "g"=> (Label.h ∘ u)
open PeakT (ordZ)
variable (h:Profile P c) (hx:∀ i, P.η i=μ-P.θ i)
   (hu:Tendsto P.θ l atTop)(hp: Super l L P.θ)
include h hx hu hp
structure scalePhysicsM (P:Geo I)(M:Land.Booked B)(S:MS_Data G M)(μ:ℝ)(T':Land.Prescription B)(V:BookM B)(u:W→Label B)(c:Berth ( W:=W ) ( I:=I ))(x: Faces I)(L:I→Side)(b:Bool)(l:Filter I) (Z:Terrify W I)(Y:Rake.Dance G I W): Prop where
     native : ∀ i s,PhysicalSum G T'.team ( P.η i ) (dimT L i) b s ( fun w=> c w i ) ( x i ) ( ApplyMM V ( Stripped T'.team ) T' u ) (bury i s Z)
     empty : Z ∅=0
     scheme : DOrd M ( frameF I μ ) S u ( lifted P c ) Y
     huge : ∀ s:Finset W,s.Nonempty→∀ n,Verdict (frameF I μ) ( Vane.charge (Label.h ∘ u) s ) 0 ( Y s n ) -- `Verdict.economic` etc
     compares : ∀ s n, PeakT.twin l P mildG (fare ( Label.h ∘ u ) P Z s n) ( Fleet.toZ Y s n ) ∧ PeakT.twin l P mildG ( fare ( Label.h ∘ u ) P (ordZ Z) s n ) ( ordZ ( Fleet.toZ Y ) s n )
-- norm.
variable (hG:G.Simple) (hc:Clearance L x)(hw:Vista.width L x)(hm:Mesh P ( info c ))
include hG hc hw hm
lemma calledM (hZ:TaylorOKM S φ A)(b:Bool): ∃ Z Y,scalePhysicsM P M S μ A φ u c x L b l Z Y:= by
    obtain ⟨V,hV,hV'⟩:= qualifies c h hx hu hp; obtain ⟨Z,Y,⟨hn,hU,hN⟩,hz,ht,hQ⟩:= CCPM u c hG hZ hc hw hV hm hV' b
    refine ⟨Z,Y,hN,hn,hz,hQ, fun s n=>⟨(ht s n).symm,?_⟩⟩; rw [← funext (fun i=> PeakT.ν_norm g ( s:=s ) ( P:=P ) ( n:=n ) i Z) ]; exact PeakT.projection ht s n
end YM.MS.Tide

-- adapted from Dial/Watch
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet -- order
open Lattice
open scoped Topology ContDiff
open Vane PeakT Program Menus Swirl Swirl.Near
open Native Wilsonian
variable {W I:Type} {μ:ℝ}{n:ℕ}[LinearOrder W] {l:Filter I}
variable {G:Gauge}{B: Deck G}{M:Booked B}(S:MS_Data G M)(φ: BookM B)(p:W→Label B)
   (T:Trial I W){A:Prescription B}
local notation "sV"=> p
local notation "gj"=> (Label.h ∘ p)
variable {V:Terrify W I}
def CutoffM (v:ℝ)(b:Bool)(A:Prescription B)(V:Terrify W I) : Prop:= ∀ i s, PhysicalSum G A.team ( v-T.profile.θ i) ( dimT T.side i ) b s (fun w=> T.off w i) ( T.head i ) ( ApplyMM φ (Stripped A.team) A p ) (bury i s V)
structure coherentM (M:Booked B)(S:MS_Data G M)(φ: BookM B)(p: W→Label B)(T:Trial I W)(v:ℝ)(b:Bool)(A:Prescription B)(l:Filter I)(V:Terrify W I): Prop where
    init: V ∅=0
    cost: CutoffM φ p T v b A V
    ready (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile V s n ) ( fun i=> book S p v ( testP T i ) s n )
    bouquet (s:Finset W)(n:ℕ): twin l T.profile mildG ( fare ( Label.h ∘ p ) T.profile ( ordZ V ) s n ) ( fun i=> tour S p v ( testP T i ) s n )
lemma check_tM (h:TaylorOKM S φ A)(U:Uses T l μ)(hp:G.Simple)(b:Bool): ∃ V:Terrify W I,coherentM M S φ p T μ b A l V:= by
    obtain ⟨ Z,Y,hY⟩:= Tide.calledM p T.off U.total U.reality U.upright U.super hp U.clear U.wind U.knit h b; have hv:=posed (μ:=μ) T.off U.knit; have hh(s:Finset W)(n:ℕ): Fleet.toZ Y s n=(fun i=> book S p μ ( testP T i ) s n):= funext fun i=> Point_t S p μ hv hY.scheme i s n;
    refine ⟨Z,hY.empty,fun i s=>?_,fun i u=> hh i u ▸ ( hY.compares i u ).1,fun i t=>?_ ⟩; exact U.reality i ▸ hY.native i s; rw [ ← show ordZ ( Fleet.toZ Y ) i t=(fun s=> tour S p μ ( testP T s ) i t) from funext fun s=> shape_f S p μ hv hY.scheme s i t ]; exact ( hY.compares i t|>.2 ) -- parser
variable {b:Bool}
variable [Fintype W] {x:W→QP}
lemma profile_tM (h:coherentM M S φ p T μ b A l V)(ht:Uses T l μ)(he:Injective x)(hc:Tendsto (testP T) l (𝓝 x)) (s:Finset W)(n:ℕ): Tendsto ( fare gj T.profile V s n ) l (𝓝 ( book S p μ x s n )) ∧ Tendsto ( fare gj T.profile (ordZ V) s n ) l (𝓝 ( tour S p μ x s n )):= ⟨agrees T (h.ready s n) ht.upright (( contin S p x he s n μ|>.2 ).tendsto.comp hc), agrees T ( h.bouquet s n ) ht.upright (( contin S p x he s n μ|>.1).tendsto.comp hc)⟩
end YM.MS.Dial

-- adapted from Dial/Signals
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real High
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Fleet
open Vane PeakT Program Menus Swirl Swirl.Near Native Wilsonian
open Puff Engine SplitP Actors Puff.Mom
open scoped Topology ContDiff
variable {W I:Type}{G:Gauge}{B:Deck G}[LinearOrder W] {F:Finset W}
   (φ: BookM B)(L: W→Label B)(P:Trial I W){O:Booked B}{μ:ℝ} {b:Bool} {A:Prescription B} {V H:Terrify W I}
lemma measureM (F:Finset W) (hp: CutoffM φ L P μ b A V)(hx: CutoffM φ L P μ b A H) (i:I): bury i F V=bury i F H:= classicalμ ( τ_nil .. ) (hp i F ) ( hx i F ) -- args
lemma separateM (hp:CutoffM φ L P μ b A V)(hx: CutoffM φ L P μ b A H)(hv:V ∅=0)(he:H ∅=0): V=H:= by
   let t (v:Terrify W I)(i:I): Finset W→ T ℂ := fun s k=> v s k i; funext s n i; have hp1(y:Terrify W I)(hy:y ∅=0): Happy (marked W) (t y i):= Tide.pointed _ hy i;
   have hx1(y:Terrify W I)(x:y ∅=0): Puff.Log.Meter Trunk ( marked W ) (fun s=> bury i s y )= t y i:= Puff.Log.recheck _ _ _ (show t y i∈ allIndex _ _ from fun i _=> fun n _=> Submodule.mem_top ) ( hp1 y x );
   have hV := hx1 V hv; rw [funext (fun F=> measureM φ L P F hp hx i), hx1 H he] at hV; exact ( congr_fun ( congr_fun hV s ) n ).symm
-- universes. genuine Θ fixed.H no assumptions.Arch + separateM assures meaningful.Main.
end YM.MS.Dial
