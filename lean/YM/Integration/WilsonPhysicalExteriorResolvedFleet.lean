import YM.Integration.WilsonPhysicalExteriorUVComparison
import YM.FVAAlt2.Plus.Remove

/-! The true rich finite-regulator book, including its original local marks
and actual periodic normalized signed multi-operator sums. The separated
inner and far operators are not confined to a common compact set. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorResolvedFleet
open Set Function Filter Finset Metric MeasureTheory Real
open YM.MS
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve City Vane Land Menus Local.Physical
open WilsonPhysicalExteriorUVStory
open scoped Topology ContDiff Interval Classical

section
variable {I W : Type} [LinearOrder W] {G:Gauge} {B:Deck G} {O:Booked B}
    {x:Position W I}
theorem covers (V:RichBook B) (M:MS_Data G O) (T:Prescription B) (u:W→Label B) (P:Geo I)
    (hg:G.Simple) (hx:Resolved P x) (ht:TaylorOKPl M V T) :
    ∃ U D, LOrdPl V P T u x U ∧ DOrd O P M u x D ∧
      ∀ s:Finset W,s.Nonempty→∀ k:ℕ,let n:=charge (Label.h∘u) s
        Verdict P n 0 (U s k) ∧ Verdict P n 0 (D s k) ∧ Verdict P n eps_gain (U s k-D s k) := by
  have L : WilsonPhysicalExteriorResolved.Source (constantP G I (LowP G)) (constantP G I (PlanetL G))
      P x true (initials P T) (rowKPl V P T ∘ u) (Label.h ∘ u) :=
    ⟨hx,Geo.masterL ..,fun i _=>tagL P T i,fun i k=>tagXPl V P T (u i) k,
        fun i=>lightLPl V P T hg (u i)⟩
  have D : WilsonPhysicalExteriorResolved.Source (constantP G I (PlanetD G)) (constantP G I (PlanetD G))
      P x false (approach P M) (rowM P M ∘ u) (Label.h ∘ u) :=
    ⟨hx,Geo.masterD ..,fun i _=>tagD P M i,fun i k=>tagF P M (u i) k,
        fun i=>VeniceD P M (u i)⟩
  obtain ⟨U,hU⟩ := WilsonPhysicalExteriorResolved.formal L
  obtain ⟨Y,hY⟩ := WilsonPhysicalExteriorResolved.formal D
  obtain ⟨l₁,d₁,z₁⟩ := offersPl V M T u ht (gulfG (P:=P))
  obtain ⟨l₂,d₂,z₂⟩ := offersPl V M T u ht (westV (P:=P))
  exact ⟨U,Y,hU,hY,fun _ hs k=>
    ⟨WilsonPhysicalExteriorResolved.closure L l₁ l₂ hU hs k,
      WilsonPhysicalExteriorResolved.closure D d₁ d₂ hY hs k,
      WilsonPhysicalExteriorResolved.trade L D l₁ d₁ l₂ d₂ z₁ z₂ hU hY hs k⟩⟩
end

section
open Tide
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
set_option quotPrecheck false
local notation "Yr"=> ApplyMPl φ A.team A u
local notation "Ur"=> ApplyMPl φ ( Stripped A.team ) A u
local notation "Qa"=> goalsK c P.η Yr
local notation "Qr"=> SeedsWPl c φ A u P
local notation "φX"=> PortEntryPl φ A ∘ u
theorem assembly (hc:G.Simple)(hp: Clearance L x)(he: Vista.width L x)(hm:WidthW V P.η c)(ht: Resolved P ( info c ))(hv: Sparse l c)(b:Bool)(hV: TaylorOKPl S φ A) : ∃ (Z:Terrify W I)(X:Rake.Dance G I W), CCOrb G P.η A.team x L Qa b Z ∧
  (∀ i s,PhysicalSum G A.team (P.η i) (dimT L i) b s (fun w=>c w i) ( x i ) Ur ( bury i s Z )) ∧ DOrd M P S u ( info c ) X ∧ Judge P c V Z ( toZ X ) L l ( Label.h ∘ u ) ∧ ∀ s:Finset W,s.Nonempty→∀ n,Verdict P ( Vane.charge ( Label.h ∘ u ) s ) 0 ( X s n ) := by
   obtain ⟨hK,hP,H,hmenu⟩:= billMenusPl u (φ:=φ) (A:=A) hc; have heo : FlowSet V Qa:= moneyM c hm (fun i=>⟨ false,0,hK.badge i ⟩); let t:=A.team; obtain ⟨F,f,hF,hf,hT,h0,hpay⟩:= Ωgo ( P:=x ) hV.bulk heo hm.proper b hp he; obtain ⟨Z,X0,hZ,hZ',hX,h',hx⟩:= Ωgo (P:=x) hV.bulk ( show FlowSet V Qr from moneyM c hm (fun i=>⟨ false,0,hP.badge i ⟩) ) hm.proper b hp he;
   obtain ⟨U',D,hU,hD,hr⟩:= covers φ S A u P hc ht hV; refine ⟨ f,D,hf,fun i s=> κglyph c i hK.badge hf ( fun _=>billRentPl .. ) H,hD, ?_, fun s hs n=> hr s hs n |>.2.1 ⟩;
   have hUe : U'=voyage c Z:= Rake.perfect hU ( BoardingPl c (seedW_okPl c) hZ (Fleet.fee hZ (moneyM c hm (fun i=> ⟨false,0,hP.badge i⟩))) ); have hΩ(s:Finset W)(hp:s.Nonempty)(n:ℕ): toZ Z s n=toZ U' s n:= by
       funext i; let v(t:ℝ):= (Z s n) i (exp t) []; have he : (fun t:ℝ=> U' s n i t [])=v:= funext fun t=> by rw [ hUe, τv ]
       obtain HT:= ( hX s n i ).comp tendsto_exp_atTop; obtain HH:=hr s hp n|>.1.1 i; change Tendsto (fun t:ℝ=> U' s n i t [] ) _ _ at HH; rw [ he ] at HH; exact tendsto_nhds_unique HT HH
   refine ⟨ ⟨h0,zeroZ hD.1⟩,⟨ toZ Z,toZ F, zeroZ hZ.1,zeroZ hF.1, fun s hs n=>?_,hpay, fun n s=>?_ ⟩ ⟩; · rw [ hΩ s hs n ]; obtain ⟨ h,hv,hu⟩:= hr s hs n; exact ⟨marketV h hv hu,h.2.2⟩
   let a(i:I)(s:Finset W)(n:ℕ):= toZ Z s n i; let v i s n:= toZ F s n i; exact Filter.EventuallyEq.symm ( peaks (l:=l) (X:=a) (Y:=v) ( marked W ) Toy ( pointed _ (zeroZ hZ.1)) (fun i=> fun s _ n _=> Submodule.mem_top) ( pointed _ (zeroZ hF.1)) (fun i s _ n _=>Submodule.mem_top) (fun s n=> Echo.quote hv hP hK hV.bulk hc hmenu hZ hF n s) s n ) -- Params order
end

end YM.Integration.WilsonPhysicalExteriorResolvedFleet
