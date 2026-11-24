import YM.FVAAlt2.Plus.High
import YM.MS.Fleet.Powers

/-! RichBook generalization. Adapted from `MS/Rake/Sequence`, `MS/Rake/Edict`, `MS/Vane/Trigger`, `MS/Fleet/Shore`, `MS/Fleet/Docks`, `MS/Fleet/Powers`. -/

set_option autoImplicit false
noncomputable section

-- Rake/Sequence
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W] {G:Gauge}{ P: Geo I}{B:Local.Physical.Deck G}{O:Land.Booked B}{M: Land.MS_Data G O}
variable (V:RichBook B) (P:Geo I)(T: Prescription B)(M: Land.MS_Data G O)
def rowKPl (x:Label B): Site G I:= circle P.η (col ( horizonPl V T.team ( T.fees x.h x.item ) ))
lemma lightLPl (h:G.Simple)(x:Label B) : Ven (fun _=>planeF) (constantP G I (LowP G)) (constantP G I (PlanetL G)) ( initials P T ) ( rowKPl V P T x ) := by
    let B:=skyline G T.team; let A:= T.fees x.h x.item; let H:= horizonPl V T.team A; obtain hP:= Marked.law (Wind.mark_seekPl V (d:=x.h) (p:=T.team) h) A; let Q:=Wind.SeekPl V T.team x.h;
    have hG:= hP.road; change Domain.Flow _ _ _ _ _ (Wind.col H) at hG; have hh (i:ℕ):Wind.Fees false 0 (H i):= ( Wind.aquaPl V T.team A ).owes i; intro n; refine ⟨ nameWarm (H n) (hh n),fun i w t=>?_ ⟩; obtain hv := pour (spaceL G) hG (P.η i) w n t; rw [ ergo (η:=P.η) ] at hv; let z:=exp t; let f:= H n (P.η i); have he : sailP (fun _=>μzone) (constantP G I (LowP G)) (rowKPl V P T x n) i t=cycle (PlanetL G t) planeF (f z):= ( startCycle f 0 (hh n|>.stay (P.η i)) _ _ ).symm
    rw [ show sailP (fun _=>(spaceL G).measure) _ (circle _ (col H) n) i t= _ from he ] at hv; exact hv
lemma tagXPl (x: Label B)(k:ℕ): Tip P true false x.h (rowKPl V P T x k):= by obtain h: Fees false 0 _:= ( Wind.aquaPl V T.team ( T.fees x.h x.item ) ).owes k; exact ⟨collectFee h,nameWarm _ h, Lease.sticks (sunX P _ h) (fun i=> rank_e P i x.h) ⟩
variable {P}{x:Position W I} (R: Mesh P x) (labels:W→ Label B) -- declare x
include R
omit [LinearOrder W] in
lemma touristPl (hc:G.Simple) : Tour ( constantP G I (LowP G) ) (constantP G I (PlanetL G)) P x true (initials P T) (rowKPl V P T ∘ labels) (Label.h ∘ labels):= ⟨ R,Geo.masterL .., fun _ _=> tagL P T _, fun i n=> tagXPl V P T (labels i) n,fun s=> lightLPl V P T hc (labels s) ⟩
end YM.MS.Rake

-- Rake/Edict
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}
   {Fp Q: Recount G}{u v:ℤ}
variable {K₀ K₁ U₀ U₁: Planet G I}{F X: Site G I}{A C: W→ Site G I}
-- lightweight edge.Radius.
variable {B: Local.Physical.Deck G}(V:RichBook B){O:Booked B}(M:MS_Data G O)(T:Prescription B)(p:W→ Label B)
lemma offersPl (h: TaylorOKPl M V T)(hv: Gold P K): Arch K (constantP G I (LowP G)) ( constantP G I (PlanetL G) ) (initials P T) ( rowKPl V P T∘ p ) ( Label.h∘ p ) ∧ Arch K (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (approach P M) (rowM P M ∘p) (Label.h∘p) ∧ ArcS K (constantP G I (LowP G)) (constantP G I (PlanetL G)) (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) (initials P T) (approach P M) ( rowKPl V P T ∘p ) (rowM P M ∘ p) ( Label.h ∘ p ):= by
    let S:= K.price; have hb (n:ℕ)(he: 0< n):= partials hv ( show 1 ≤ n from he ) ( fun r hr=> h.bulk n he r hr );
    have H (i:W) (n:ℕ) := partials hv ( show 0≤ n from Nat.zero_le n ) ( fun r hr=> (h.mark ( p i|>.h ) (p i|>.item)) n ( Nat.zero_le _ ) r hr );
    have he i : 1≤K.price.length i:= hv.day i ▸ Real.one_le_exp ( hv.paid i ); have hx:= cost_D (G:=G) hv.day
    exact ⟨ ⟨CoupleY he hv.day,Mate0 he hv.day,fun i hi=>(hb i hi).1,fun i n=>( H i n).1⟩, ⟨fun i j=> polar (hx i j),hx,fun i hi=>(hb i hi).2.1,fun i n=> (H i n).2.1⟩, ⟨ submarineT he hv.day (phaseY hv),submarineP he hv.day (phaseY hv), fun i hi=> ( hb i hi).2.2, fun i n=>(H i n).2.2 ⟩ ⟩ -- types.Loop.Serge.
end YM.MS.Rake

-- Vane/Trigger
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}{F H D: Glade G I}{X:I→ℂ}{d h:ℕ}{ζ:ℝ}
variable { J:Type}[LinearOrder W]{x:Position W I}{c b:Bool}{K L K' L':Planet G I}{B B': Site G I}{A A':W→Site G I}{R:W→ℕ}{p:ℝ}{U V:Dance G I W}{S:Finset W}{v:I→ℝ}
local notation "m0"=> (fun (_:I)=>planeF)
open Land Pearl Train Booked Menus Local.Physical
variable { B: Deck G} (V:RichBook B){O:Booked B}(M:MS_Data G O)(T:Prescription B)(R:W→Label B)(P:Geo I)
abbrev LOrdPl (V: RichBook B)(P:Geo I)(T:Prescription B)(R: W→Label B)(x:Position W I)(U:Dance G I W):= Fields x m0 (constantP G I ( LowP G )) ( constantP G I ( PlanetL G )) (initials P T) ( rowKPl V P T ∘ R ) U
include T
lemma CoversPl (h:G.Simple)(hx: Mesh P x)(he:TaylorOKPl M V T): ∃ U V', LOrdPl V P T R x U ∧ DOrd O P M R x V' ∧ ∀ S: Finset W,S.Nonempty→ ∀ n:ℕ,let k:= charge ( Label.h∘ R ) S; Verdict P k 0 ( U S n ) ∧ Verdict P k 0 ( V' S n ) ∧ Verdict P k eps_gain ( U S n - V' S n ):= by
    obtain ht:= touristPl V T hx R h; obtain hV:= builder M hx R; obtain ⟨ U,hU⟩:= formal ht; obtain ⟨W,hW⟩:= formal hV; obtain ⟨Z,X,Tz⟩:= offersPl V M T R he (gulfG (P:=P)); obtain ⟨Y,Q,RQ⟩:= offersPl V M T R he ( westV (P:=P) ); exact ⟨ U,W,hU,hW,fun _ hp n=> ⟨ closure ht Z Y hU hp n, closure hV X Q hW hp n,trade ht hV Z X Y Q Tz RQ hU hW hp n⟩ ⟩
end YM.MS.Vane

-- Fleet/Shore
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{L:I→Side}{S:Finset W} {e:ℤ}
  {X:Rake.Dance G I W}{Q:Seeds G I W}{F H:Glade G I}{n:ℕ}
  (c:Berth ( W:=W ) ( I:=I )) {A:Faces I}
local notation "Ψ"=> ( outside L )
local notation "ιW"=> ( Orbit.uniform G I )
open Native.Wilsonian Paint Rake.Geo Vane Land Program Logarithm Wind Menus
local notation "m0"=> (fun (_:I)=>planeF)
local notation "ρk"=> ( constantP G I (LowP G) )
local notation "Y"=> ( constantP G I (PlanetL G) )
variable {B:Local.Physical.Deck G}{T:Prescription B}{R: Geo I}{v:W→ Rake.Label B}{V:RichBook B}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
abbrev PortEntryPl (V:RichBook B)(T:Prescription B)(u:Rake.Label B): Actor G:= scorePl V T.team ( T.fees u.h u.item )
-- avoid abbrev Prop
structure Crew0Pl (V:RichBook B)(T:Prescription B)(v:W→ Rake.Label B)(η:I→ℝ)(c:Berth ( W:=W ) ( I:=I ))(Q:Seeds G I W) : Prop where
   one (p:W)(n:ℕ)(i:I): Q {p} n i=frameL ( c p i ) ( run ( PortEntryPl V T ( v p ) ( η i ) n ) )
   higher (p:Finset W): 2≤ p.card→ Q p=0
lemma BoardingPl (hP: Crew0Pl V T v R.η c Q)(hx: Crew Ψ ιW πA 0 A Q X)(he:∀ i t,Knits ( X i t )): LOrdPl V R T v (info c) (voyage c X):= by
   refine ⟨?_,fun p=> ?_,fun s hs k=>?_ ⟩; · unfold voyage; rw [ hx.1 ]; funext i t p; dsimp only [ vessel, unload, Pi.zero_apply ]; rw [ map_zero,map_zero ]; -- sometimes no subM
   · let P:=v p; let Hw:= horizonPl V T.team ( T.fees P.h P.item ); let F:Rake.Site G I:=fun n i t=>lodging ( c p i ) ( Scope G Hw R.η n i t ); have hΨ : X {p}=F:= by
         refine special p (fun n=>?_) hx; rw [show Q {p} n = _ from funext ( hP.one p n ) ]; exact castP R.η (c p) ( aquaPl V T.team ( T.fees P.h P.item )) n L A
     unfold voyage; rw [hΨ]; funext n i t; unfold vessel; rw [anchorC, dif_pos ( Finset.singleton_nonempty _ ), Finset.min'_singleton ]; exact unpack_home (c p i)
   obtain H:=hx.2 s ( Finset.card_pos.mp (by omega) ) k
   let f:=X s k; let E:= Vista.fort Ψ A ιW πA 0 X s k; have heL(i): f i 0=0:= by rw [show f i 0=Q s k i from H.1 i, hP.higher s hs ]; rfl -- beta
   have hE:Toned E:=( knit_plus ( LiftE.knit ( gen_zip0 Ψ ( healthy G I ) A ) ( he s k )) ( campusK ( healthy G I ) (fun k=> feesBuy ( skyPC G T.team|>.owes k) R.η) (fun _ _=> knit0 ..) (fun i _=>he i) k (fun i _=> he s i ) ) ).1
   obtain hz := curve ( F:=f ) ( H:=E ) H.2 (anchorC c s) hE heL
   have hu : ( sailP m0 Y (voyage c X s k)+Rake.multi m0 (info c) ρk Y (initials R T) (voyage c X s) (voyage c X) k s )= (fun i t=> ( exp t:ℂ ) • vessel E ( anchorC c s ) i t):= by funext i t; apply f_inj ( anchorC c s i ); rw [ map_smul, show frameL _ (vessel E _ i t)=E i (exp t) from accountable .., show E i _=_ from π_src (R:=R) (X:=X) c T A s L (fun i n=> he i n |>.1) t k i,smul_inv_smul₀ ( by exact_mod_cast ( exp_pos t ).ne' )]
   unfold Trip; rw [hu]; exact hz
end YM.MS.Fleet

-- Fleet/Docks
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{L:I→Side}{S:Finset W}{g:ℤ}
    {X:Rake.Dance G I W}{Q:Seeds G I W}{F:I→Law G}{n:ℕ}
variable (c:Berth ( W:=W ) ( I:=I )) {A:Faces I}{V:Vista.Visa I}
local notation "Ψ"=> ( outside L )
local notation "ιW"=> ( Orbit.uniform G I )
open Vista Vane Land High Program Native.Wilsonian Paint Wind Menus
variable {B:Local.Physical.Deck G}{T:Prescription B}{R: Rake.Geo I}{l:W→ Rake.Label B}{W':RichBook B}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
variable { U:W→ Actor G}{ η:I→ℝ}
abbrev SeedsWPl (V:RichBook B)(T:Prescription B)(l:W→ Rake.Label B)(R: Rake.Geo I): Seeds G I W:= goalsK c R.η ( (PortEntryPl V T) ∘ l )
lemma seedW_okPl : Crew0Pl W' T l R.η c ( SeedsWPl c W' T l R ):= ⟨fun p n i=> goals_m c R.η p n i,fun p h=> goals_t c R.η (by omega) ⟩
lemma cashSeedsPl (T:Prescription B) (l:W→ Label B) (W':RichBook B)(h: WidthW V R.η c): SpaceOut.FlowSet V ( SeedsWPl c W' T l R ):= moneyM c h (fun _=>⟨ false,0,decorPl W' ..⟩)
end YM.MS.Fleet

-- Fleet/Powers
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I W:Type}[LinearOrder W]{L:I→Side}{S:Finset W}
    {X U:Rake.Dance G I W}{Q:Seeds G I W}{F:I→Law G}{n:ℕ}{A:Faces I}
    (c:Berth ( W:=W ) ( I:=I )) {b:Bool}
open Vista Vane Rake.Geo Land High Program Logarithm Wind Menus Orbit.LogReal
variable {B:Local.Physical.Deck G}{O: Booked B}{V:RichBook B}{T:Prescription B}
   {R: Geo I}{Wv: Visa I}{l:W→ Rake.Label B}{M: MS_Data G O}
local notation "Ψ"=> outside L
local notation "ιW"=> Orbit.uniform G I
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
variable (h:G.Simple) (hc:TaylorOKPl M V T)(hx:Mesh R ( info c ))
    (hV: WidthW Wv R.η c)(hj:Clearance L A)(hL: Vista.width L A)
include h hc hx hV hj hL
lemma pursuitPl (b:Bool): ∃ (f: Finset W→ℕ→ I→ℂ)(g p:Rake.Dance G I W), CCOrb G R.η T.team A L ( SeedsWPl c V T l R ) b f ∧ LOrdPl V R T l (info c) g ∧ DOrd O R M l (info c) p ∧
    f ∅=0 ∧ ∀ s:Finset W,s.Nonempty→∀ n:ℕ,
    let k:= Vane.charge (Label.h∘ l) s
    let C:= Vane.blade (g s n)
    let B:= Vane.blade (p s n)
    cash_out Wv L ( f s n - C ) ∧ title R eps_gain k (C-B) ∧ Verdict R k 0 ( g s n ) ∧ Verdict R k 0 ( p s n ):= by
    let Q:=SeedsWPl c V T l R; let HP: SpaceOut.FlowSet Wv Q:=cashSeedsPl c T l V hV
    obtain ⟨Y,F,S,U,hU,H,hC,hB,hK⟩:= SpaceOut.Resolution hc.bulk HP hV.proper b hj hL
    obtain ⟨g,p,hg,hp,hD⟩:= CoversPl V M T l R h hx hc -- order inspect
    have ht : g=voyage c U := perfect hg ( BoardingPl c (seedW_okPl c) hU (fee hU HP) ); -- shadow hp
    have he(i:I)(s:Finset W)(H':s.Nonempty)(n:ℕ): Vane.blade ( g s n ) i= Vane.blade ( U s n ) i:= by
        have h := ( ( hC s H' n ).1 i ).comp tendsto_exp_atTop; apply tendsto_nhds_unique ( hD s H' n|>.1.1 i ); rw [ht]; exact h.congr fun t=>(τv c i t s).symm
    let f(t:Finset W)(n:ℕ)(i:I):ℂ:=limUnder atTop (fun p:ℝ=> S i t n p []); have h0 : f ∅=0:= by funext n i; unfold f; rw [(H i|>.1.2.1)]; exact Filter.Tendsto.limUnder_eq tendsto_const_nhds
    have hm (s:Finset W)(hz:s.Nonempty)(n:ℕ): f s n=Vane.blade (Y s n):= by funext i; unfold f; simp_rw [ ( H i ).2 ]
    refine ⟨ f,g,p,⟨ F,S,fun i=>H i|>.1, ?_⟩,hg,hp,h0,fun s hz n=>?_⟩
    · intro s n i; by_cases hs:s.Nonempty
      · rw [ show (fun p:ℝ=>(S i s n p [])) = _ from funext (H i|>.2 s n) ]; rw [hm s hs n]; exact (hB s hs n).1 i
      rw [Finset.not_nonempty_iff_eq_empty.mp hs,h0,(H i|>.1.2.1)]; exact tendsto_const_nhds
    intro k C0 B0; obtain ⟨ht,hz',hu⟩:= hD s hz n; refine ⟨?_,marketV ht hz' hu, ht,hz'⟩; rw [ hm s hz, show C0=_ from funext fun i=> he i s hz n ]; exact hK s hz n
end YM.MS.Fleet
