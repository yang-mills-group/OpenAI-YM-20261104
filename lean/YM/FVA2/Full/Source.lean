import YM.MS.Fleet.Shore
import YM.MS.Fleet.Docks
import YM.MS.Swirl.Migrate
import YM.FVA2.Full.Covers
/-! FVA_2 addition: `FullBook` with W-type shifts.
Module Source. Relevant proofs extended from `LitBook` in
YM.MS.Fleet.Shore
YM.MS.Fleet.Docks
YM.MS.Swirl.Migrate.
Main stencils/rank/affordability modified in `YM.FVA2.Full.Glyph`.
Names with `F` suffix are generally for the adjusted versions.
No changes to `PhysicalSum`, BV prescription or `MS_Data`. -/
set_option autoImplicit false
noncomputable section
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
variable {B:Local.Physical.Deck G}{T:Prescription B}{R: Geo I}{v:W→ Rake.Label B}{V:FullBook B}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
abbrev PortEntryF (V:FullBook B)(T:Prescription B)(u:Rake.Label B): Actor G:= scoreF V T.team ( T.fees u.h u.item )

structure Crew0F (V:FullBook B)(T:Prescription B)(v:W→ Rake.Label B)(η:I→ℝ)(c:Berth ( W:=W ) ( I:=I ))(Q:Seeds G I W) : Prop where
   one (p:W)(n:ℕ)(i:I): Q {p} n i=frameL ( c p i ) ( run ( PortEntryF V T ( v p ) ( η i ) n ) )
   higher (p:Finset W): 2≤ p.card→ Q p=0
lemma BoardingF (hP: Crew0F V T v R.η c Q)(hx: Crew Ψ ιW πA 0 A Q X)(he:∀ i t,Knits ( X i t )): LOrdF V R T v (info c) (voyage c X):= by
   refine ⟨?_,fun p=> ?_,fun s hs k=>?_ ⟩; · unfold voyage; rw [ hx.1 ]; funext i t p; dsimp only [ vessel, unload, Pi.zero_apply ]; rw [ map_zero,map_zero ];
   · let P:=v p; let Hw:= horizonF V T.team ( T.fees P.h P.item ); let F:Rake.Site G I:=fun n i t=>lodging ( c p i ) ( Scope G Hw R.η n i t ); have hΨ : X {p}=F:= by
         refine special p (fun n=>?_) hx; rw [show Q {p} n = _ from funext ( hP.one p n ) ]; exact castP R.η (c p) ( aquaF V T.team ( T.fees P.h P.item )) n L A
     unfold voyage; rw [hΨ]; funext n i t; unfold vessel; rw [anchorC, dif_pos ( Finset.singleton_nonempty _ ), Finset.min'_singleton ]; exact unpack_home (c p i)
   obtain H:=hx.2 s ( Finset.card_pos.mp (by omega) ) k
   let f:=X s k; let E:= Vista.fort Ψ A ιW πA 0 X s k; have heL(i): f i 0=0:= by rw [show f i 0=Q s k i from H.1 i, hP.higher s hs ]; rfl
   have hE:Toned E:=( knit_plus ( LiftE.knit ( gen_zip0 Ψ ( healthy G I ) A ) ( he s k )) ( campusK ( healthy G I ) (fun k=> feesBuy ( skyPC G T.team|>.owes k) R.η) (fun _ _=> knit0 ..) (fun i _=>he i) k (fun i _=> he s i ) ) ).1
   obtain hz := curve ( F:=f ) ( H:=E ) H.2 (anchorC c s) hE heL
   have hu : ( sailP m0 Y (voyage c X s k)+Rake.multi m0 (info c) ρk Y (initials R T) (voyage c X s) (voyage c X) k s )= (fun i t=> ( exp t:ℂ ) • vessel E ( anchorC c s ) i t):= by funext i t; apply f_inj ( anchorC c s i ); rw [ map_smul, show frameL _ (vessel E _ i t)=E i (exp t) from accountable .., show E i _=_ from π_src (R:=R) (X:=X) c T A s L (fun i n=> he i n |>.1) t k i,smul_inv_smul₀ ( by exact_mod_cast ( exp_pos t ).ne' )]
   unfold Trip; rw [hu]; exact hz
end YM.MS.Fleet
end
set_option autoImplicit false
noncomputable section
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
variable {B:Local.Physical.Deck G}{T:Prescription B}{R: Rake.Geo I}{l:W→ Rake.Label B}{W':FullBook B}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
variable { U:W→ Actor G}{ η:I→ℝ}
abbrev SeedsWF (V:FullBook B)(T:Prescription B)(l:W→ Rake.Label B)(R: Rake.Geo I): Seeds G I W:= goalsK c R.η ( (PortEntryF V T) ∘ l )
lemma seedW_okF : Crew0F W' T l R.η c ( SeedsWF c W' T l R ):= ⟨fun p n i=> goals_m c R.η p n i,fun p h=> goals_t c R.η (by omega) ⟩
lemma cashSeedsF (T:Prescription B) (l:W→ Label B) (W':FullBook B)(h: WidthW V R.η c): SpaceOut.FlowSet V ( SeedsWF c W' T l R ):= moneyM c h (fun _=>⟨ false,0,decorF W' ..⟩)
end YM.MS.Fleet
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Swirl.Near
open Function Set Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom
open scoped Topology ContDiff Interval
variable {A E I W:Type} [AddCommGroup E][Module ℂ E] {G:Gauge}{i:I}{L:I→Side}{A':Faces I} {φ:Team}{n d:ℕ}{N:Side} {X:Actor G} {V: W→Actor G} [LinearOrder W] {b:Bool}{η:I→ℝ}
open SpaceOut
lemma billRentF {B:Local.Physical.Deck G}(P: FullBook B)(p:Team)(v: Acts B d): Circle G ( Menus.rentF P p v ) false 0 where
    stance0 _ _ h:=Bool.noConfusion h
    actual i x:= posesF P p ..
    settled i x:= appearsF P p v x i
    tag i:= rentReadyF P p ..
    room i:=⟨ i+d,fun x=> by exact_mod_cast rentLimitF P p v x i⟩
omit [LinearOrder W] in
lemma rankVF {B:Local.Physical.Deck G}(t:Team)(U:FullBook B)(d:ℕ)(A:Acts B d)(x:ℝ): Menus.rentF U t A x= car ( Y t x ) ( Menus.rentF U (Stripped t) A x ):= by
    have he (t:Team): Menus.rentF U t A x=∑ i:Glyph B d,pairW ( LinearMap.lsmul ℂ (Dot G Cover) ) (fun n=> oil A i n x) (Glyph.preambleF U t i x):= funext (fun n=> by rw [Finset.sum_apply]; rfl);
    rw [ he t, he ( Stripped t ),map_sum ]; refine Finset.sum_congr rfl fun i _=>?_ ; unfold Glyph.preambleF; rw [ sWob ( t:=t ), oil_roll ]
end YM.MS.Swirl.Near
end
