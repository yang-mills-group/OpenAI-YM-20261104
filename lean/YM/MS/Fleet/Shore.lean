import YM.MS.Fleet.Span
/-!
Cover comparison identity from the exact zero-length specification. Statement independent of Mesh
assumption. `voyage` gives the same solution as `LOrd` (proven shorter-distance estimates there),
not a special choice of eventual regularization or extension. Use even after taking Y scalar.
-/
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
variable {B:Local.Physical.Deck G}{T:Prescription B}{R: Geo I}{v:W→ Rake.Label B}{V:LitBook B}
local notation "πA"=> Scope G (Wind.skyline G T.team) R.η
omit [LinearOrder W] in
lemma castP {U P:Dec G}{φ:Actor G} (us:I→ℝ)(C:Faces I) (h:PM φ U P e)(n:ℕ)(L':I→Side)(A':I→Cover): let M:Rake.Site G I:= fun n i t=>lodging (C i) ( (Ext G ( P n ) us) i t ); Clocked (zip0 (outside L') ιW A') (fun i=>frameL ( C i ) ( run ( φ ( us i ) n ) )) ( M n ) ( lonely ιW (Scope G U us) M n ):= by
    intro M; refine ⟨ fun i=> congr_arg (frameL (C i)) ( h.recu n (us i)|>.1 ), (cap_lod C ( feesBuy (h.owes n) us )).2,?_ ⟩; intro i t w; let c:=frameL ( G:=G ) ( C i ); let q:=P n ( us i ); let K:= Cpu G t
    have he : zip0 (outside L') ιW A' ( M n ) i t= c ( Wiref G q t ):= by
        rw [flat_zip0 ( outside L' ) rfl]; change Θ_pc false μzone 0 (dope K) (lodging ( C i ) (sleeve lace (q t)))= c (Heat.orbit K μzone (q t)); rw [ finite_cc μzone (period0 μzone cour0 ( main_f _ ) (((h.owes n).stay ( us i ) ).joint)), Θ_z,be_cycle,skin_c ]; rfl
    have hL : lonely ιW (Scope G U us) M n i t= c ( path 1 n 0 U P ( us i ) t ):= by unfold lonely path; rw [one_smul]; simp_rw [Finset.sum_apply,map_sum]; refine Finset.sum_congr rfl fun j hj=>?_ ; rw [ show c=frameL ( G:=G ) ( C i ) from rfl,f_l ]; exact ( be_tree ( C i ) ( Dk_rev ( Vrev G t ) ) ).trans (congr_arg ( lodging ( C i ) ) ( D_tree ( Vrev G t ) ) ) -- defeq `κ`
    have hv (F:Law G): c F w=( be (C i) ( net w )*hook lace w )* F w:= by rw [show c=_ from rfl,f_l,lodg,sleeve_here,mul_assoc]
    obtain hz:= h.recu n (us i)|>.2 t w; change HasDerivAt (fun t=>c (q t) w) ((zip0 (outside L') ιW A' (M n)) i t w + (lonely ιW (Scope G U us) M n ) i t w) t; rw [he,hL]; simp_rw [ hv ]; exact (by simpa only [Pi.add_apply,mul_add] using hz.const_mul ( be (C i) ( net w )*hook lace w )) -- order
lemma special (p:W) {F:Rake.Site G I}(h:∀ i, Clocked (zip0 (outside L) ιW A) ( Q {p} i ) ( F i ) ( lonely ιW πA F i ))(he:Crew Ψ ιW πA 0 A Q X): X {p}=F:= by
   funext n; induction n using Nat.strong_induction_on with| h n ih=>
       obtain ht:= he.2 {p} ( Finset.singleton_nonempty _ ) n; rw [ campus,Vista.idle_d rfl,add_zero, archB, show picks ({p}:Finset W)=∅ from Finset.eq_empty_iff_forall_notMem.mpr (fun i hx=> Rake.clips (Finset.card_singleton _) hx), Finset.sum_empty,add_zero, show lonely ιW πA ( X {p} ) n= lonely ιW πA F n from Finset.sum_congr rfl (fun i hi=> by rw [ih i ( mem_Ico.mp hi|>.2)]) ] at ht; exact modal_uniq ( β_motor (engineV ..)) ht ( h n )
-- marks specification. independent of flow!
abbrev PortEntry (V:LitBook B)(T:Prescription B)(u:Rake.Label B): Actor G:= score V T.team ( T.fees u.h u.item )
-- avoid abbrev Prop
structure Crew0 (V:LitBook B)(T:Prescription B)(v:W→ Rake.Label B)(η:I→ℝ)(c:Berth ( W:=W ) ( I:=I ))(Q:Seeds G I W) : Prop where
   one (p:W)(n:ℕ)(i:I): Q {p} n i=frameL ( c p i ) ( run ( PortEntry V T ( v p ) ( η i ) n ) )
   higher (p:Finset W): 2≤ p.card→ Q p=0
lemma Boarding (hP: Crew0 V T v R.η c Q)(hx: Crew Ψ ιW πA 0 A Q X)(he:∀ i t,Knits ( X i t )): LOrd V R T v (info c) (voyage c X):= by
   refine ⟨?_,fun p=> ?_,fun s hs k=>?_ ⟩; · unfold voyage; rw [ hx.1 ]; funext i t p; dsimp only [ vessel, unload, Pi.zero_apply ]; rw [ map_zero,map_zero ]; -- sometimes no subM
   · let P:=v p; let Hw:= horizon V T.team ( T.fees P.h P.item ); let F:Rake.Site G I:=fun n i t=>lodging ( c p i ) ( Scope G Hw R.η n i t ); have hΨ : X {p}=F:= by
         refine special p (fun n=>?_) hx; rw [show Q {p} n = _ from funext ( hP.one p n ) ]; exact castP R.η (c p) ( aqua V T.team ( T.fees P.h P.item )) n L A
     unfold voyage; rw [hΨ]; funext n i t; unfold vessel; rw [anchorC, dif_pos ( Finset.singleton_nonempty _ ), Finset.min'_singleton ]; exact unpack_home (c p i)
   obtain H:=hx.2 s ( Finset.card_pos.mp (by omega) ) k
   let f:=X s k; let E:= Vista.fort Ψ A ιW πA 0 X s k; have heL(i): f i 0=0:= by rw [show f i 0=Q s k i from H.1 i, hP.higher s hs ]; rfl -- beta
   have hE:Toned E:=( knit_plus ( LiftE.knit ( gen_zip0 Ψ ( healthy G I ) A ) ( he s k )) ( campusK ( healthy G I ) (fun k=> feesBuy ( skyPC G T.team|>.owes k) R.η) (fun _ _=> knit0 ..) (fun i _=>he i) k (fun i _=> he s i ) ) ).1
   obtain hz := curve ( F:=f ) ( H:=E ) H.2 (anchorC c s) hE heL
   have hu : ( sailP m0 Y (voyage c X s k)+Rake.multi m0 (info c) ρk Y (initials R T) (voyage c X s) (voyage c X) k s )= (fun i t=> ( exp t:ℂ ) • vessel E ( anchorC c s ) i t):= by funext i t; apply f_inj ( anchorC c s i ); rw [ map_smul, show frameL _ (vessel E _ i t)=E i (exp t) from accountable .., show E i _=_ from π_src (R:=R) (X:=X) c T A s L (fun i n=> he i n |>.1) t k i,smul_inv_smul₀ ( by exact_mod_cast ( exp_pos t ).ne' )]
   unfold Trip; rw [hu]; exact hz
end YM.MS.Fleet
