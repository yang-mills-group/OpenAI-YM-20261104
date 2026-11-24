import YM.ForFlash.MS.Phase
import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Sequence
import YM.MS.Rake.Magic
/-! Adapted from the YM modules indicated. Only lower gap hypothesis on the Mesh arguments,
see Phase for the change in the estimate itself. -/
set_option autoImplicit false
noncomputable section

/- Widening MS/Rake/Hour -/
namespace YM.MS.Rake.Geo
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open scoped Topology ContDiff Interval
variable {I J:Type}{G: Gauge}{b c:Bool}{x:I→QP}(P: Geo I){K L:Planet G I}{F H: Glade G I}
local notation "Ψ"=> east P b
variable (h:Stage K L P b)
include h
variable {P}
structure CoverSepForFlash (P:Geo I)(x:I→QP) : Prop where
    floor: ∃ C:ℝ,0<C∧∀ i,C*P.roots i≤‖x i‖
lemma touchForFlash (hz: CoverSepForFlash P x){n m:ℕ}(he: Tip P b false n F)(hx:Tip P b false m H): Came P b ( fun i t=> Cabin (x i) ( L i t ) planeF ( F i t ) ( H i t )):= by
    refine ⟨⟨?_, warmJoin (fun _=>Coherent) h.pool he.2.1 hx.2.1⟩, collect_join _ L he.1 hx.1⟩; intro k; obtain ⟨l,hM⟩:= money (b:=b) ( P:=P ) k n m; obtain ⟨C,hC,H⟩:=hz.floor; refine Lease.sticks ( PulseQForFlash ( v:=fun i=>P.roots i.1 ) ( A:=x∘ Sigma.fst ) h.well he.2.2 hx.2.2 ( airLamp _ _ ) (rateC _ _ ) (rateC _ _ ) hC (fun _=>exp_pos _) (fun i=> (H i.1)) ( rightB P ) l ) hM
end YM.MS.Rake.Geo

/- Widening MS/Rake/Cluster -/
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook
open Book.Convolve Geo
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}
def MeshForFlash (P:Geo I)(x:Position W I): Prop:= ∀ i j:W,i≠j→ CoverSepForFlash P (x i - x j)
variable {x:Position W I}{P:Geo I}{K L:Planet G I}{X Y: Dance G I W}{F:Site G I}{s t:Finset W}{w:W}{G':W→ Site G I}{b:Bool}
lemma spaceForFlash (h:MeshForFlash P x) (ht:t∈picks s): CoverSepForFlash P ( rootX x t-rootX x s ):= by obtain ⟨hh,hT,H⟩:= n_small ht; let p:=s\ t; have hx:= H.1; rw [unfT x ht,rootX, rootX,dif_pos hT,dif_pos hx]; refine h _ _ ?_; intro he; exact (( mem_sdiff.mp ( min'_mem p hx)).2) ( he ▸ min'_mem t hT )
end YM.MS.Rake

/- Widening MS/Rake/Magic -/
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}
variable (x:Position W I)(μ:I→Measure QP)(K L:Planet G I)(F: Site G I)(A:W→ Site G I)
local notation "V"=>story x μ K L F A
variable {s:Finset W}
variable {x K L A F} {P:Geo I}{b:Bool}
section
local notation "N" => story x (fun _=>planeF) K L F A
lemma stageForFlash (h: Stage K L P b)(hx: MeshForFlash P x)(hm: ∀ i,0< i→ Tip P b true 4 (F i))(he:∀ (s:W) n, ∃ d:ℕ,Tip P b false d (A s n))(s:Finset W) (hp: s.Nonempty) (n:ℕ): (∃ d:ℕ,Tip P b false d (N s n))∧ (2 ≤ s.card→ Came P b (N s n) ∧ Trip (sailP (fun _=>planeF) L) ( N s n ) (multi (fun _=>planeF) x K L F (N s) N n s)) := by
    induction s using Finset.strongInductionOn generalizing n with| _ s ih=>
       by_cases hv:2≤s.card; swap; · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from (by obtain H:= Finset.card_pos.mpr hp; omega)); refine ⟨?_,fun p=>False.elim (hv p)⟩; rw [st_u]; exact he i n
       induction n using Nat.strong_induction_on with
       | h k hK=>
          let S := multi (fun _=>planeF) x K L F (N s) N k s; have hO : Came P b S := by
             let Z(i:Finset W) := rootX x i-rootX x s; let Y := fun (i:Finset W)=>∑ j∈antidiagonal k,regionC (fun _=>planeF) (Z i) L ( N i j.1 ) (N (s\i) j.2 ); let C:=∑ i∈picks s,Y i; have hh: Came P b C:= by
                 refine seamount (fun i hi=>seamount (fun j hj=> ?_)); obtain ⟨H,hx',he,hI⟩:= n_small hi; obtain ⟨m,hm⟩:=( ih i H hx' j.1 ).1; obtain ⟨v,hv⟩:= ( ih (s\i) hI he j.2 ).1; exact Geo.touchForFlash h (Rake.spaceForFlash hx hi) hm hv
             obtain hL: Came P b (lonely K F ( N s ) k):= by refine seamount (fun i hi=>?_); obtain hx: i<k:= (Finset.mem_Ico.mp hi).2; exact cone h (hK _ hx|>.2 hv|>.1) (hm _ (by omega))
             exact ⟨ hL.1.add hh.1,collect_p hL.2 hh.2 ⟩
          obtain hS : Came P b (N s k) ∧ Trip (sailP (fun _=>planeF) L) ( N s k ) S := st_n _ _ _ _ _ _ hv k ▸ wand_C h hO;
          exact ⟨⟨0, Geo.tipby hS.1 0⟩,fun _=>hS⟩
lemma nominalForFlash {P: Geo I}{b:Bool}(h:Stage K L P b)(hx:MeshForFlash P x)(hm:∀ i,0< i→Tip P b true 4 (F i))(he:∀ s n,∃ d:ℕ,Tip P b false d ( A s n )) : ∃ X, Fields x (fun _=>planeF) K L F A X∧∀ (s:Finset W), 2≤s.card→∀ n,Came P b (X s n):= by
    have he(s:Finset W) (hp:s.card≥2) (k:ℕ):= stageForFlash h hx hm he s ( Finset.card_pos.mp (by omega) ) k|>.2 hp; refine ⟨N,⟨ st_0 x _ K L F A,st_u x _ K L F A, fun s hp n=>?_⟩,fun s hp n=>(he s hp n).1⟩; exact ( he s hp n ).2
end
end YM.MS.Rake

/- Widening MS/Rake/Sequence -/
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W] {G:Gauge}{ P: Geo I}{B:Local.Physical.Deck G}{O:Land.Booked B}{M: Land.MS_Data G O}
variable (V:LitBook B) (P:Geo I)(T: Prescription B)(M: Land.MS_Data G O)
structure TourForFlash (K L: Planet G I)(P:Geo I)(x:Position W I) (b:Bool)(Y:Site G I)(H: W→ Site G I)(sizes:W→ℕ): Prop where
    plot: MeshForFlash P x
    ground: Stage K L P b
    energy i : 0< i → Tip P b true 4 ( Y i )
    obey i n: Tip P b false (sizes i) (H i n)
    register s: Ven (fun _=> planeF ) K L Y (H s)
variable {P}{x:Position W I} (R: MeshForFlash P x) (labels:W→ Label B)
include R
omit [LinearOrder W] in
lemma builderForFlash : TourForFlash (constantP G I (PlanetD G)) (constantP G I (PlanetD G)) P x false (approach P M) (rowM P M ∘ labels) (Label.h ∘ labels):= ⟨ R,Geo.masterD .., fun _ _=> tagD P M _, fun i n=>tagF P M (labels i) n,fun i=>VeniceD P M ( labels i ) ⟩
end YM.MS.Rake
