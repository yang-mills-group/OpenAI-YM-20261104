import YM.MS.Rake.Magic
import YM.WiderProfiles.Rake.Cluster
/-!
WiderProfiles §F.1. Derivations extended from `YM/MS/Rake/Magic.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}
variable (x:Position W I)(μ:I→Measure QP)(K L:Planet G I)(F: Site G I)(A:W→ Site G I)
variable {x K L A F} {P:Geo I}{b:Bool}
section
local notation "N" => story x (fun _=>planeF) K L F A
lemma stage_wide (h: Stage K L P b)(hx: WMesh P x)(hm: ∀ i,0< i→ Tip P b true 4 (F i))(he:∀ (s:W) n, ∃ d:ℕ,Tip P b false d (A s n))(s:Finset W) (hp: s.Nonempty) (n:ℕ): (∃ d:ℕ,Tip P b false d (N s n))∧ (2 ≤ s.card→ Came P b (N s n) ∧ Trip (sailP (fun _=>planeF) L) ( N s n ) (multi (fun _=>planeF) x K L F (N s) N n s)) := by
    induction s using Finset.strongInductionOn generalizing n with| _ s ih=>
       by_cases hv:2≤s.card; swap; · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from (by obtain H:= Finset.card_pos.mpr hp; omega)); refine ⟨?_,fun p=>False.elim (hv p)⟩; rw [st_u]; exact he i n
       induction n using Nat.strong_induction_on with
       | h k hK=>
          let S := multi (fun _=>planeF) x K L F (N s) N k s; have hO : Came P b S := by
             let Z(i:Finset W) := rootX x i-rootX x s; let Y := fun (i:Finset W)=>∑ j∈antidiagonal k,regionC (fun _=>planeF) (Z i) L ( N i j.1 ) (N (s\i) j.2 ); let C:=∑ i∈picks s,Y i; have hh: Came P b C:= by
                 refine seamount (fun i hi=>seamount (fun j hj=> ?_)); obtain ⟨H,hx',he,hI⟩:= n_small hi; obtain ⟨m,hm⟩:=( ih i H hx' j.1 ).1; obtain ⟨v,hv⟩:= ( ih (s\i) hI he j.2 ).1; exact Geo.touch_wide h (Rake.space_wide hx hi) hm hv
             obtain hL: Came P b (lonely K F ( N s ) k):= by refine seamount (fun i hi=>?_); obtain hx: i<k:= (Finset.mem_Ico.mp hi).2; exact cone h (hK _ hx|>.2 hv|>.1) (hm _ (by omega))
             exact ⟨ hL.1.add hh.1,collect_p hL.2 hh.2 ⟩
          obtain hS : Came P b (N s k) ∧ Trip (sailP (fun _=>planeF) L) ( N s k ) S := st_n _ _ _ _ _ _ hv k ▸ wand_C h hO;
          exact ⟨⟨0, Geo.tipby hS.1 0⟩,fun _=>hS⟩
lemma nominal_wide {P: Geo I}{b:Bool}(h:Stage K L P b)(hx:WMesh P x)(hm:∀ i,0< i→Tip P b true 4 (F i))(he:∀ s n,∃ d:ℕ,Tip P b false d ( A s n )) : ∃ X, Fields x (fun _=>planeF) K L F A X∧∀ (s:Finset W), 2≤s.card→∀ n,Came P b (X s n):= by
    have he(s:Finset W) (hp:s.card≥2) (k:ℕ):= stage_wide h hx hm he s ( Finset.card_pos.mp (by omega) ) k|>.2 hp; refine ⟨N,⟨ st_0 x _ K L F A,st_u x _ K L F A, fun s hp n=>?_⟩,fun s hp n=>(he s hp n).1⟩; exact ( he s hp n ).2
end
end YM.MS.Rake
