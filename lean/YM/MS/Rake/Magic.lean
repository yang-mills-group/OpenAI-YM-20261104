import YangMills.WilsonProof.NativeSupport.YM.MS.Rake.Cluster
/-!
# Well-founded manufacturing many source amplitudes, always in rank/loop program. Parameters kept.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}
def wand (U:Calculator G I)(X:Glade G I): Glade G I:= by classical exact if h:∃ F, Trip U F X then Classical.choose h else 0
lemma wand_spec {U:Calculator G I}{F H: Glade G I}(hp:Engine U)(ht:Trip U F H): wand U H= F:= by unfold wand; rw [dif_pos (show ∃ x, Trip U x H from ⟨F,ht⟩)]; exact Duty.consistent hp ( Classical.choose_spec (show ∃ x,Trip U x H from ⟨F,ht⟩) ) ht
lemma wand_C {b:Bool}{P:Geo I} {K L:Planet G I}{F:Glade G I}(hs:Stage K L P b)(hp:Came P b F): Came P b (wand (sailP (fun _=>planeF) L) F) ∧ Trip (sailP (fun _=>planeF) L) (wand (sailP (fun _=>planeF) L) F) F:= by
    obtain ⟨H,h,hV⟩:= Duty.pic hp.1 (ready P hs) (born P G b) hp.2; rw [wand_spec ( retire L (fun _=>planeF)) hV]; exact ⟨⟨ h,hV.1⟩,hV⟩
variable (x:Position W I)(μ:I→Measure QP)(K L:Planet G I)(F: Site G I)(A:W→ Site G I)
def loadM (s:Finset W)(X:Dance G I W) : Site G I:= fun n=> Nat.strongRecOn n fun k f=> wand (sailP μ L) (multi μ x K L F (fun i=>if h:i<k then f i h else 0) X k s)
lemma loaded (s:Finset W)(X:Dance G I W)(n:ℕ): loadM x μ K L F s X n=wand (sailP μ L) (multi μ x K L F (loadM x μ K L F s X) X n s):= by
   unfold loadM; nth_rw 1 [Nat.strongRecOn, WellFounded.fix_eq]; apply congr_arg (wand _); unfold multi lonely; apply congr_arg ( · + _ ); refine Finset.sum_congr rfl (fun i hi=>?_); dsimp only; rw [dif_pos (Finset.mem_Ico.mp hi |>.2)]; rfl
def moor_help (s:Finset W)(f:∀ t:Finset W,t ⊂ s → Site G I) : Site G I := by -- def
   exact if h: s.Nonempty then (if s.card<2 then A (s.min' h) else loadM x μ K L F s (fun i=>if h:i ⊂ s then f i h else 0)) else 0
def story : Dance G I W:= fun s=> Finset.strongInductionOn s ( moor_help x μ K L F A )
local notation "V"=>story x μ K L F A
variable {s:Finset W}
lemma st_0 : V ∅=0:= by rw [story, Finset.strongInductionOn_eq]; simp [moor_help]
lemma st_u (i:W): V {i}=A i:= by rw [story,Finset.strongInductionOn_eq]; simp [moor_help]
lemma st_n (hp:2≤s.card)(k:ℕ): V s k=wand (sailP μ L) ( multi μ x K L F ( V s ) V k s):= by
    let X:= story x μ K L F A; let mp(t:Finset W):= if t⊂ s then X t else 0; have hx : V s = loadM x μ K L F s mp := by unfold story; rw [Finset.strongInductionOn_eq]; simp only [moor_help,dif_pos (Finset.card_pos.mp (show s.card>0 from by omega)), if_neg (by omega: ¬ s.card<2), dite_eq_ite]; rfl
    rw [hx,loaded]; refine congr_arg (wand _ ) (congr_arg (_+ ·) ?_); refine Finset.sum_congr rfl (fun i hi=> Finset.sum_congr rfl (fun j hj=>?_)); simp_rw [mp, if_pos ( n_small hi|>.1), if_pos ( n_small hi|>.2.2.2)]; rfl
variable {x K L A F} {P:Geo I}{b:Bool}
section
local notation "N" => story x (fun _=>planeF) K L F A
lemma stage (h: Stage K L P b)(hx: Mesh P x)(hm: ∀ i,0< i→ Tip P b true 4 (F i))(he:∀ (s:W) n, ∃ d:ℕ,Tip P b false d (A s n))(s:Finset W) (hp: s.Nonempty) (n:ℕ): (∃ d:ℕ,Tip P b false d (N s n))∧ (2 ≤ s.card→ Came P b (N s n) ∧ Trip (sailP (fun _=>planeF) L) ( N s n ) (multi (fun _=>planeF) x K L F (N s) N n s)) := by
    induction s using Finset.strongInductionOn generalizing n with| _ s ih=>
       by_cases hv:2≤s.card; swap; · obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from (by obtain H:= Finset.card_pos.mpr hp; omega)); refine ⟨?_,fun p=>False.elim (hv p)⟩; rw [st_u]; exact he i n
       induction n using Nat.strong_induction_on with
       | h k hK=>
          let S := multi (fun _=>planeF) x K L F (N s) N k s; have hO : Came P b S := by
             let Z(i:Finset W) := rootX x i-rootX x s; let Y := fun (i:Finset W)=>∑ j∈antidiagonal k,regionC (fun _=>planeF) (Z i) L ( N i j.1 ) (N (s\i) j.2 ); let C:=∑ i∈picks s,Y i; have hh: Came P b C:= by
                 refine seamount (fun i hi=>seamount (fun j hj=> ?_)); obtain ⟨H,hx',he,hI⟩:= n_small hi; obtain ⟨m,hm⟩:=( ih i H hx' j.1 ).1; obtain ⟨v,hv⟩:= ( ih (s\i) hI he j.2 ).1; exact Geo.touch h (Rake.space hx hi) hm hv
             obtain hL: Came P b (lonely K F ( N s ) k):= by refine seamount (fun i hi=>?_); obtain hx: i<k:= (Finset.mem_Ico.mp hi).2; exact cone h (hK _ hx|>.2 hv|>.1) (hm _ (by omega))
             exact ⟨ hL.1.add hh.1,collect_p hL.2 hh.2 ⟩
          obtain hS : Came P b (N s k) ∧ Trip (sailP (fun _=>planeF) L) ( N s k ) S := st_n _ _ _ _ _ _ hv k ▸ wand_C h hO;
          exact ⟨⟨0, Geo.tipby hS.1 0⟩,fun _=>hS⟩
lemma nominal {P: Geo I}{b:Bool}(h:Stage K L P b)(hx:Mesh P x)(hm:∀ i,0< i→Tip P b true 4 (F i))(he:∀ s n,∃ d:ℕ,Tip P b false d ( A s n )) : ∃ X, Fields x (fun _=>planeF) K L F A X∧∀ (s:Finset W), 2≤s.card→∀ n,Came P b (X s n):= by
    have he(s:Finset W) (hp:s.card≥2) (k:ℕ):= stage h hx hm he s ( Finset.card_pos.mp (by omega) ) k|>.2 hp; refine ⟨N,⟨ st_0 x _ K L F A,st_u x _ K L F A, fun s hp n=>?_⟩,fun s hp n=>(he s hp n).1⟩; exact ( he s hp n ).2
end
end YM.MS.Rake
