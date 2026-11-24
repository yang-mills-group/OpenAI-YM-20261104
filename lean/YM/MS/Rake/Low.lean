import YM.MS.Latch.Quilt
/-!
# Responses with zero UV boundary, over smooth point family.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open scoped Topology ContDiff Interval
abbrev Glade (G:Gauge)(I:Type):= Moments I ( Law G )
abbrev Planet (G:Gauge)(I:Type):= Moments I ( Edge G )
variable {I J:Type}{G:Gauge}{F H X:Glade G I}{K: Belt I}{L:Planet G I}{a b:Bool} {Y:ℤ}{P:ℕ→K.time→ℝ}{r n:ℕ} {A:K.time→ℝ}
-- elementary algebra
abbrev Diversity (X:Glade G I)(Y:ℤ):= ∀ i t, Limit (X i t) Y
lemma uh (h: Diversity F Y)(he: Diversity H Y): Diversity (F+H) Y:= fun i t=> (h i t).add (he i t)
lemma behind {r:ℤ}(h:Diversity F Y)(he:Y≤r): Diversity F r:= fun i t=> Limit.up (h i t) he
def collect (F:Glade G I) := ∃ k:ℕ,Diversity F k
lemma collect_z : collect (0:Glade G I):= ⟨0,fun _ _ _ _=>rfl ⟩
lemma collect_p (hf:collect F)(hh: collect H): collect (F+H):= by obtain ⟨v,hv⟩:=hf; obtain ⟨u,hu⟩:=hh; exact ⟨max v u,uh (behind hv (by omega)) (behind hu (by omega))⟩
lemma aboveC (P:Belt I)(b:Bool)(h:collect F):∃ n:ℕ,∀ i, Upper b n (plug ( J:=P.slot) F i):= by obtain ⟨n,h⟩:=h; exact ⟨ n,fun i w hw hp=> (h i.1 i.2 w (by omega))⟩
def Birth (G:Gauge)(K:Belt I)(P:ℕ→K.time→ℝ): Prop:= (∀ j,nn (P j)) ∧ Walk K∧Shore K∧∀ j, Break (G:=G) false false K (P j) (P j)
-- include collect con fields
structure CabinF (P:ℕ→ K.time→ℝ)(F:Glade G I): Prop where
    pick: ∀ j, Here false false K F (P j)
    mood: Warm F false
namespace CabinF
lemma trainS (h:CabinF P F)(H:Birth G K P): Job.train false F:= FarX (H.2.2.2 0) H.2.1 (h.pick 0) H.2.2.1 h.mood.walk
lemma shelter (h:CabinF P F)(H:Birth G K P) : CabinF P (river F):= ⟨fun n=> (pastH (H.2.2.2 n) H.2.1 (H.1 n) H.2.2.1 h.mood (h.pick n)).1,( pastH (H.2.2.2 0) H.2.1 (H.1 0) H.2.2.1 h.mood (h.pick 0) ).2.2⟩
lemma warm_zip (hf:Warm X b)(ht:Warm F b): Warm (X+F) b:= ⟨fun i t ht'=> Lease.plus (hf.cost i t ht') (ht.cost i t ht'), fun i t ht'=>Continuous.add (hf.walk i t ht') ( ht.walk i t ht')⟩
lemma warm0 : Warm (0:Glade G I) b:= ⟨ fun _ _ _=> Lease.zero fun _=>zero_le_one,fun _ _ _=>continuous_const⟩
lemma add (hF:CabinF P F)(he: CabinF P H): CabinF P (F+H):= ⟨ fun i=> Lease.plus (hF.pick i) (he.pick i),warm_zip hF.mood he.mood⟩
lemma zero (H:Birth G K P): CabinF ( G:=G) P 0:= ⟨fun i=> Lease.zero (H.1 i), warm0⟩
end CabinF
lemma flow_add (h:Job.train false F)(hp: Job.train false H): Job.river (F+H) = river F+river H:= by funext i t l; unfold river; simp only [Pi.add_apply]; exact integral_add ( h i t l (fun x=> Bool.noConfusion x) ) (hp i t l (fun x=> Bool.noConfusion x))
lemma river0 : river (0:Glade G I)=0:= by funext i t l; unfold river; simp
lemma diversity_flow (h:Diversity F Y): Diversity (river F) Y:= fun i t l hl=> by simp [ Job.river,show ∀ t,F i t l=0 from fun t=> h i t l hl ]
lemma dry (h:Diversity F Y)(hx:Y<0): F=0:= funext fun i=> funext fun t=> funext fun p=> h i t p (by omega)
lemma collect_tree (K:Planet G I)(hf:collect X)(hp:collect F): collect (G:=G) (fun i t=> tree parity (K i t) ( X i t ) ( F i t )):= by obtain ⟨n,hf⟩:=hf; obtain ⟨k,hp⟩:= hp; exact ⟨n+k,fun i t=> ( leastT (hf i t) (hp i t) _).up (by omega)⟩
lemma collect_join {A:I→QP} (μ:I→Measure QP)(K:Planet G I)(hf:collect X)(hp:collect F): collect (G:=G) (fun i t=> Cabin (A i) (K i t) (μ i) ( X i t) ( F i t )):= by obtain ⟨n,hf⟩:=hf; obtain ⟨k,hp⟩:=hp; exact ⟨n+k,fun i t=> (capjoin (hf i t) (hp i t) (μ i) (K i t) _).up (by omega)⟩
lemma warm_sum {F:J→ Glade G I}(S: Finset J)(hp:∀ i∈S,Warm (F i) b): Warm (∑ i∈ S,F i) b:= by classical induction S using Finset.induction with| empty=> rw [Finset.sum_empty]; exact CabinF.warm0| insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact CabinF.warm_zip (hp i (by simp)) (ih fun j hj=>hp j (by simp [hj]))
lemma collected {F:J→ Glade G I}(S:Finset J)(hp:∀ i∈S,collect ( F i )): collect (∑ i∈ S,F i ):= by classical induction S using Finset.induction with| empty=> rw [Finset.sum_empty]; exact collect_z| insert i s hi ih=> rw [ Finset.sum_insert hi ]; exact collect_p (hp i (by simp)) (ih fun j hj=>hp j (by simp [hj]))
lemma He_here {F:J→ Glade G I}(S:Finset J)(hp:∀ i∈ S,Here b a K ( F i ) A)(he:nn A): Here b a K (∑ i∈S,F i) A:= by
   classical
   induction S using Finset.induction with|empty=> rw [Finset.sum_empty]; exact Lease.zero he| insert i s hi ih=> rw [Finset.sum_insert hi]; exact Lease.plus (hp _ (by simp)) (ih fun j hj=> hp j ( Finset.mem_insert_of_mem hj))
end YM.MS.Rake
