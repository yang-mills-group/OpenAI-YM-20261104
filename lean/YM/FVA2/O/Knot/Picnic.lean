import YM.FVA2.O.Knot.Tie
import YM.FVA2.O.Fusion.Logs
/-!
# Initial-cost solver (all grades)
Per arbitrary moving matching scale, reaching negative rank eventually cuts the iterated Picard sum.
No output support or smoothness assumptions on the matching *index*. Cost only Warm.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.FVA2.O.Knot
open MS Function Filter Set Finset MS.Latch Job MS.Plane MeasureTheory Real Metric
open Heat LogTime IntervalFamily Koszul Tone Momentum Landau Fiddle Osc Snap Wire Signal
open Lives MS.City MS.Rake Tune Flux Book Convolve Serve Vane O.Fuse MS.Land MS.Local.Physical
open scoped Topology ContDiff Interval
variable {I J:Type}{G:Gauge} {b η:I→ℝ}{k t:ℤ}{F H:Glade G I}{X Y:T ( Glade G I )}
variable {B:Deck G}{K:Booked B}{M:MS_Data G K}{n:ℕ}
abbrev Tactic (F H:Glade G I)(b:I→ℝ): Glade G I:= seatB b F+tieQ b H
def closeP (b:I→ℝ) (X:Glade G I) := tieQ b ((both G I).P X)
lemma drops (hp:Warm F false)(h:Diversity F k): Diversity ( closeP b F ) (k-2):= perf_s ( cdrop hp h realityA )
lemma fence (hp:Bank F t): Bank (closeP b F) t:= Tie_t hp.A
lemma final_view (hp:Bank F t)(he:Diversity F k)(i:ℕ): Bank ((closeP b)^[i] F) t ∧ Diversity ((closeP b)^[i] F) (k-2*i):= by
    induction i with| zero=> simpa using And.intro hp he | succ i ih=> rw [Function.iterate_succ_apply']; push_cast; exact ⟨ fence ih.1,( show k-2*(i:ℤ)-2=k-2*(i+1) by ring ) ▸ drops (ih.1.cross) ih.2 ⟩
lemma loopQ (b:I→ℝ)(hp:Bank F t)(ht:Bank H t): ∃ X:Glade G I,Bank X t ∧ Velocity X (H+(both G I).P X) ∧ ( ∀ i,X i (b i)= F i (b i) ):= by
    let Y:= Tactic F H b; have hY : Bank Y t:= (bank_at hp).add (Tie_t ht); obtain ⟨m,h⟩:= hY.heat; let Z:=closeP (G:=G) b; let V(i:ℕ):= Z^[i] Y; let X:=∑ i∈Finset.range (m+1), V i; have hV i:= final_view (b:=b) hY h i; have hx: Bank X t:= Bank.all_fin _ ( fun i _=> (hV i).1 ); have hz: X=Y+Z X:= by
        have hu: Z X=∑ i∈Finset.range (m+1), V (i+1):= by unfold X Z closeP; rw [map_sum,tie_sum (Finset.range (m+1)) (f:=fun i=>(both G I).P (V i)) (fun i _=> ( hV i|>.1.A ).cross )]; exact Finset.sum_congr rfl fun i _=> (iterate_succ_apply' Z i Y).symm
        rw [hu, Finset.sum_range_succ (fun i=> V (i+1)) m, show V (m+1)=0 from dry (hV (m+1)|>.2) (by omega), add_zero]; unfold X; rw [ Finset.sum_range_succ' ]; rw [ show V 0=Y from rfl,add_comm ]
    refine ⟨ X,hx,?_,?_⟩; · nth_rw 1 [hz]; exact Velocity.add (by have h:Velocity ( seatB b F ) 0:=fun i t l=>hasDerivAt_const ..; simpa only [zero_add] using h.add (tie_v (b:=b) ht.cross) : Velocity Y H) (tie_v hx.A.cross)
    intro i; rw [hz]; simp [Y,Tactic,Z,closeP,seatB]
private def rim (b:I→ℝ)(F:T (Glade G I))(M:MS_Data G K)(η:I→ℝ)(t:ℤ)(X:T (Glade G I))(n:ℕ) : Prop:= ∀ i<n,Bank (X i) t ∧ Velocity (X i) ( helm M η X i ) ∧ seatB b (X i)= seatB b (F i)
private lemma talk (A B:T (Glade G I))(h:∀ i≤ n,A i=B i): helm M η A n= helm M η B n:= by
    rw [hel_core,hel_core]; congr! 1; · rw [h _ (le_refl _)]
    unfold lonely; apply Finset.sum_congr rfl; intro i hi; rw [h i ( Finset.mem_Ico.mp hi |>.2.le )]
lemma soars (M:MS_Data G K)(b η:I→ℝ)(hp:Banks X t) : ∃ F:T (Glade G I),Response F M η t ∧ (∀ n, seatB b (F n) = seatB b ( X n )):= by
    let H(Y:T (Glade G I))(n:ℕ):= lonely (fun _=>lineA G) (gather M η) Y n
    have hY (Y:T (Glade G I))(k:ℕ)(h:rim b X M η t Y k): ∃ F:T ( Glade G I ),rim b X M η t F (k+1) ∧ ∀ i<k,F i= Y i:= by
       have he : Bank (H Y k) t:= Bank.all_fin _ (fun i hi=> (zero_add t) ▸ Bank.X ( plenary M _ ) (h i (Finset.mem_Ico.mp hi|>.2)|>.1) ) -- unif
       obtain ⟨Z,hZ,hv,hF⟩:= loopQ b ( hp k ) he; let F (i):= if i=k then Z else Y i; have hy(i)(h:i<k): F i=Y i:= if_neg h.ne; refine ⟨ F,?_,hy⟩; intro i hi; rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h'|h'; · rw [hy i h', talk (M:=M) F Y (fun j hj=> hy j (lt_of_le_of_lt hj h')) ]; exact h i h'
       subst i; obtain he':F k=Z:= if_pos rfl; rw [ hel_core, he', show lonely (fun _=>lineA G) (Lives.gather M η) F k=H Y k from ?_ ]; · exact ⟨ hZ,(by rw [add_comm]; exact hv), funext fun i=> funext fun _=>hF i ⟩
       exact Finset.sum_congr rfl fun i hi=> congr_arg (fun F=> expJ ( fun _=>lineA G ) ( gather M η (k-i) ) F ) (hy _ (Finset.mem_Ico.mp hi|>.2))
    choose Z hz h using hY; let V:∀ k,{F:T ( Glade G I ) // rim b X M η t F k}:= fun k=> Nat.recOn k ⟨0,fun i h=>False.elim ((Nat.not_lt_zero i) h)⟩ (fun k v=> ⟨ Z v.val k v.property, hz v.val k v.property ⟩); let f i := (V (i+1)).val i; have hf(i j)(hh:i<j): ( V j ).val i=f i:= by
       change i+1 ≤ j at hh; induction j,hh using Nat.le_induction with| base=>rfl| succ j hh ih=> exact (h _ j (V j).property i hh).trans ih
    refine ⟨ f,⟨fun n=> ((V (n+1)).property n (Nat.lt_succ_self n)).1,fun n=>?_⟩, fun n=> ((V (n+1)).property n ( Nat.lt_succ_self n )).2.2 ⟩; rw [talk f ( V (n+1) ).val (fun i hi=> ( hf i _ ( Nat.lt_succ_of_le hi ) ).symm )]; exact ((V (n+1)).property n (Nat.lt_succ_self n)).2.1
end YM.FVA2.O.Knot
