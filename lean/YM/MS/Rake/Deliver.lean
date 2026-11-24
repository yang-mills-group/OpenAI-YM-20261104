import YM.MS.Rake.Low
/-!
# Equation for repeated loops with coherent rank reserve. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open scoped Topology ContDiff Interval
variable {I:Type}{G:Gauge}{F H X:Glade G I}{K: Belt I}{L:Planet G I}{Y:ℤ}{P:ℕ→K.time→ℝ}{r n:ℕ}{b:Bool} {A:K.time→ℝ}
abbrev DegreeAt (F H:Glade G I)(r:ℤ): Prop:=∀ i t (x:Legs (Lane4 G)), (x.length:ℤ)≥r→ F i t x=H i t x
abbrev Calculator (G:Gauge)(I:Type):= Glade G I→ Glade G I
variable {U:Calculator G I}
structure Engine (U: Calculator G I): Prop where
   degree (ρ:ℤ) (F Y:Glade G I): DegreeAt F Y (ρ+1) → DegreeAt (U F) (U Y) ρ
   empty: U 0 = 0
structure Duty (P:ℕ→ K.time→ℝ)(U:Calculator G I): Prop where
   motor : Engine U
   add F H: Warm F false → Warm H false→ U (F+H)=U F+U H
   invoke F: CabinF P F → CabinF P ( U F )
def Trip (U: Calculator G I)(F H:Glade G I): Prop:= collect F ∧ Job.train false (U F+H)∧ F=river ( U F+H ) -- H independent term
namespace Duty
lemma fee (hU:Engine U)(he:Diversity F Y): Diversity (U F) (Y-1):= by
   intro i t p h; have hx (r):= hU.degree r F 0; rw [hU.empty] at hx; exact hx ( Y ) (fun i t v hi=> he i t v (by omega)) i t p (by omega)
def Ψ (U:Calculator G I)(n:ℕ) (F:Glade G I):= (river ∘ U)^[n] F
lemma prepares (hm:Duty P U)(hb:Birth G K P)(hf:CabinF P F)(n:ℕ): CabinF P (Ψ U n F):= by
    induction n with| zero=> exact hf| succ n ih=> rw [Ψ, iterate_succ_apply']; exact (hm.invoke _ ih).shelter hb
lemma Pdiv (h:Engine U)(hv:Diversity F Y)(k:ℕ): Diversity (Ψ U k F) (Y-k) := by induction k with| zero=> simpa [Ψ] using hv| succ k ih=> rw [Ψ, iterate_succ_apply',show Y-(↑(k+1):ℤ)=Y-↑k-1 from by omega ]; exact diversity_flow (fee h ih)
lemma pic (hf:CabinF P F) (hp:Duty P U)(hb:Birth G K P)(hv:collect F) : ∃ H: Glade G I,CabinF P H∧ Trip U H F := by
    let Y n:= Ψ U n (river F); have hz(n): CabinF P (Y n):= prepares hp hb (hf.shelter hb) n; obtain ⟨M,hm⟩:= hv; let W:= Finset.range (M+1); have hy(n): Diversity ( Y n ) ((M:ℤ)-n):= Pdiv hp.motor (diversity_flow hm) n;
    let V0:=∑ i∈W,Y i; have H (W: Finset ℕ): CabinF P (∑ i∈W,Y i):= ⟨ fun n=> He_here W (fun i _=> (hz i).pick n) (hb.1 n), warm_sum W (fun i _=>(hz i).mood) ⟩
    have Hζ:= (hp.invoke V0 (H W)); refine ⟨V0,H W,collected W (fun i _=> ⟨M,behind (hy i) (by omega)⟩ ),(Hζ.add hf).trainS hb,?_⟩; rw [ flow_add (Hζ.trainS hb) (hf.trainS hb) ]; have hld (W:Finset ℕ): river (U (∑ i∈ W, Y i))=∑ i∈W,Y (i+1):= by induction W using Finset.induction with| empty=> rw [Finset.sum_empty,Finset.sum_empty,hp.motor.empty,river0]| insert i s hi ih=> rw [Finset.sum_insert hi, hp.add _ _ (hz i).mood (H s).mood,flow_add (hp.invoke _ (hz i)|>.trainS hb) ( hp.invoke _ (H s) |>.trainS hb ), ih, Finset.sum_insert hi]; congr 1; unfold Y Ψ; rw [iterate_succ_apply']; rfl
    unfold V0 W; rw [hld]; conv_lhs=> rw [Finset.sum_range_succ']
    conv_rhs=> lhs; rw [Finset.sum_range_succ]
    rw [dry ( hy (M+1)) (by omega), add_zero ]; rfl
lemma consistent (h:Engine U)(hv:Trip U F X)(ht:Trip U H X): F=H:= by
    suffices he: DegreeAt F H 0 from funext fun i=>funext fun t=>funext (fun l=> he i t l (by omega)); obtain ⟨M,hM⟩:= hv.1; obtain ⟨n,hp⟩:=ht.1; let Y':ℕ := max M n+1; have hu : DegreeAt F H ( Y':ℤ ):= fun i t l hx=>( hM i t l (by unfold Y' at hx; omega)).trans ( hp i t l (by unfold Y' at hx; omega) ).symm
    suffices he: ∀ (v:ℕ), DegreeAt F H ((Y':ℤ)-v) from by simpa only [sub_self] using he Y'
    intro k; induction k with
    | zero=> simpa using hu
    | succ n ih=>
       intro i t w hw; nth_rw 1 [hv.2.2,ht.2.2]; unfold river; refine integral_congr_ae (Filter.Eventually.of_forall fun p=>congr_arg (fun c=> c+ X i p w) (h.degree F H (ρ:=(Y':ℤ)-↑(n+1:ℕ)) ?_ i p w hw) ); rw [ show (Y':ℤ)-( ↑(n+1:ℕ) )+1 = ↑Y'-n from by omega]; exact ih
end Duty
-- instantiate single-cycle
abbrev sailP (μ:I→Measure QP)(K: Planet G I) : Calculator G I:= fun V i t=> cycle (K i t) (μ i) (V i t)
variable {m:I→Measure QP}
lemma retire (L:Planet G I) (m:I→Measure QP): Engine (sailP m L) := by
    constructor; · intro r F Y h i t w hw; unfold sailP cycle; refine integral_congr_ae (Filter.Eventually.of_forall fun p=>?_); simp_rw [at_trc,show ∀ u v:Lane4 G,F i t (u::v::w)= _ from fun u v=> h i t (u::v::w) (by simp; omega)];
    funext i t v; simp_rw [sailP,cycle,Pi.zero_apply,map_zero]; simp
lemma Sat_W (h:Warm H b)(he:BackF L)(hM:∀ i,Cohere (m i)) (x:I)(t:ℝ): SatC (m x) ( L x t ) ( H x t ) b := by
    let T:=‖t‖+1; have hT:T≥0:= by unfold T; positivity
    let p:camp T:= ⟨(),t,existsC t⟩; obtain ⟨d,hD,hQ⟩:= funds (camp T) (hM x); exact herec hQ (he.cost x T hT) (h.cost x T hT|>.highp) (fun i=>zero_le_one) (fun i=>zero_le_one) p
lemma control (h:Birth G K P)(hm:∀ i,Cohere (m i))(hL:BackF L)(hx: Sheet K.price 1 (plug L))(hv:Mint K.price (m ∘ Sigma.fst) n) (hK:glob K.price (m ∘ Sigma.fst) n): Duty P (sailP m L):= by
    refine ⟨ retire L m,?_,?_⟩; · intro F H h hh; funext i t l; exact of_cyc ( Sat_W h hL hm i t ) ( Sat_W hh hL hm i t ) (fun v=> Bool.noConfusion v)
    intro F hv'; refine ⟨fun i=>?_,warmCycle hm hL hv'.mood⟩; have ht := planC (μ:=m∘Sigma.fst) ((hv'.pick i).highp) hx hK hv ( h.1 i ) (fun _=>zero_le_one); rw [one_mul] at ht; exact ht
end YM.MS.Rake
