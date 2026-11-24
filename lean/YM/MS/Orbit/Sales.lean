import YM.MS.Orbit.Cleat
/-!
# Budget-free Volterra at absolute R. Actual Wick reading across charts.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Orbit
open Set Function Filter Finset Metric MeasureTheory
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Snap Native Lattice City Latch Job Belt Flux Cog Wire Rake Book
open scoped Topology ContDiff Interval
variable { I E A:Type}{G:Gauge}
abbrev over (I:Type)(A:Type):= Moments I (Raw A ℂ)
variable {U:over I A→ over I A}{F H X: over I A}{L:I→Raw A ℂ}
structure Modal (F: over I A) (H: over I A): Prop where
    cap : ∃ n:ℕ,∀ i t,Limit (F i t) n
    pace i t w: HasDerivAt (fun t:ℝ=>F i t w) ( H i t w ) t
abbrev Clocked (U: over I A→ over I A)(L:I→Raw A ℂ)(F H:over I A): Prop:= (∀ i,F i 0=L i ) ∧ Modal F (U F+H)
-- compare on truncations
abbrev upperRP (k:ℤ) (F H:over I A): Prop:=∀ i t (l:Legs A), ( l.length:ℤ ) ≥ k→ F i t l= H i t l
def motor (U:over I A→ over I A): Prop:= ∀ F H k,upperRP (k+1) F H→ upperRP k (U F) (U H)
lemma modal_uniq (h:motor U)(he:Clocked U L F X)(hp: Clocked U L H X): F=H:= by
   obtain ⟨k,hK⟩:= he.2.cap; obtain ⟨r,hR⟩:= hp.2.cap; let v:= (k+r:ℕ); have hT: upperRP ((v:ℤ)+1) F H:= fun i t l hL=> Eq.trans (hK i t l (by unfold v at hL; omega)) ( hR i t l (by unfold v at hL; omega)).symm
   suffices hv: ∀ i:ℕ, upperRP (v+1-(i:ℤ)) F H from funext fun i=> funext fun t=> funext fun l=> hv (v+1) i t l (by omega); intro ξ; induction ξ with| zero=> simpa using hT| succ ξ ih=>
      intro i t l hl; have hm : ∀ t, U F i t l= U H i t l := fun t=> h F H (v- (ξ:ℤ)) (show upperRP _ _ _ from (by rw [show (v:ℤ)- (ξ:ℤ)+1=v+1-(ξ:ℤ) from (by abel)]; exact ih)) i t l (by omega)
      have hx: F i t l-H i t l= F i 0 l-H i 0 l:= Wind.constancy (f:=fun t:ℝ=> F i t l - H i t l) (fun x=> (by convert! (he.2.pace i x l).sub ( hp.2.pace i x l) using 1; simp only [Pi.add_apply, hm, sub_self])) t; apply sub_eq_zero.mp; rw [hx, he.1 i,hp.1 i,sub_self ]
-- solve ext.All all. Rake.Engine & coast carry
variable {S T Y:Glade G I}{K:Calculator G I}
def reachP (F:Glade G I): Glade G I:= fun i=> Wind.coast (F i)
structure LiftE (K:Calculator G I): Prop extends Rake.Engine K where
   tones F: Toned F→Toned (K F)
   plus F X:Toned F→ Toned X→K (F+X)=K F+K X
lemma reachT (h:Toned S): Toned (reachP S):= by constructor; exact fun i=> deskLift (h.touch i); exact fun i t x y hv=>by unfold reachP Wind.coast; simp_rw [h.sound i _ x y hv]
lemma RP_add (h:Toned S)(he:Toned T): reachP ( S+T )=reachP S+reachP T:= by ext i t v; exact intervalIntegral.integral_add ( Wind.tune_interval ( h.touch i ) t v ) ( Wind.tune_interval ( he.touch i) t v )
lemma reach0 : reachP (0:Glade G I)=0:= by funext i t w; unfold reachP Wind.coast; simp
lemma reach_pc {c:ℤ}(h:Diversity S c): Diversity (reachP S) c:= fun i=> Wind.desk_max ( h i )
variable {X: I→Law G}
abbrev coast0 (X:I→Law G): Glade G I:= fun i _=> X i
namespace LiftE
variable (h:LiftE K)
include h
lemma φpay (H:Toned S)(n:ℕ): Toned ((reachP ∘ K)^[n] S) := by induction n with| zero=>exact H| succ n ih=> rw [iterate_succ_apply']; exact reachT (h.tones _ ih)
lemma δstart (q:ℤ)(hF:Diversity S q)(k:ℕ): Diversity ((reachP ∘ K)^[k] S) (q-k):= by induction k with| zero=> simpa using hF| succ k ih=> rw [ Function.iterate_succ_apply', show q-(↑(k+1:ℕ):ℤ)=q-k-1 from (by omega) ]; exact reach_pc ( Duty.fee h.toEngine ih )
lemma knit (hF:Knits S): Knits ( K S ):= by obtain ⟨H,k,hv⟩:= hF; exact ⟨ h.tones _ H,k, behind (Duty.fee h.toEngine hv) (by omega)⟩ -- shadow h
lemma perfect {H:Glade G I} (hf:Knits (coast0 X))(hp: Knits H): ∃ S, Clocked K X S H ∧ Knits S:= by -- H collision over I A
   let F:= coast0 X+reachP H; have ht:Knits F:= knit_plus hf ⟨ reachT hp.1, by obtain ⟨i,hi⟩:= hp.2; exact ⟨i,reach_pc hi⟩ ⟩; obtain ⟨hv,i,hI⟩:= ht; let W n:=(reachP ∘ K)^[n] F; let T(Q:Finset ℕ):=∑ n∈ Q, W n; have hA n:Knits ( W n ):= ⟨ φpay h hv n,i, behind (δstart h _ hI n ) (by omega) ⟩
   have hT s:Knits (T s):= knit_sum s fun i _=>hA i; let Y:= Finset.range (i+1); let Z:= T Y; have he : reachP (K Z) + F= Z:= by
       have he (Q:Finset ℕ):∑ n∈Q,W (n+1)=reachP ( K (T Q) ):= by induction Q using Finset.induction with| empty=> unfold T; rw [Finset.sum_empty,Finset.sum_empty,h.empty,reach0]| insert i q v ih=> rw [Finset.sum_insert v, ih, show T (insert i q)= _ from Finset.sum_insert (f:=W) v, h.plus _ _ (hA _|>.1) (hT q|>.1), RP_add ( h.tones _ (hA _|>.1) ) ( h.tones _ ( hT q|>.1)) ]; unfold W; rw [iterate_succ_apply']; rfl -- maybe more
       unfold Z; rw [← he]; unfold Y T; conv_rhs=> rw [Finset.sum_range_succ']
       conv_lhs=> lhs; rw [Finset.sum_range_succ]; rhs; rw [show W (i+1)=0 from dry (δstart h _ hI (i+1)) (by omega)]
       rw [add_zero ]; rfl -- order
   have hZ:Toned (K Z+H):= ( knit_plus ( h.knit ( hT Y )) hp ).1; have hw : Z=reachP ( K Z+H)+coast0 X:= by rw [ RP_add (h.tones _ ( hT Y|>.1 )) hp.1 ]; rw [ add_assoc,add_comm (reachP H),he ]; -- unfold F
   refine ⟨Z,⟨ fun i=>?_,⟨ hT Y|>.2, ?_⟩ ⟩, hT Y ⟩; · rw [hw]; funext; simp [reachP,Wind.coast] -- def?
   intro i t w; have hω:=hfun ( ( ( hZ.touch i ).at_const _ w contDiff_id ).continuous ) t; convert! ( hω.add_const ( X i w ) ) using 1; ext u; nth_rw 1 [hw]; rfl
end LiftE
end YM.MS.Orbit
