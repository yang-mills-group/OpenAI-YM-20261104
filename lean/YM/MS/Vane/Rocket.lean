import YM.MS.Vane.Intake
/-!
# Getting all one/many-mark tangents for a Tour.Rates. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I E J:Type}{G:Gauge}[LinearOrder J] {s:Finset J}{P:Geo I}{R: J→ℕ}{x:Position J I}{K L:Planet G I}{b:Bool} {X H: Site G I}{A:J→Site G I}{Y:Dance G I J}{n:ℕ}{μ:I→Measure QP}
abbrev Src (P: Position J I)(μ:I→Measure QP)(K L:Planet G I)(F: Site G I)(X:Dance G I J)(s:Finset J)(k:ℕ):= multi μ P K L F ( X s ) X k s
abbrev rhs (P: Position J I)(μ:I→Measure QP)(K L:Planet G I)(F:Site G I)(X:Dance G I J)(s:Finset J)(k:ℕ):= sailP μ L ( X s k ) + Src P μ K L F X s k
variable (h:Tour K L P x b X A R)(hv: Fields x (fun _=>planeF) K L X A Y)
local notation "m0"=> (fun (_:I)=>planeF)
include h
lemma formal : ∃ Y, Fields x m0 K L X A Y:= by obtain ⟨Y,h,H⟩:= nominal h.ground h.plot h.energy ( fun i n=>⟨_,h.obey i n⟩ ); exact ⟨_,h⟩
include hv
lemma emerged (hp:2≤s.card)(n:ℕ): Came P b (Y s n):= by obtain ⟨U,hx,hL⟩:= nominal h.ground h.plot h.energy ( fun i n=>⟨_,h.obey i n⟩ ); rw [perfect hv hx]; exact hL s hp n
lemma tip0 (hs:s.Nonempty): ∃ a:ℕ,Tip P b false a ( Y s n ):= by
    by_cases he: s.card ≥ 2; · exact ⟨0,tipby (emerged h hv he n) _ ⟩;
    obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp ( show s.card=1 from by obtain he':= Finset.card_pos.mpr hs; omega ); rw [hv.2.1]; exact ⟨_,h.obey i n⟩
lemma founded (hp:s.Nonempty)(n:ℕ): collect ( Y s n ) ∧ Warm ( Y s n ) false:= by obtain ⟨v,hm⟩:= tip0 h hv (n:=n) hp; exact ⟨hm.1,hm.2.1⟩
lemma hosp (hp:s.Nonempty)(n:ℕ): Warm ( Src x m0 K L X Y s n ) false:= by
    refine CabinF.warm_zip ( warm_sum (F:=fun i=> expJ _ _ _) _ (fun i hi=>?_)) (warm_sum _ (fun i hi=>warm_sum _ (fun j hj=>?_))) -- infer F size
    · exact walk_tree h.ground.pinC ( h.energy ( n-i ) (by obtain hx: i<n:= ( Finset.mem_Ico.mp hi ).2; omega)|>.2.1 ) ( founded h hv hp i |>.2 )
    exact warmJoin (fun _=>Coherent) h.ground.pool (founded h hv ( n_small hi |>.2.1 ) _ |>.2 ) ( founded h hv ( n_small hi|>.2.2.1 ) _|>.2 )
lemma winter (hp:s.Nonempty)(n:ℕ): Warm (rhs x m0 K L X Y s n) false:= CabinF.warm_zip ( warmCycle (fun _=> Coherent) h.ground.pool ( founded h hv hp n|>.2 )) ( hosp h hv hp n )
-- Estimated.RHS triggers ∫.∂.We use HasDeriv along log time.
structure Fits (b:Bool)(F H:Glade G I): Prop where
    stroll: Stroll b H
    pace:∀ i w,Course b w→∀ t,HasDerivAt (fun t=>F i t w) ( H i t w ) t
lemma motion (hp:s.Nonempty)(n:ℕ) : Fits false ( Y s n ) (rhs x m0 K L X Y s n):= by
    obtain hh:= winter h hv hp n; refine ⟨ hh.walk, ?_⟩; intro i w hw t; by_cases hx:s.card<2
    · obtain ⟨k,rfl⟩:= Finset.card_eq_one.mp (show s.card=1 from by obtain he:= Finset.card_pos.mpr hp; omega); have hc: picks ({k}:Finset J)=∅:= Finset.eq_empty_iff_forall_notMem.mpr fun i hi=> clips (by simp) hi; unfold rhs Src multi; rw [hc,hv.2.1]; rw [Finset.sum_empty,add_zero]; exact h.register k n |>.motion i w t
    let H:=rhs x m0 K L X Y s n; obtain ⟨hu,hW,hM⟩:= hv.2.2 s (le_of_not_gt hx) n; change Y s n=river H at hM; have hx:(fun t:ℝ=> Y s n i t w)=fun t:ℝ=> river H i 0 w+∫ s in 0..t,H i s w:= funext fun t=> by rw [hM]; exact swamp hW i t 0 hw
    rw [hx]; exact ( hfun (hh.walk _ _ hw) t ).const_add _
end YM.MS.Vane
