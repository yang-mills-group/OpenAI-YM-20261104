import YM.Frontier6.Bouquet.Anise.Mail

/-!
# Center coordinates. Each Ensemble owns the corresponding map Anchors.
 Orthogonal slots in `fiber`; at a split transfer the new centers over the
 independent macro space `Margin`. Keep branches in the same frame, transporting
 only over that independent variable. (Cut projections can leave the footprint in
 inner test assignments but not on this macro transfer.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q R:Ensemble}{p q:Pod}
abbrev Seats (P:Ensemble):= P→ E4
-- physical slot at its relative frame. Intentionally not junked for i ∉ p;
-- use membership hypotheses where required.
def actual (x:Seats P)(y:fiber P)(p:P)(i:Slot):= house i y.val + x p
@[fun_prop] lemma actual_cont (p:P)(i:Slot): Continuous (fun (y: Seats P × fiber P)=> actual y.1 y.2 p i):=by
    unfold actual; fun_prop
-- transfer of anchors (not ROOT PROJECTION but macro integration). Relative frame remains same
section
variable (h:P ≤ Q) (x:Seats Q) (z: Margin Q P)
def transit : Seats P:= fun p:P=> centroid p.val z.val + x (assign h p)
lemma set_down (p:P){i:Slot}(hi:i∈ p.val.val): transit h x z p = house i z.val + x (assign h p):=by unfold transit; rw [pod_centroid (orthogonal_le (home_sub p.property) (loft_orth z.property)) i hi]; rfl
lemma actual_down (p:P){i:Slot}(hi:i∈p.val.val)(y:fiber P): actual x (forward (plan_sub h) (insideCL loft_le z) y) (assign h p) i= actual (transit h x z) y p i:=by
   unfold actual; rw [set_down h x z _ hi, forward_cast, map_add]; change house i z.val+house i y.val+ _= _; abel
@[fun_prop] lemma transit_cont : Continuous (fun i:Seats Q × Margin Q P=> transit h i.1 i.2):=by apply continuous_pi; intro i; unfold transit; fun_prop
lemma transit_self (x:Seats P) : transit (le_refl P) x 0=x:=by
   ext1 i; unfold transit; rw [Submodule.coe_zero,map_zero,zero_add, assigned (le_refl P) i i le_rfl]
lemma transits (he:Q ≤ R)(v:Seats R)(y: Margin R Q) : transit (le_trans h he) v ((bridges (plan_sub h) (plan_sub he)).together (y,z)) = transit h (transit he v y) z:=by
   ext1 p; rw [set_down (h.trans he) v _ p p.val.here_mem,set_down h _ z p p.val.here_mem, (bridges (plan_sub h) (plan_sub he)).together_eq, map_add, set_down he v y _ (inside h p p.val.here_mem),via h he p]; abel
end

section
variable (h:Free P Q){f:Seats (merge h)}
abbrev preL (x:Seats (merge h)) := x ∘ germL h
abbrev preR (x:Seats (merge h)) := x ∘ germR h
include h
lemma ignores_right (i:Slot)(hi:i ∈ Along P)(y: fiber Q): house i y.val=0:= (fiber_entire Q y.property) _ (fun hu=> Finset.disjoint_left.mp h hi hu)
lemma ignores_left (i:Slot)(hi:i∈Along Q)(y: fiber P): house i y.val=0:= ignores_right h.symm _ hi y
lemma acts_left (x:fiber P)(y:fiber Q) (p:P){i:Slot}(he:i∈p.val.val): actual f ((merged h).together (x,y)) (germL h p) i= actual (preL h f) x p i:=by unfold actual; rw [Tandem.together_eq, map_add, ignores_right h _ (listed P _ p.property he) y,add_zero];rfl
lemma acts_right (x:fiber P)(y:fiber Q)(p:Q){i:Slot}(he:i∈p.val.val): actual f ((merged h).together (x,y)) (germR h p) i= actual (preR h f) y p i:=by unfold actual; rw [Tandem.together_eq, map_add, ignores_left h _ (listed Q _ p.property he) x, zero_add]; rfl
section
variable {A B:Ensemble}{K: Free A B}(hA:A≤P)(hB:B≤Q)
    (p: Margin P A) (q:Margin Q B)
lemma transit_left : preL K (transit (merge_le h hA hB) f ((adds_macro h hA hB).together (p,q)))= transit hA (preL h f) p:=by
    ext1 a; unfold preL Function.comp
    rw [set_down (merge_le h hA hB) _ _ (germL K a) (show a.val.here∈ a.val.val from a.val.here_mem),set_down hA _ p a a.val.here_mem, Tandem.together_eq,map_add,left_travel h hA hB a, show house a.val.here q.val=0 from ignores_right h _ (ref_slots hA ▸ listed A _ a.property a.val.here_mem) (insideCL (show Margin Q B ≤ fiber Q from loft_le) q), add_zero] -- syntactic last fails
lemma transit_right : preR K (transit (merge_le h hA hB) f ((adds_macro h hA hB).together (p,q)))= transit hB (preR h f) q:=by
    ext1 a; unfold preR Function.comp
    rw [set_down (merge_le h hA hB) _ _ (germR K a) (show a.val.here∈ a.val.val from a.val.here_mem),set_down hB _ q a a.val.here_mem, Tandem.together_eq,map_add,right_travel h hA hB a, show house a.val.here p.val=0 from ignores_left h _ (ref_slots hB ▸ listed B _ a.property a.val.here_mem) (insideCL (show Margin P A ≤ fiber P from loft_le) p),zero_add] 
end
end
end YM.Frontier6.Bouquet
