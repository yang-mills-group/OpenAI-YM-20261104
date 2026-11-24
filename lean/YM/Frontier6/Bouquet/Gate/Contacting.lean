import YM.Frontier6.Bouquet.Gate.Veins
/-!
# Physical masks; record legitimate motions in the finite evaluation
 not assumptions about estimates on such motions.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet
open Function Set Finset Ensemble MeasureTheory Submodule Normal Analysis Anise Metric
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P Q R:Ensemble}
def Pod.pair (i j:Slot): Pod:= ⟨insert i {j}, Finset.insert_nonempty ..⟩
lemma normGap {p:Pod}{i j:Slot}{x: Room}(hi:i∈p.val)(hj:j∈p.val): ‖house i x-house j x‖≤2*‖ontoSpace (normal p) x‖:=by
   let v:= ontoSpace (normal p) x
   have he : house i (x-v.val)=house j (x-v.val):= tie_eq on_drop hi hj; rw [map_sub, map_sub] at he
   rw [show house i x-house j x= house i v.val-house j v.val from (by rw [sub_eq_sub_iff_add_eq_add] at he ⊢; convert! he using 1; abel)];
   exact (norm_sub_le ..).trans (le_trans (add_le_add (norm_house i v.val) (norm_house j v.val)) (two_mul _).symm.le)
lemma equal_pair {i j:Slot}{x:Room}(he:x i=x j) : ontoSpace (normal (Pod.pair i j)) x=0:=by
    apply on_blank; apply tie_up; let p:= Pod.pair i j; have hx(k:Slot)(hk:k∈p.val): x k=x i:= by rcases Finset.mem_insert.mp hk with hk|hk; exact congr_arg _ hk; rw [mem_singleton.mp hk,he]
    exact fun k hk=> (hx k hk).trans (hx p.here p.here_mem).symm
abbrev Balcony (P:Ensemble) := P→ Set E4
def Fair (s:Full (fiber P)) (B: Balcony P) (x: Seats P) :Prop:=∀ y∈ tsupport s,∀ (p:P)(i:Slot),i∈p.val.val→ actual x y p i∈ B p
namespace Fair
variable {f g:Full (fiber P)}{B:Balcony P}{x:Seats P}(h:Fair f B x)
include h
lemma narrower (he: tsupport g⊆tsupport f): Fair g B x:= fun _ hy=> h _ (he hy)
lemma broad {Q: Balcony P}(he:B≤ Q): Fair f Q x:=fun a hay i j hj=> he i (h a hay i j hj)
lemma moved (he: Q ≤ P) (y: Margin P Q) : Fair (restrictS (plan_sub he) (insideCL loft_le y) f) (B ∘ assign he) (transit he x y):= fun z hz p i hi=> (actual_down he x y p hi z) ▸ h _ (restrict_support _ _ f hz) _ _ (inside he p hi)
end Fair

-- matrix separation in a refinement
variable {x:Seats P}
def Separate (h:Q≤P) (y:fiber P):Prop := ∀ (i j:Q), i≠ j→ assign h i=assign h j→ ∀ (z w:Slot),z∈ i.val.val→w∈j.val.val→ house z y.val≠ house w y.val
lemma scar_pair (h:Q≤P) {i j:Q}(hh:i≠j)(he:assign h i=assign h j){z w:Slot}(hz:z∈ i.val.val)(hw:w∈j.val.val): Pod.pair z w∈ scars P Q:=by
    rw [scars, Finset.mem_sdiff]; constructor
    · apply encloses.mpr; refine ⟨(assign h i).val, (assign h i).property,fun k hk=>?_⟩; rcases mem_insert.mp hk with h'|h'; exacts [h' ▸ inside h i hz,he.symm ▸ Finset.mem_singleton.mp h' ▸ inside h j hw] -- he maybe orientation?
    intro hu; obtain ⟨p,hp,hq⟩:= encloses.mp hu; let v:Q:=⟨_,hp⟩; have hI:i=v:= serial Q hz (hq (mem_insert_self ..)); exact hh (hI.trans (serial Q (hq (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))) hw))
lemma Separate.excision (h:Q≤P)(C:Veins){y:fiber P}{f:Full (fiber P)}(he:y∈ tsupport (C.film P Q f)): Separate h y:=by
   intro i j hh hk a b ha hb hX
   let p:= Pod.pair a b; have ht : C.range p ≤ ‖ontoSpace (normal p) y.val‖:= C.cutter_tale (scar_pair h hh hk ha hb) (C.film_support' _ f he); rw [equal_pair (x:=y.val) hX,norm_zero] at ht; exact not_le.mpr (C.pos p) ht

lemma Separate.positions (h:Q≤P){y:Margin P Q}(he:Separate h (insideCL loft_le y)){i j:Q}(hp:i≠j)(hv:assign h i=assign h j): transit h x y i≠transit h x y j:=by
    rw [set_down h x y i i.val.here_mem,set_down h x y j j.val.here_mem,hv]; exact fun hh=> he i j hp hv _ _ i.val.here_mem j.val.here_mem (add_right_cancel hh)
lemma Separate.included (h:Q≤P)(he:R≤P){y:Margin P R}(hf: Separate h (insideCL loft_le y)): R≤Q:=by
    by_contra hh; obtain ⟨i,q,v,x,z,hq,hx,hX,hz,hZ,hp⟩:= scar_deny he h hh; exact hf q v hq hp x z hX hZ (tie_eq (orthogonal_le (home_sub i.property) (loft_orth (y.property))) hx hz)
lemma Seats_fair (h: Q≤P){y:Margin P Q}(f: Full (fiber P)) {B: Balcony P}(hc:Fair f B x)(he: insideCL loft_le y ∈ tsupport f) (i:Q): transit h x y i∈ B (assign h i) :=by
    rw [set_down h x y i i.val.here_mem]; exact hc _ he (assign h i) _ (inside h i i.val.here_mem)
end YM.Frontier6.Bouquet
