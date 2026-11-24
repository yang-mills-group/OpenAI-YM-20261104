import YM.Frontier6.Bouquet.Atlas.Schedule

/-! Transporting through one boss annulus at a time (also disjoint advances
 already in the parent `Air` retain their powers). -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Bouquet.Atelier.Court
open Function Set Finset Ensemble MeasureTheory Normal Filter Audit Metric Submodule
open scoped Topology BigOperators Classical InnerProductSpace lp ContDiff
open scoped YM.Frontier6.Bouquet
variable {P:Ensemble}{i:P}(Z:Court i){r:ℝ}{A:Aura P}
set_option quotPrecheck false
local notation "Q"=> Z.split
local notation "↑ᴾ"=> assign Z.legend.le

def balcony (Z:Court i)(A:Aura P)(r:ℝ):Balcony Z.split:= fun p=> A.foot (assign Z.legend.le p) ∩ if p∈Z.small then Z.place A.center r p else Set.univ
lemma subset (A:Aura P)(r:ℝ): Z.balcony A r≤ A.foot ∘ (assign Z.legend.le):= fun _=> inter_subset_left
lemma toRight (A:Aura P)(r:ℝ){p:Z.split}(he:assign Z.legend.le p≠ i): Z.balcony A r p=A.foot (assign Z.legend.le p):=by unfold balcony; rw [if_neg (fun hh=> he ((members ..).mp hh)), Set.inter_univ]
lemma toLeft (A:Aura P)(r:ℝ){p:Z.split}(he:p∈Z.small): Z.balcony A r p=A.foot i∩ Z.place A.center r p:= by unfold balcony; rw [if_pos he,(members ..).mp he]
lemma convex (A:Aura P)(r:ℝ){M:Pod→ℝ} (he:A.Cozy M)(u): Convex ℝ (Z.balcony A r u):=by
    unfold balcony; apply Convex.inter (he.solid _); split; exact convex_closedBall ..; exact convex_univ
lemma crown_distance (A:Aura P) (hr:0<r){j k:Z.split}(he: assign Z.legend.le j=assign Z.legend.le k)(hv:j≠k){x y:E4}(hx:x∈ Z.balcony A r j)(hy:y∈ Z.balcony A r k) : Z.clearance*r ≤ ‖x-y‖:= by
    obtain ⟨hQ,hR⟩:= Z.focus j k he hv; rw [toLeft Z A r hQ] at hx; rw [toLeft Z A r hR] at hy; exact Z.scene_gap hr _ hQ hR hv hx.2 hy.2
lemma placements (A:Aura P)(hr:0<r) (p:P) : (dialogues Z.legend.le p : Set Z.split).PairwiseDisjoint (Z.balcony A r):=fun j hj k hk he=> Set.disjoint_left.mpr (fun x hx hy=>by have h:= Z.crown_distance A hr (((members ..).mp (show j∈dialogues _ _ from hj)).trans ((members ..).mp (show k∈dialogues _ _ from hk)).symm) he hx hy; rw [sub_self,norm_zero] at h; linarith only [mul_pos Z.pos hr,h]) -- implicit x?
lemma necklace (Z:Court i)(A:Aura P)(hr:0<r){f:Full (fiber P)}(he:Fair f A.foot A.center)(hc: Z.Contains r f) {x:Margin P Z.split}{v:fiber Z.split} (hf:forward (plan_sub Z.legend.le) (insideCL loft_le x) v∈ tsupport f)(p:Z.split)(j:Slot)(hj:j∈ p.val.val) :
    actual (transit Z.legend.le A.center x) v p j ∈ Z.balcony A r p:=by
    rw [← actual_down Z.legend.le A.center x p hj]; let U:= forward (plan_sub Z.legend.le) (insideCL loft_le x) v; change actual A.center U _ _∈_;
    refine ⟨he U hf _ _ (inside Z.legend.le p hj),?_⟩; by_cases h:p∈ Z.small; swap; rw [if_neg h]; exact Set.mem_univ _
    rw [if_pos h,(members ..).mp h]; exact Z.situate hr (hc U hf) p h hj
lemma enlivens (Z:Court i)(hr:0<r) {M:Pod→ℝ}(hp:A.Cozy M) {f:Full (fiber P)} (he: Fair f A.foot A.center)(hc: Z.Contains r f) {x:Margin P Z.split}{v:fiber Z.split}(hf:forward (plan_sub Z.legend.le) (insideCL loft_le x) v∈ tsupport f) (p:Z.split): transit Z.legend.le A.center x p∈ Z.balcony A r p:= average_within p v _ (Z.convex A r hp p) _ fun j hj=>necklace Z A hr he hc hf p j hj
end YM.Frontier6.Bouquet.Atelier.Court
