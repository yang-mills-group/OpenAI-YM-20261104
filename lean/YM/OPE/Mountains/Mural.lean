import YM.OPE.Mountains.Scene
import YM.OPE.Samples.Frame
/-!
# Expose drafts and windows. Any active subtree or remainder can be scheduled
with *its own* scales onto the same pattern bound.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset OPE.Log Mountain Trunk
open scoped Classical Topology BigOperators ContDiff
set_option quotPrecheck false
variable {I J:Type}[Fintype I] {s:Arboreal I} {φ:Ultrafilter J} {t:I→ℝ} {x:J→I→ E4}{R:J→I→ℝ}{M δ:ℝ}{i j k o u:I} {a b : Finset I}

namespace Portrait
variable (h:s.Coterie (φ:Filter J) t M δ x R) (V:Portrait s φ R o)
    (ht:s.Active a)(ho:o∈a)(ha:b ⊆ s.live a) (r : b) -- r is star
local notation "I'"=> (↑b:Type)
local notation "T"=> (fun i=>s.fullLife (R i))

def costCap (s:Arboreal I) : ℝ:= ∑ i,(s.depth i:ℝ)
private lemma useful' (i:I): (s.depth i:ℝ)≤ costCap s:= Finset.single_le_sum (fun u _=> Nat.cast_nonneg (α:=ℝ) (s.depth u)) (mem_univ i)
include h in
lemma cap : 0 ≤ 2*costCap s*M:=mul_nonneg (mul_nonneg zero_le_two (sum_nonneg fun i _=> Nat.cast_nonneg _)) h.cap
lemma near (h:s.Coterie (φ:Filter J) t M δ x R)(V:Portrait s φ R o) (he:i∈s.tower o) (hv:s.Anc i j): ∀ᶠ k in φ, ‖x k j-x k i‖ ≤ costCap s*M*V.top k (V.hue i):=by -- not 2*
    filter_upwards [h.space,V.close i he] with k hk he';
    calc _ ≤ (s.depth j:ℝ)*(M*R k i) := hk.near h.cap hv (tower_at.mp he).1
         _ ≤ costCap s*(M*R k i):= mul_le_mul_of_nonneg_right (useful' j) (mul_nonneg h.cap (hk.sizes.allowed _ (tower_at.mp he).1|>.le))
         _ ≤ costCap s*(M*V.top k (V.hue i)):= by gcongr; all_goals first | exact h.cap| exact he'.2| exact (sum_nonneg fun i _=> Nat.cast_nonneg _)
         _ = _:= by ring
lemma reach (h:s.Coterie (φ:Filter J) t M δ x R)(V:Portrait s φ R o) (he:i∈s.tower o) (hv:s.Anc i j): ∀ᶠ k in φ, ‖x k j-x k i‖ ≤ 2*costCap s*M*V.top k (V.hue i):=by
    filter_upwards [Portrait.near h V he hv] with k hk; linarith only [hk,norm_nonneg (x k j-x k i)]
-- force order of binder
variable (hp:∀ i∈ b,s.Anc o (s.parent i))
local notation "Q"=> frame h V r hp
include ht ha
lemma mura (hy:i∈s.tower o)(hx:s.Anc i r.val): ∀ᶠ j in (φ: Filter J), draft Q (V.top j) (V.low j) (2*costCap s*M) (δ/2) (V.hue i) (OPE.away (crop (x j) b) (x j i)):=by
    let X j' := OPE.away (crop (x j') b) (x j' i); have hf(j k:I')(hj:j≠k): ∀ᶠ n in φ,
       ‖X n j-X n k‖≤ 2*costCap s*M*V.top n ((Q).gap j k)∧ δ/2*V.low n ((Q).gap j k)< ‖X n j-X n k‖:=by
          let u:= s.common (s.parent j.val) (s.parent k.val); have hh := Subtype.val_injective.ne hj; have hw:= Fork.link (lived ht (ha j.property) (ha k.property) hh) (lived ht (ha k.property) (ha j.property) hh.symm); have hu:u∈ s.tower o:=inherits (hp _ j.property) (hp _ k.property); have hz:=h.keep
          filter_upwards [Portrait.near h V hu hw.left.1,Portrait.near h V hu hw.swap.left.1,h.space,V.close u hu] with n h1 h2 h3 h4; let μ:=((Q).gap j k); have hz' : ‖X n j-X n k‖=‖x n j.val - x n k.val‖:= by rw [show X n j - X n k=(x n j.val-x n i)-(x n k.val-x n i) from rfl, sub_sub_sub_cancel_right]
          have hξ:(Q).gap j k=V.hue u:=rfl; rw [hz',hξ]; refine ⟨?_,?_⟩
          · have he:=c_dist_point (x n j.val) (x n u) (x n k.val); rw [norm_sub_rev (x n u)] at he; linarith only [h1,h2,he] -- order
          exact lt_of_lt_of_le ((mul_le_mul_of_nonneg_left h4.1 (half_pos hz|>.le)).trans_lt (mul_lt_mul_of_pos_right (half_lt_self hz) (h3.sizes.allowed _ (tower_at.mp hu).1))) (h3.spread _ _ _ hw)
    filter_upwards [eventually_all.mpr (fun j=>eventually_all.mpr fun k=>eventually_all.mpr (hf j k)), reach h V hy hx] with j hj hk; exact ⟨fun i k hi=> (hj i k hi).1,fun i k hi=>(hj i k hi).2,hk⟩
-- Sign case analog for same subset config.W focus iff ancestor.Also age match.Strike only on terminal.
lemma reserve (hi:i∈ a) (hy:r.val∈ s.inputs a i) (he:j∈b) (hx:j∉s.inputs a i):
    s.Anc (s.common (s.parent r.val) (s.parent j)) (s.parent i):=by
    let k:= s.common (s.parent r.val) (s.parent j); have hr:=s.span (s.parent r.val) (s.parent j); have hw : ¬s.Anc i k:= fun h'=> hx (mem_filter.mpr ⟨ha he, h'.joins (hr.2.1.joins (Anc.step s j))⟩); have hb:= inside ht hi hy
    exact ((hb.compare hr.1).resolve_left hw).back (fun hz=> hw (hz ▸ Anc.same ..))
include ha ht -- v2
lemma mainOffer (hi:i∈ a)(hv:s.Anc o (s.parent i)) (hy:r.val∈ s.inputs a i) (hz:V.hue (s.parent i) < V.hue i) (u:I') : u ∈ (Q).focus (V.hue i) ↔ u.val∈ s.inputs a i:=by
    have ht': i∈ s.tower o:= tower_at.mpr ⟨ht.included hi,hv.joins (Anc.step s i)⟩
    let j:= u.val; let k:= s.common (s.parent r.val) (s.parent j); have hw:= inherits (hp _ r.property) (hp _ u.property)
    have hk:(Q).gap (Q).star u= V.hue k:=rfl -- `Q` notation raw macro dot??
    rw [(Q).on_focus]; constructor
    · rintro (hQ|hQ)
      · rw [← hQ]; exact hy
      by_contra H'; exact hz.not_ge (hQ.trans (hk.le.trans (adhere h V hw (tower_at.mpr ⟨s.inward i,hv⟩) (reserve (b:=b) ht ha r hi hy u.property H')))) -- order
    intro Hu; exact Or.inr (hk.symm ▸ (adhere h V ht' hw ((s.span _ _).2.2 i (inside ht hi hy) (inside ht hi Hu))))
lemma selected (hi:i∈a)(he:s.Border a i)(hv:s.Anc o (s.parent i))(hy:r.val∈s.inputs a i)(hz:V.hue (s.parent i)<V.hue i): (Q).Strike (V.hue i) (V.hue (s.parent i)):=by
    have hh (u:I')(hp : u.val ∈ s.inputs a i) : s.parent u.val = i:= ((s.related ..).1 (show u.val∈ s.kids i from next_leaves he hi ▸ hp)).2
    have hw := mainOffer h V ht ha r hp hi hv hy hz
    refine ⟨hz,congr_arg V.hue (hh r hy),fun u hu=> congr_arg V.hue (hh u ((hw u).1 hu)),fun u hu=>?_⟩
    rw [(Q).flip]; exact adhere h V (inherits (hp _ r.property) (hp _ u.property)) (tower_at.mpr ⟨s.inward i,hv⟩) (reserve ht ha r hi hy u.property (fun hz=>hu ((hw u).2 hz))) -- order
end Portrait
end YM.OPE.Arboreal
