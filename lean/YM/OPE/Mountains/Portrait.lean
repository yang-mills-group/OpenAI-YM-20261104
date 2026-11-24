import YM.OPE.Mountains.Layer
import YM.OPE.Trees.Regime
/-!
# Cloaking any sub-hierarchy of geometries

Only the given hierarchy's **cost** is global. Assign layers relative
any upper internal. Include its scale in the account, this setup works
on arbitrary contractions or subsets of the frontier below it. `Portrait`
marks costs within each supplied window along one ultrafilter. Top scale
may be wider than the offered internal R_o, at most polynomial more. Then
we charge the actual R_o factor also in subtree and redacted estimates.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Filter Finset Real OPE.Log Mountain
open scoped Classical Topology BigOperators
variable {I J:Type}[Fintype I] {s:Arboreal I} {φ:Ultrafilter J} {t:I→ℝ} {x:J→I→ E4}{R:J→I→ℝ}{M δ:ℝ}{i j k l o:I}
local notation "T!" => (fun a=>s.fullLife (R a))
def tower (s:Arboreal I)(i:I):= s.zones.filter (s.Anc i)
lemma tower_at : j∈ s.tower i ↔ j∈ s.zones∧ s.Anc i j:= mem_filter
-- L local lifetimes,T! notation avoid syntax declaration across var
structure Palette (f:Filter J)(T:J→ℝ)(A: Finset I)(R:J→I→ℝ) where
    hue : I→ℕ
    cost : ℕ→ℝ
    top : J→ℕ→ℝ
    low : J→ℕ→ℝ
    limit : ℕ
    fair : Ranking A (fun i j=> Reward f T (fun k=>R k i) (fun k=> R k j)) hue limit
    schedule : Trunk.Border f T limit top low cost
    close i : i∈A→ ∀ᶠ j in f,low j (hue i)≤ R j i ∧ R j i ≤ top j (hue i)
abbrev Portrait (s:Arboreal I)(φ:Ultrafilter J)(R:J→I→ℝ)(i:I):Type:= Palette (φ:Filter J) (fun i=> s.fullLife (R i)) (s.tower i) R
lemma paints (h:s.Coterie (φ:Filter J) t M δ x R) (hx:o∈s.zones) : Nonempty (Portrait s φ R o):=by
    let V:=s.tower o; let T := fun i=> s.fullLife (R i); let F i j:= R j i; let H:= fun i j=> Reward (φ:Filter J) T (F i) (F j); have he(i)(hi:i∈V) : i∈ s.zones:= (tower_at.mp hi).1; have hu:= h.tracked; have hh(i)(hi:i∈V) : ∀ᶠ j in φ,0 < F i j:= (hu.rates i (he i hi)).pos; have hV : V.Nonempty:=⟨o,tower_at.mpr ⟨hx,Anc.same s o⟩⟩
    obtain ⟨v,m,hv⟩ := ranked (R:=H) hV (fun i hi j hj=> Reward.bid h.time (hh i hi) (hh j hj)) (fun _ _ j hj _ _ => Reward.join (hh j hj))
    let A i:= V.filter fun j=>v j=i; have hA(i)(hi:i ≤ m) : (A i).Nonempty:=by obtain ⟨t,ht,hT⟩:= hv.realizes i hi; exact ⟨t, mem_filter.mpr ⟨ht,hT⟩⟩; -- notation ≤m tokenizer
    choose l hl hL using fun i (hi:i ≤ m)=> Reward.minOffer (f:=φ) R (hA i hi); choose u hu' hU using fun i (hi:i ≤ m)=> Reward.maxOffer (f:=φ) R (hA i hi)
    let lo i:= if h:i ≤ m then l i h else o; let up i:= if h:i ≤ m then u i h else o
    have hl₀ i (hi:i ≤ m): lo i = l i hi:= dif_pos hi; have hu₀ i (hi:i ≤ m): up i=u i hi:= dif_pos hi
    have hl' i (hi:i ≤ m): lo i ∈ V ∧ v (lo i)=i := by rw [hl₀ i hi]; exact (mem_filter.mp (hl i hi))
    have hu'' i (hi:i ≤ m): up i∈ V∧ v (up i)=i:= by rw [hu₀ i hi]; exact mem_filter.mp (hu' i hi) -- semicolon bug
    have hf i (hi:i ≤ m): ∀ᶠ j in φ,∀ k∈A i,F (lo i) j ≤ F k j∧ F k j ≤ F (up i) j :=by filter_upwards [hL i hi, hU i hi] with k hk he j hj; rw [hl₀ i hi,hu₀ i hi]; exact ⟨hk j hj,he j hj⟩
    refine ⟨{ hue:=v, cost:=fun j=> t (lo j), top:=fun i t=> F (up t) i, low:=fun i t=> F (lo t) i, limit:=m, fair:=hv, schedule:=?_, close:=fun i hi=> ((hf _ (hv.bounded i hi)).mono (fun j hu=> hu i (mem_filter.mpr ⟨hi,rfl⟩))) }⟩
    constructor
    · exact h.time
    · intro i hi; exact hu.bounds _ (he _ (hl' i hi).1)
    · intro i hi; exact (tendsto_nhdsWithin_iff.mp (h.pixels (he _ (hu'' i hi).1))).1
    · intro i hi; exact (hu.rates _ (he _ (hl' i hi).1))
    · intro i hi; obtain ⟨hx,hP⟩:= hl' i hi; obtain ⟨hy,hQ⟩:= hu'' i hi; exact ⟨((hh _ hx).and (hh _ hy)).mono fun _ hi=> div_pos hi.2 hi.1, (hv.compares _ _ hx hy).2 ((hP.trans hQ.symm).le), ((show Wallet _ _ _ from (hv.compares _ _ hy hx).2 ((hQ.trans hP.symm).le))).congr (Eventually.of_forall fun i=> (inv_div ..).symm)⟩
    · intro i hi; exact (hf i hi).mono fun k hk=> (hk (lo i) (mem_filter.mpr (hl' i hi))).2
    intro i hi p; have hP:=hl' i hi.le; have hQ:=hu'' (i+1) hi
    apply Reward.beats h.time (hh _ hP.1) (hh _ hQ.1); intro hc; apply i.lt_succ_self.not_ge; exact hQ.2.symm.trans_le (((hv.compares _ _ hQ.1 hP.1).1 hc).trans hP.2.le)

namespace Portrait
variable (h:s.Coterie (φ: Filter J) t M δ x R) (V:Portrait s φ R o)
lemma bounded (hi:i∈ s.tower o): V.hue i ≤ V.limit:= V.fair.bounded i hi
include h
lemma budget (hi:i∈ s.tower o) (hj:j∈s.tower o)(hk: V.hue i≤ V.hue j): Reward (φ : Filter J) T! (fun k=>R k i) (fun k=> R k j):= (V.fair.compares _ _ hi hj).2 hk
lemma adhere (hi:i∈ s.tower o)(hj:j∈ s.tower o)(hb:s.Anc i j): V.hue i ≤ V.hue j:= (V.fair.compares _ _ hi hj).1 (Reward.credit h.time (h.tracked.rates i (tower_at.mp hi).1|>.pos) (h.tracked.rates j (tower_at.mp hj).1|>.pos) (h.space.mono fun _ h=> h.sizes.bound hb (tower_at.mp hj).1))
lemma mark (hi:o∈ s.zones): V.hue o=0:=by
    obtain ⟨x,hx,he⟩:= V.fair.realizes 0 (Nat.zero_le _); exact Nat.eq_zero_of_le_zero (he ▸ (adhere h V (mem_filter.mpr ⟨hi,Anc.same s o⟩) hx (tower_at.mp hx).2)) -- order
lemma led (hi:i∈ s.tower o):ValueStamp (φ:Filter J) T! (fun j=> R j i / V.top j (V.hue i)):=by
    let L:= V.hue i; have he:= V.schedule; have hh:= V.bounded hi; have hu:= (he.rates L hh).pos; have hf:= (he.ahead hh).pos; have hp:= (h.tracked.rates _ (tower_at.mp hi).1).pos; have hV:= V.close i hi
    have hY: ∀ᶠ j in φ,0 < R j i/V.top j L:=by filter_upwards [hf,hp] with i he hi using div_pos hi he
    refine ⟨hY, (Wallet.const h.time (1:ℝ)).of_le' hY ((hV.and hf).mono fun i hi=> (div_le_one hi.2).2 hi.1.2), (((he.relative L hh).up).of_le' (hY.mono (fun _ hi=> inv_pos.mpr hi)) ?_)⟩
    filter_upwards [hV,hf,hu] with i hi he hu; rw [inv_div]; exact div_le_div_of_nonneg_left he.le hu hi.1
end Portrait
end YM.OPE.Arboreal
