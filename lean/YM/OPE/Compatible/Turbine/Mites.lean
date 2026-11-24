import YM.OPE.Compatible.Satin.Fold
/-!
# Proper subtree for the glen price. Active nodes restrict. No hypotheses of being terminal needed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal.Trace
open Function Set Filter MeasureTheory Finset
open scoped Topology BigOperators Classical
variable {X I V:Type}[PartialOrder X][OrderBot X][Fintype X](D:Origin X){Q:Finset X}
variable (u:X)
-- use ↑Ici u
abbrev cone := ↥(Set.Ici u)
omit [OrderBot X] [Fintype X] in
include D in
lemma nestle : Origin (cone u):= ⟨fun h hp=> D.path (v:=Subtype.val _) h hp⟩
-- necessary parents
omit [OrderBot X] [Fintype X] in
lemma node_val : (⊥:cone u).val = u:= rfl
lemma par_nest {y: cone u} (h:y≠ ⊥): (par (nestle D u) y).val=par D y.val:=by
    have hp: u < y.val:= bot_lt_iff_ne_bot.2 h -- defeq?
    refine le_antisymm (touch_par D (from_par (nestle D u) h)) ?_ -- annotate
    exact touch_par (nestle D u) (w:=(⟨par D y.val,touch_par D hp⟩: cone u)) (v:=y) (from_par D (bot_lt_iff_ne_bot.mp (lt_of_le_of_lt bot_le hp))) -- arg names
-- couple coincides
lemma join_nest (y z: cone u): (couple (nestle D u) y z).val= couple D y.val z.val:=by
    refine le_antisymm (ancestors_couple D (coupled_left (nestle D u) y z) (coupled_right (nestle D u) y z)) ?_
    let v: cone u:=⟨couple D y.val z.val,ancestors_couple D y.2 z.2⟩; exact ancestors_couple (v:=v) (nestle D u) (coupled_left D ..) (coupled_right D ..)
def partQ (Q:Finset X): Finset (cone u) := univ.filter (fun i=>i.val∈Q)
omit [OrderBot X] in
lemma limb {v:cone u}: v∈ partQ u Q ↔ v.val∈Q:= by simp [partQ]
variable (hu:u ∈ Q)
local notation "X!"=> nestle D u
local notation "P"=> partQ u Q
local notation "Z"=> glen D Q u
include hu
lemma part_crown (h:Crown Q): Crown (partQ u Q):= by
    refine ⟨(limb u).mpr hu,fun x hx=> ?_,fun h1 h2=> (limb u).mpr (h.roots h1 ((limb u).mp h2))⟩
    obtain ⟨y,hy⟩:= heart_mem.mp (h.inner ((limb u).mp hx)); exact heart_mem.mpr ⟨⟨y,(show u ≤ x.val from x.2).trans hy.le⟩,hy⟩
set_option quotPrecheck false
lemma limb_brim (v : cone u) : v∈ brim X! P ↔ v.val ∈ Z :=by
    by_cases hv:v=⊥
    · rw [hv,on_brim]; constructor
      · rintro ⟨_,h,_⟩; exact absurd rfl h
      intro h; exact (((on_brim ..).mp (mem_filter.mp h|>.1)).1 hu).elim
    rw [on_brim, limb, limb,par_nest D u hv]; constructor
    · rintro ⟨h, -, hw⟩; exact mem_filter.mpr ⟨(on_brim ..).2 ⟨h,bot_lt_iff_ne_bot.mp (lt_of_le_of_lt (bot_le (a:=u)) (show u < v.val from (bot_lt_iff_ne_bot (a:=v)).mpr hv)),hw⟩, v.2⟩
    intro h; obtain ⟨hz,-⟩ := mem_filter.mp h; rw [on_brim] at hz; exact ⟨hz.1,hv,hz.2.2⟩
def home : ↥(brim X! P)≃ ↥Z where
    toFun i:=⟨i.val.val,(limb_brim D u hu _).mp i.2⟩
    invFun i:= ⟨⟨i.val,(mem_filter.mp i.2|>.2)⟩,(limb_brim D u hu _).mpr i.2⟩
    left_inv _:=rfl
    right_inv _:=rfl
lemma all_nest (v:cone u) (hv:v∈allUp X! P): v.val∈ allUp D Q:=by
    rcases (@Finset.mem_union _ (fun _ _=>Classical.propDecidable _) _ _ _).mp hv with h|h
    exact Finset.mem_union_left _ ((limb u).mp h)
    exact Finset.mem_union_right _ (mem_filter.mp ((limb_brim D u hu v).1 h)|>.1)
variable {ψ:Filter V}{T: V→ℝ}{s:V→ X→ℝ}{η M:ℝ}
variable (Y:Burst D Q ψ T s)
include Y in
lemma below : Burst X! P ψ T (fun i=>s i ∘ Subtype.val):=by
    refine ⟨fun η h=>?_,Y.fronts.mono fun i hi v hv=> hi _ ((limb u).mp hv)⟩; let H:=Y.fresh η h; exact ⟨part_crown u hu H.crowned,H.ray,h,fun v hv=> H.fade _ ((limb u).mp hv),fun v hv=> H.charge _ ((limb u).mp hv),H.dim.mono fun i hi v hv z hz=> hi _ ((limb u).mp hv) _ hz⟩
lemma notch {x:X→E4}{s:X→ℝ}(h:Ridge s η M D Q (away x (x ⊥))): Ridge (s∘ Subtype.val) η M X! P (away (x ∘ Subtype.val) (x u)):=by
   refine ⟨sub_self _,fun y z hy hz h'=> ?_,fun y z hy hz h1 h2=>?_⟩
   · have ht:= h.near y.val z.val ((limb u).mp hy) (all_nest D u hu _ hz) h'; simpa only [away,sub_sub_sub_cancel_right, Function.comp_apply] using ht
   have ht:=h.span y.val z.val (all_nest D u hu _ hy) (all_nest D u hu _ hz) h1 h2; simpa only [away,sub_sub_sub_cancel_right,Function.comp_apply,join_nest D u y z] using ht
-- volume link
open Arcade Allot Pixel
lemma vale_area (x:brim D Q→ℕ)(s:X→ℝ)(b:glen D Q u→ℕ) (hb:∀ i : ↑(glen D Q u),x ⟨i.val,(Finset.mem_filter.mp i.2).1⟩=b i): volume X! P (b∘home D u hu) (s ∘ Subtype.val) = area D x s (cove D Q u):=by
    have hh:= cove_prod D u (fun i:shore D Q u=> s (par D i.val)^x ⟨i.val,(mem_filter.mp i.2).1⟩) (fun i:brim D Q=> s (par D i.val)^x i) (fun i:glen D Q u=>s (par D i.val)^b i) (fun _=>rfl) ?_ |>.1
    · unfold volume area; rw [hh, ← Equiv.prod_comp (home D u hu)]; refine prod_congr rfl fun i _=>?_; dsimp only [Function.comp_apply,home]; rw [par_nest D u ((on_brim ..).mp i.2|>.2.1)]; rfl
    intro i; change s (par D i.val)^x ⟨i.val,_⟩ = _; rw [hb]
end YM.OPE.Arboreal.Trace
