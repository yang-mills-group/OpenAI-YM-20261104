import YM.Frontier6.Forest.Syntax.Activity

/-! Not formal quotient rewrite: rejected branch projections retain the same
exact nested fit of the phase-coherent detector. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I:Type}{T:Fareway I}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book} (K:Final C H S) (d:ℕ) (x:E4) (A:Spelling S)
lemma all_congr : Congr K (all K x d A) (letter S x ⟨d,absorb K x d A⟩):= deck_at K _ _ _
lemma part_congr : Congr K (part K x d A) (letter S x ⟨d,pitch K x d A⟩):= by
   unfold part pitch; rw [face_appears]; exact suit_reads K x _ _
lemma acts_all {P:Set E4}(he:x∈P): Acts P (all K x d A):= Acts.deck K he _ _
lemma acts_part {P:Set E4}(he:x∈P): Acts P (part K x d A):= Acts.suit K he _ _
lemma visible_all (e:ℕ): Visible K x e (all K x d A):= (apo_letter K x e ⟨d,absorb K x d A⟩).cf K ((all_congr K d x A).symm K)
lemma visible_part (e:ℕ): Visible K x e (part K x d A):= (apo_letter K x e ⟨d,pitch K x d A⟩).cf K ((part_congr K d x A).symm K)
lemma absorb_all : absorb K x d (all K x d A)=absorb K x d A:=(absorbed K d x (all_congr K d x A)).trans (absorb_letter ..)
lemma absorb_kills (h: Visible K x d A) : absorb K x d (reject K x d A)=0:= by rw [reject,absorb_sub K h (visible_all ..), absorb_all,sub_self]
lemma absorb_killed (h:Visible K x d A){e:ℕ}(he:e ≤ d): absorb K x e (reject K x d A)=0:=by rw [←absorb_lower K he (show Visible K x d (reject K x d A) from h.sub K (visible_all ..)),absorb_kills K _ _ _ h,map_zero]
lemma all_from_parts (h:Visible K x d A): all K x d A=∑ i:Fin (d+1),part K x i A:=by
    unfold all;rw [deck_eq]; refine Finset.sum_congr rfl (fun i _=>?_); unfold part pitch; rw [face_appears]; exact congr_arg _ (absorb_lower K (show (i:ℕ) ≤ d from Nat.lt_add_one_iff.mp i.isLt) h)
lemma letter_all {e:ℕ}(v:S.Field e)(he:e≤d): Congr K (all K x d (letter S x ⟨e,v⟩)) (letter S x ⟨e,v⟩):=by
   have hy:= letter_cap K x _ v he; refine (all_congr K d x _).trans K ?_ -- test .. after K?
   rw [absorbed K d x hy, absorb_letter]; exact hy.symm K
lemma all_plus {B:Spelling S} (h:Visible K x d A)(he:Visible K x d B): all K x d (A+B)=all K x d A+all K x d B:=by unfold all; rw [absorb_plus K h he,map_add]
lemma all_scal (p:ℂ)(h:Visible K x d A): all K x d (p • A)=p • all K x d A:=by unfold all; rw [absorb_scal K h,map_smul]
lemma all_void : all K x d 0=0:=by unfold all; rw [absorb_zero,map_zero]
lemma pitch_plus {B:Spelling S}(h:Visible K x d A)(he:Visible K x d B): pitch K x d (A+B)=pitch K x d A+pitch K x d B:=by unfold pitch; rw [absorb_plus K h he,map_add]
lemma pitch_sub {B:Spelling S}(h:Visible K x d A)(he:Visible K x d B): pitch K x d (A-B)=pitch K x d A-pitch K x d B:=by unfold pitch; rw [absorb_sub K h he,map_sub]
lemma pitch_scal (p:ℂ)(h:Visible K x d A): pitch K x d (p • A)=p • pitch K x d A:=by unfold pitch; rw [absorb_scal K h,map_smul]
lemma pitch_void : pitch K x d 0=0:=by unfold pitch; rw [absorb_zero,map_zero]

abbrev Art (S:Table C.book)(I:Type) := I→ Spelling S
abbrev Intact (T:Fareway I)(P:Fabric I)(A:Art S I):Prop:=∀ᶠ i in T.via, Acts (P i) (A i)
variable {x:I→ E4} {P Q:Fabric I} {f g:Art S I}
lemma Intact.weaker (h:Intact T P f)(he: Extends T Q P): Intact T Q f:= (h.and he).mono fun _ hi=> hi.1.weaker hi.2
lemma Intact.product (h:Intact T P f)(he: Intact T Q g){b:ℝ}(hb:Cross T P Q b): Intact T (P⊔Q) (f*g):= ((h.and he).and hb.disjoint).mono fun _ hi=>hi.1.1.mul hi.1.2 hi.2
lemma Intact.plus (h:Intact T P f)(he:Intact T P g): Intact T P (f+g):= (h.and he).mono fun _ hi=> hi.1.add hi.2
lemma lights (hc:Forest.Centered T P x K d) (h:Intact T P f): ∀ᶠ i in T.via, Visible K (x i) d (f i):=by
    obtain ⟨r,hr,hp,hc⟩:= hc; exact (h.and hc).mono fun _ hi=> hi.1.visible K (hr.down K le_rfl (by linarith : r≤2*r)) hi.2
end YM.Frontier6.Forest
