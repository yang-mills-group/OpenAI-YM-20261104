import YM.RegulatorIR.Step.Comparison

/-! Companion cover-soft transmission away from the top. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform.Batch
open Budget Budget.Packet Budget.Tuple Budget.Deck Budget.Layer Budget.Tariff Diagram Function Step Step.GridStep Post
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type} {X Y U V:W→Type} (F:Batch X Y U V) {L:Meter W} {l:W→ℝ} {hl:∀ w,0<l w}
variable {u e r:ℕ}(T C:(w:W)→ Orders (X w)) {v:W→ℝ≥0∞} {x:W→Room}

theorem beam_mark (hH:∀ w,Vacuum ((F.grid w).jVac (T w)))(hr:∀ i≤e,∀ j,Workday L ((F.insideRoom l hl).cone u) fun w=> (F.grid w).jVac (T w) i j)
   (h:Beam L ((F.insideRoom l hl).cone u) (F.lineL))
   (hM:Beam L ((F.insideRoom l hl).cone u) F.forecast)(ht:∀ i j,Earlier e r i j →0<j → Claim L ((F.incoming l hl).rooted x u) v (fun w=>C w i j))(hv:∀ w,v w ≠ ⊤)
   (hS:∀ w,markQ ((F.incoming l hl).rooted x u w) (C w e r)≠⊤)
   (m:ℕ): Claim L ((F.outgoing l hl).rooted x u) v fun w=>(F.grid w).each m (T w) (C w) e r - bump F (fun w=> C w e r) w:=by
 let G:= fun w=>∑ i∈Finset.range (m+3*e), F.primary T C w (i+1) e r
 have hG: Claim L ((F.insideRoom l hl).rooted x u) v G := Claim.sum (fun i w=> F.primary T C w (i+1) e r) _ (fun i _=> F.issue T C h hr hH ht (i+1) (by omega))
 have hz:= hG.draft_budget hM
 convert F.out_post hz using 1
 ext1 w; let A:=F.grid w; let B:=firstChannel (F.fine w) (F.coarse w); let P:=F.insideRoom l hl; let Q:= (F.incoming l hl).rooted x u w
 change crop (lastChannel (F.fine w) (F.coarse w)).native (draft (F.forecast w) (heated (fun e=>m+3*e) (F.primary T C w) e r))- _=_
 rw [first_payment, show F.primary T C w 0 e r= offer B.native (C w e r) by unfold primary; rw [markHeat_first]]
 obtain ⟨f,hf,H⟩:=hM
 have he: markQ (P.rooted x u w) (offer B.native (C w e r)) ≠ ⊤:= by
    let L:= Premium.rooted (native (l w) (hl w) u) (x w)
    let J:=combine (F.fine w) (F.coarse w)
    have hh:= mark_offer B.native (B:=L) (T:=C w e r) (y:=J.pos); rw [Channel.native_paid] at hh
    exact ne_top_of_le_ne_top (hS w) hh
 rw [draft_split (F.forecast w) _ (G w) (P.rooted x u w) (H w).2 he (Claim.cost hG w (hv w)) (hf.cost w),crop_plus]
 exact add_sub_cancel_left ..
end YM.RegulatorIR.Uniform.Batch
