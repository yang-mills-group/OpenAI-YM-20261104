import YM.RegulatorIR.Step.Batch
import YM.RegulatorIR.Uniform.Spines

/-! Predecessor comparisons in the actual log-rank step. All bounds are on
kernels after folding representatives, with upper-rank contraction cost in the
same moment norm required for arbitrary propagation. The *size* of that
repeated component is still a Ward/geometry obligation, separate. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform.Batch
open Budget Budget.Packet Budget.Tuple Budget.Deck Budget.Layer Budget.Tariff Diagram Function Step Step.GridStep Post
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type} {X Y U V:W→Type} (F:Batch X Y U V) {L:Meter W} {l:W→ℝ} {hl:∀ w,0<l w}

abbrev lineL (w:W):=(F.grid w).line
abbrev rails w:=(F.grid w).addon
abbrev forecast w:=(F.grid w).driftL
abbrev room (w:W):= combine (F.fine w) (F.coarse w)

def kick {j:ℕ}(T:(w:W)→Packet (U w) j)(w): Packet (V w) j:= (F.grid w).pullJ (offer (firstChannel (F.fine w) (F.coarse w)).tile (T w))
def bump {j:ℕ}(T:(w:W)→Packet (X w) j)(w): Packet (Y w) j := (F.grid w).pullI (offer (firstChannel (F.fine w) (F.coarse w)).native (T w))

variable {u b e r:ℕ}(T:(w:W)→ Orders (X w))(S:(w:W)→ Orders (U w))
lemma lock (w:W) (h: (F.fine w).Ready (T w e r))(hh:(F.room w).Ready (F.rails w e r)): (F.room w).Ready ((F.grid w).jVac (T w) e r):= Deck.ready_add _ (Channel.offer_valid (firstChannel ..) h) hh
lemma opening
 (H:Workday L ((F.incoming l hl).cone u) fun w=>T w e r)(hF:Workday L ((F.insideRoom l hl).cone u) fun w=> F.rails w e r) :
    (F.insideRoom l hl).vgap (fun w=>(F.grid w).jVac (T w) e r) (fun w=>(F.grid w).jOrb (S w) e r)= fun w=>offer (firstChannel (F.fine w) (F.coarse w)).tile ((F.incoming l hl).vgap (fun w=>T w e r) (fun w=>S w e r) w):=by
 obtain ⟨c,hc,H⟩:= F.fine_bill H; obtain ⟨d,hd,G⟩:= hF
 ext1 w; let A:= F.fine w; let B:=F.coarse w; let Y:=firstChannel A B; let P:=combine A B
 change (offer Y.tile (S w e r)+P.deckSum _) - P.deckSum (offer Y.native _+ F.rails w e r)= _
 rw [Deck.desk_sup _ (H w) (hc.cost w) (G w) (hd.cost w), Channel.offer_project]; unfold Post.vgap; rw [offer_diff]; abel

section Earnings
variable [∀ w,Fintype (U w)] [∀ w,Fintype (V w)]
variable
  (hk:Beam L ((F.insideRoom l hl).cone (u+b+(u+b))) (F.lineL))
  (hp:Poly L ((F.insideRoom l hl).weight b))
  (hΓ:∀ w, Layer.Sym (F.room w) (F.room w) (F.lineL w))
  (hB:∀ w i j,i≤e → (F.room w).Ready (F.rails w i j))
  (hx:∀ w i j,i≤e→(F.fine w).Ready (T w i j))
  (hz:∀ w,Vacuum (F.rails w))(hv:∀ w,Vacuum (T w))(hh:∀ w,Vacuum (S w))
  (ho:∀ i≤e,∀ j,Workday L ((F.incoming l hl).cone (u+b+(u+b))) fun w=>T w i j)
  (hg:∀ i≤e,∀ j,Workday L ((F.insideRoom l hl).cone (u+b+(u+b))) fun w=> F.rails w i j)
  (hW:∀ i j, Earlier e r i j → 0<j → Claim L ((F.incoming l hl).pear u) 1 ((F.incoming l hl).vgap (fun w=>T w i j) (fun w=> S w i j)))
include hk hp hΓ hB hx hz hv hh ho hg hW
lemma coal (k i j:ℕ)(ht:Touch e r i j) (hm:0<j)(h':k=0 → Earlier e r i j) :
    Claim L ((F.insideRoom l hl).pear u) 1 ((F.insideRoom l hl).vgap (fun w=> logHeat (F.grid w).line ((F.grid w).jVac (T w)) false k i j) (fun w=>logHeat (F.grid w).layer ((F.grid w).jOrb (S w)) true k i j)):=by
 let D:= F.insideRoom l hl
 let V:= fun w=>(F.grid w).jVac (T w); let Z:=fun w=>(F.grid w).jOrb (S w)
 refine part_vac (F.lineL) V Z hk hp hΓ (fun w=>joint_vac_shape _ (hv w) (hz w)) (fun w=>joint_fold_shape _ (hh w) (hz w)) (fun i he j=> F.fine_work (ho _ he j) (hg _ he j)) (fun w i hi j=>F.lock T w (hx w i j hi) (hB w i j hi)) ?_ k i j ht hm h'
 intro p q he hf
 have hq:p≤e := by unfold Earlier at he;omega
 rw [show Post.vgap (F.insideRoom l hl) _ _=_ from F.opening T S (ho _ hq q) (hg _ hq q)]
 exact F.orb_bill (hW p q he hf)
lemma assembly (hM:Beam L ((F.insideRoom l hl).cone u) F.forecast)(hN:∀ w,Layer.Sym (F.room w) (F.room w) (F.forecast w))(hr:0<r) :
  Claim L ((F.outgoing l hl).pear u) 1 fun w=> (F.outgoing l hl).vgap (fun w=>(F.grid w).pure (T w) e r) (fun w=>(F.grid w).common (S w) e r) w - F.kick ((F.incoming l hl).vgap (fun w=>T w e r) (fun w=>S w e r)) w:=by
 let D:= F.insideRoom l hl
 let T':= fun w=>(F.grid w).jVac (T w); let S':=fun w=>(F.grid w).jOrb (S w)
 let X w:= logHeat (F.lineL w) (T' w) false
 let Y w:= logHeat (F.grid w).layer (S' w) true
 have HH (n:ℕ) : Workday L (D.cone u) (fun w=>X w n e r):= D.writes (Workday.hot (e:=e) (A:=D.cone (u+b+(u+b))) (V:=T') (fun i hi j=> F.fine_work (ho i hi j) (hg i hi j)) hk _ _ _ _ le_rfl) (by omega)
 have H w k : (D.deck w).Ready (X w k e r):=heat_uses _ _ (T' w) (hΓ w) (fun p (hp:p≤e) j=> F.lock T w (hx w _ _ hp) (hB w _ _ hp)) _ _ _ _ le_rfl
 have hx' : ¬r=0:=Nat.ne_of_gt hr
 have he:= rolls (U:=X) (F:=Y) D hN hM e r (fun e=>3*e) HH H (fun k hkz=>F.coal T S hk hp hΓ hB hx hz hv hh ho hg hW k e r (Or.inr ⟨rfl,le_rfl⟩) hr (fun hv=> False.elim (Nat.ne_of_gt hkz hv)))
 convert F.out_bill he using 1
 ext1 w; let A:= F.fine w; let B:=F.coarse w; let P:= combine A B; let t:=lastChannel A B; let f:= firstChannel A B
 change (F.grid w).common _ e r - B.deckSum ((F.grid w).pure _ e r) - _ = _
 rw [GridStep.pure,common,if_neg hx', if_neg hx']
 change crop t.tile _- B.deckSum (crop t.native _) - crop t.tile _ = crop t.tile _
 rw [Channel.crop_project t _,crop_diff,crop_diff]
 have hp' : D.vgap (fun w=>X w 0 e r) (fun w=>Y w 0 e r) w =offer f.tile ((F.incoming l hl).vgap (fun w=>T w e r) (fun w=>S w e r) w):=by
    unfold X Y; simp_rw [logHeat_first]; simp only [hx',false_and,↓reduceIte]; exact congr_fun (F.opening T S (ho e le_rfl r) (hg e le_rfl r)) w
 rw [← hp']; rfl
end Earnings
end YM.RegulatorIR.Uniform.Batch
