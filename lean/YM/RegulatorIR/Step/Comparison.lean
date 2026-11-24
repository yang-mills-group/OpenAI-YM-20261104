import YM.RegulatorIR.Step.Assembly
import YM.RegulatorIR.Uniform.Leases

/-! Step outputs before gauge-horizontal contraction. Despite treating two
procedures (orb and cover), the marked errors refer to the full marked numerator
reclosed under conditional division on each side. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Uniform.Batch
open Budget Budget.Packet Budget.Tuple Budget.Deck Budget.Layer Budget.Tariff Diagram Function Step Step.GridStep Post
open scoped Topology ENNReal NNReal BigOperators Classical
variable {W:Type} {X Y U V:W→Type} (F:Batch X Y U V) {L:Meter W} {l:W→ℝ} {hl:∀ w,0<l w}

variable {u b q e r:ℕ}(T:(w:W)→ Orders (X w))(S:(w:W)→ Orders (U w))
   (C:(w:W)→Orders (X w)) (G:(w:W)→Orders (U w))
   {s v:W→ℝ≥0∞}{x: W→Room}
-- register radius length l externally (at coarser steps=l_c, finer use ≥1 when position based)
variable
  (K:(w:W)→Layer (X w ⊕ Y w) (X w⊕ Y w))
-- shortcuts
abbrev primary w k:=markHeat (F.grid w).line (logHeat (F.grid w).line ((F.grid w).jVac (T w)) false) (fun i r=>offer (firstChannel (F.fine w) (F.coarse w)).native (C w i r)) k
abbrev paired w k:= markHeat (F.grid w).layer (logHeat (F.grid w).layer ((F.grid w).jOrb (S w)) true) (fun i r=>offer (firstChannel (F.fine w) (F.coarse w)).tile (G w i r)) k

-- cover-only strict work used in proving soft decay and on first joins
lemma issue
  (H:Beam L ((F.insideRoom l hl).cone u) (F.lineL)) (hp:∀ i ≤ e,∀ j,Workday L ((F.insideRoom l hl).cone u) fun w=>(F.grid w).jVac (T w) i j)
  (ht:∀ w, Vacuum ((F.grid w).jVac (T w)))
  (hO:∀ p q, Earlier e r p q → 0<q → Claim L ((F.incoming l hl).rooted x u) s fun w=> C w p q) (k:ℕ)(hk:0<k) : Claim L ((F.insideRoom l hl).rooted x u) s fun w=> F.primary T C w k e r := by
 apply Claim.from_mark _ H ?h ?hv ?hW k e r (Or.inr ⟨rfl, le_rfl⟩) (by exact fun h=> (hk.ne' h).elim)
 case h => exact fun p h i j _=> Workday.hot hp H false j p i h
 case hv=> intro w i r; by_contra! hx; exact lt_irrefl 0 (heated_cap _ _ (ht w) false 0 r i hx).1
 case hW=> exact fun p q he hf=> F.onto_bill (hO _ _ he hf)

section Joint
variable [∀ w,Fintype (U w)] [∀ w,Fintype (V w)]

variable
  {l₀:W→ℝ} {hl₀:∀ w,0<l₀ w} (hmul:l₀≤l)
  (hk:Beam L ((F.insideRoom l₀ hl₀).cone ((u+b+q)+(u+b+q))) (F.lineL))
  (hp:Poly L ((F.insideRoom l₀ hl₀).weight q))
  (hΓ:∀ w, Layer.Sym (F.room w) (F.room w) (F.lineL w))
  (hB:∀ w i j,i≤e → (F.room w).Ready (F.rails w i j))
  (hx:∀ w i j,i≤e→(F.fine w).Ready (T w i j))
  (hz:∀ w,Vacuum (F.rails w))(hV:∀ w,Vacuum (T w))(hh:∀ w,Vacuum (S w))
  (ho:∀ i≤e,∀ j,Workday L ((F.incoming l₀ hl₀).cone ((u+b+q)+(u+b+q))) fun w=>T w i j)
  (hg:∀ i≤e,∀ j,Workday L ((F.insideRoom l₀ hl₀).cone ((u+b+q)+(u+b+q))) fun w=> F.rails w i j)
  (hW:∀ i ≤ e,∀ j, 0<j→ Claim L ((F.incoming l₀ hl₀).pear (u+b)) 1 ((F.incoming l₀ hl₀).vgap (fun w=>T w i j) (fun w=> S w i j)))
  (hT:∀ p ≤ e,∀ r,0<r → Claim L ((F.incoming l hl).rooted x (u+b+b)) s (fun w=> C w p r))
  (hs:∀ w,s w≠⊤) (hv:Carry L v fun w=> s w*((F.insideRoom l hl).toll x b w)⁻¹)
  (hm: ∀ i j, Earlier e r i j → 0<j → Claim L ((F.incoming l hl).anchored x u) v ((F.incoming l hl).agap (fun w=> C w i j) (fun w=> G w i j)))
include hmul hk hp hΓ hB hx hz hV hh ho hg hW hT hs hv hm

lemma seam (k:ℕ)(he:0<k) : Claim L ((F.insideRoom l hl).anchored x u) v ((F.insideRoom l hl).agap (fun w=>F.primary T C w k e r) (fun w=>F.paired S G w k e r)):=by
 let A:=F.insideRoom l hl
 have hK:= A.descent (beam_fewer hl (show (F.insideRoom l₀ hl₀).length ≤ l from hmul) hk) (show (u+b+b)≤(u+b+q)+(u+b+q) by omega)
 let V:=fun w=> logHeat (F.lineL w) ((F.grid w).jVac (T w)) false; let Z:=fun w=> logHeat (F.grid w).layer ((F.grid w).jOrb (S w)) true
 let T' (w:W) : Orders (X w ⊕ Y w):= fun i r=> offer (firstChannel (F.fine w) (F.coarse w)).native (C w i r)
 let S' (w:W) : Orders (U w ⊕ _) := fun i r=> offer (firstChannel (F.fine w) (F.coarse w)).tile (G w i r)
 have hhX w :Vacuum ((F.grid w).jVac (T w)):= joint_vac_shape _ (hV w) (hz w); have hhZ w:Vacuum ((F.grid w).jOrb (S w)):= joint_fold_shape _ (hh w) (hz w)
 apply part_mark (F.lineL) V Z T' S' hK hv hs hΓ ?_ ?_ ?_ ?_ ?_ (fun p he j hi=> F.onto_bill (hT p he j hi)) ?_ k e r (Or.inr ⟨rfl,le_rfl⟩) (fun h=> (he.ne' h).elim)
 · exact fun w k i=> Classical.byContradiction fun h=>lt_irrefl 0 (heated_cap _ _ (hhX w) false _ _ _ h).1
 · exact fun w k i=> Classical.byContradiction fun h=>lt_irrefl 0 (heated_cap _ _ (hhZ w) true _ _ _ h).1
 · intro p hhP r k _; exact A.writes (work_fewer hl (show (F.insideRoom l₀ hl₀).length ≤ l from hmul) (Workday.hot (A:=((F.insideRoom l₀ hl₀).cone _)) (V:=fun w=>(F.grid w).jVac (T w)) (fun p hv j=>F.fine_work (ho p hv j) (hg p hv j)) hk _ _ _ _ hhP)) (by omega)
 · exact fun w i he r k _=> heat_uses _ _ _ (hΓ w) (fun p (hp:p≤e) j=>F.lock T w (hx w _ _ hp) (hB w _ _ hp)) false k i r he
 · intro p he i k ht
   apply fewer hl (show (F.insideRoom l₀ hl₀).length ≤ l from hmul) (coal F T S hk hp hΓ hB hx hz hV hh ho hg (fun i j h hj=>hW i (by unfold Earlier at h;omega) j hj) k p i (r:=0) (by unfold Touch;omega) ht (fun h' => by unfold Earlier; omega))
 intro i j he hv
 convert F.orb_bill_mark (hm i j he hv) using 1;ext1 w
 unfold Post.agap;change offer (firstChannel (F.fine w) (F.coarse w)).tile _ - (combine (F.fine w) (F.coarse w)).scroll (offer _ _) = _
 rw [Channel.offer_scroll]
 rw [offer_diff];rfl

lemma node (hM:Beam L ((F.insideRoom l hl).cone u) F.forecast)(hN:∀ w,Layer.Sym (F.room w) (F.room w) (F.forecast w))(m:ℕ) :
  Claim L ((F.outgoing l hl).anchored x u) v fun w=> (F.outgoing l hl).agap (fun w=>(F.grid w).each m (T w) (C w) e r) (fun w=>(F.grid w).island m (S w) (G w) e r) w - F.kick ((F.incoming l hl).agap (fun w=>C w e r) (fun w=>G w e r)) w:=by
 let P:=F.insideRoom l hl
 have h (i:ℕ) (h:r+i>0): Claim L (P.rooted x u) s (fun w=>F.primary T C w i e r):=by
   by_cases hv:i=0
   · subst i; unfold primary; simp_rw [markHeat_first]; exact P.narrower x (F.onto_bill (hT e le_rfl r (by omega))) (by omega)
   have h₁ := P.descent (k:=u) (beam_fewer hl (show (F.insideRoom l₀ hl₀).length ≤ l from hmul) hk) (by omega)
   apply issue F T C h₁ (fun i he j=> P.writes (work_fewer hl (show (F.insideRoom l₀ hl₀).length ≤ l from hmul) (F.fine_work (ho i he j) (hg i he j))) (by omega)) (fun w=>joint_vac_shape _ (hV w) (hz w)) _ _ (by omega)
   exact fun p q he ht=> (F.incoming l hl).narrower x (hT p (by unfold Earlier at he;omega) q ht) (by omega)
 have H:= rolls_mark (U:=F.primary T C) (F:=F.paired S G) P hN hM e r (fun e=>m+3*e) h hs (F.seam T S C G hmul hk hp hΓ hB hx hz hV hh ho hg hW hT hs hv hm)
 convert F.out_mark H using 1; ext1 w
 let A:=F.fine w; let B:= F.coarse w; let X:=combine A B; let t:=lastChannel A B; let f:= firstChannel A B
 change crop t.tile _-B.scroll (crop t.native _)-crop t.tile _=crop t.tile _
 rw [Channel.crop_scroll t,crop_diff,crop_diff]
 have hh:P.agap (fun w=>F.primary T C w 0 e r) (fun w=>F.paired S G w 0 e r) w=offer f.tile ((F.incoming l hl).agap (fun w=>C w e r) (fun w=>G w e r) w):=by
    unfold Post.agap primary paired; simp_rw [markHeat_first]; change offer f.tile _-X.scroll (offer f.native _)=offer _ (_-A.scroll _)
    rw [f.offer_scroll,offer_diff]
 rw [← hh]; rfl
end Joint
end YM.RegulatorIR.Uniform.Batch
