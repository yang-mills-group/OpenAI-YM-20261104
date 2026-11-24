import YM.Trace.Physicalv2.GermStep

/-!
A one-root extension of the fitted graph while keeping the same represented
vacuum. For an inhomogeneous term *already* represented at weight r and with
raw coordinate of size ≤r, one can pay ~4/ stock factors and use the shared
library to make the intrinsic projection vanish. The estimate is on exact
densities, not equality of addresses. The winding correction is part of the
fit, not ignored. Here every `value` includes the current vacuum density and
is in the engineering convention used by `blast`, not a conditional quotient.
-/
noncomputable section
namespace YM.Trace.Physical.GermGraph
open Function Set Filter Labels Lattice Wilson RG Source Analysis Next.Foundations
open Push.Local ProjectorNext.Equivariance MeasureTheory Extra.Histories Relay
open Germ Bid Work.G08 PhysicalNext.Repeat.Lotus YM.MergeProof Motion
open PhysicalNext.Repeat.Legato.Bandage
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2450000
set_option synthInstance.maxHeartbeats 125000
set_option quotPrecheck false
set_option warningAsError false
set_option maxRecDepth 3600
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {G:Gauge}(C:Family G)(d:ℕ)
local notation "F" => C.labels.level d
local notation "tally" => (C.labels.level d).coeffSize
variable {C d} {N i p:ℕ}

lemma count_neg (v:C.label d):tally (-v)=tally v:=by simp [Frame.coeffSize]
lemma count_sub (x y:C.label d):tally (x-y) ≤ tally x+tally y := by rw [sub_eq_add_neg, ←count_neg y]; exact Size.add F _ _
lemma control_page (H:C.Makes)(h:Opened C d i p)(hi:i≤N)(q:Coefficient F (C.side i p)) {r:ℝ}(hr:reads d N p i q r)(hx:tally q.x ≤ r): tally (page d p i q) ≤ 2*r:=by
   have hz₀ : page d p i q=q.x+(page d p i q-q.x):=(add_sub_cancel q.x _).symm
   have hn:= Size.add F q.x (page d p i q-q.x)
   have he:=measured_diff d N p i H h.post hi hr
   have hr':=le_trans (size_nonneg F q.x) hx
   rw [hz₀]
   have hz:=mul_le_mul_of_nonneg_right (le_trans (smaller d p h) (by norm_num: (1:ℝ)/4 ≤ 1)) hr'
   exact le_trans hn (by linarith)
lemma negative_cal (H:C.Makes)(h:Opened C d i p)(hi:i ≤ N)(x:C.label d) : calValues (C:=C) d N p i (-x)+calValues d N p i x = 0:= by rw [←cal_add d N p i H h.post hi, neg_add_cancel,zero_cal d N p i H h.post hi]
lemma fresh_split0 (H:C.Makes)(h:Opened C d i p)(hi:i≤N)(q:Coefficient F (C.side i p)) {r:ℝ}(hr:reads d N p i q r):
   ∃ (s:Coefficient F (C.side i p))(x:C.label d), reads d N p i s (r+(2* stock C i)*tally (page d p i q)) ∧ page d p i s=0 ∧ value (C:=C) d N p i q=value d N p i s+calValues d N p i x ∧ fitting d N p i H h hi x = page d p i q := by
   let Q:=fitting d N p i H h hi
   let x:=Q.symm (page d p i q)
   let l:=(C.factory d N p).entries i (-x)
   let s:=beside q l
   have hv : Q x=page d p i q:=Q.apply_symm_apply _
   have he:=graph_cost d N p i H h hi (-x)
   have hs: tally (page d p i q)=tally (Q (-x)):= by change tally (page d p i q)=_; rw [map_neg, count_neg, hv];
   rw [←hs] at he
   obtain ⟨hF,hR⟩:=presentation hr.1 hr.2 he.1 he.2
   refine ⟨s,x,⟨hF,hR⟩,?_,?_,hv⟩
   · rw [show s=beside q l from rfl, addPage d N p i q l H h.post hi hr he,show page d p i l=(fitting d N p i H h hi) (-x) from rfl,map_neg,hv,add_neg_cancel]
   · rw [show value d N p i s=value d N p i q+value d N p i l from plus (H.wilson.represents _ _ _ hi|>.good) hr.2 he.2 (C.localSection d), add_assoc]
     -- calc? should use add_assoc not ←
     rw [show value d N p i l=calValues d N p i (-x) from rfl,negative_cal H h hi,add_zero]
lemma fresh_split (H:C.Makes)(h:Opened C d i p)(hi:i ≤ N)(q:Coefficient F (C.side i p)) {r:ℝ}(hr: reads d N p i q r)(hx:tally q.x ≤ r) : ∃ s: Coefficient F (C.side i p),∃ x:C.label d,
     reads d N p i s ((1+4*stock C i)*r) ∧ page d p i s = 0 ∧ value (C:=C) d N p i q=value d N p i s+ calValues d N p i x ∧ fitting d N p i H h hi x = page d p i q ∧ tally (fitting d N p i H h hi x) ≤ 2*r:=by
     obtain ⟨s,x,hR,h₀,hv,hQ⟩:=fresh_split0 H h hi q hr
     have hz:=control_page H h hi q hr hx
     have hc:= stage C i|>.columns_ge
     have htol:=mul_le_mul_of_nonneg_left hz (show 0≤2*stock C i by dsimp [stock];linarith)
     refine ⟨s,x,⟨hR.1,rem_increase d hR.2 (by linarith)⟩,h₀,hv,hQ, hQ ▸ hz⟩
lemma same_page (H:C.Makes)(hi:i≤ N)(hr:C.ref d ≤ i){q s:Coefficient F (C.side i p)}{a b:ℝ}(hq:reads d N p i q a)(hs:reads d N p i s b)(hf : value (C:=C) d N p i q =ᶠ[𝓝 1] value d N p i s) : page d p i q=page d p i s :=by
    have hv: (C.path.rep N p i).p=plank C i:=(H.wilson.represents N p i hi).vac
    unfold page; rw [←hv]; exact Germ.intrinsic_at F C.params (C.localSection d) (H.sections d) 0 (H.places d i p hr) (dimensions d N p i H hr hi).1 (dimensions d N p i H hr hi).2 (sections_visit H hr 0) _ _ hq.1 hs.1 ⟨_,_,hq.2⟩ ⟨_,_,hs.2⟩ hf
lemma forget_page (H:C.Makes)(h:Opened C d i p)(hi:i≤N){s q:Coefficient F (C.side i p)}{a b:ℝ}(hs:reads d N p i s a)(hzero:page d p i s=0){y:C.label d}(hq:reads d N p i q b)(he:value (C:=C) d N p i q =ᶠ[𝓝 1] value d N p i s + calValues d N p i y) : page d p i q=fitting d N p i H h hi y := by
   let u:= (C.factory d N p).entries i y
   let v:=beside s u
   have ht:=entryOk d N p i H h.post hi y
   obtain ⟨hF,hR⟩:=presentation hs.1 hs.2 ht.1 ht.2
   have heq :value d N p i s + calValues d N p i y=value d N p i v := by unfold v value calValues; rw [plus (H.wilson.represents _ _ _ hi|>.good) hs.2 ht.2 (C.localSection d)]
   have hv :=same_page H hi h.post hq (show reads d N p i v _ from ⟨hF,hR⟩) (he.trans (EventuallyEq.of_eq heq))
   rw [hv]; unfold v; rw [addPage d N p i s u H h.post hi hs ht, hzero,zero_add]; exact rfl
end YM.Trace.Physical.GermGraph
