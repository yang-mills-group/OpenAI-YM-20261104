import YM.OPE.Compatible.Trees.Nest
/-!
# Freedom in postorder even with the fixed heights
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Arboreal
open Function Set Filter Cov Display
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {V:Type} [PartialOrder V][OrderBot V][Fintype V] (E:Origin V)
    {G:Gauge} {C:Family G} {F:Extraction.Order} {S:Table C.book} (U:Spec.Final C F S)
    (s:V→ ℝ) (x:V→ E4) (D:V→ℕ) {P:Finset V}(H:Crown P) (a:Tones U)(p:V→ S.Tag)
variable {w v:V}
omit [Fintype V] [OrderBot V] in
lemma maximal_trim (h: Maximal (·∈ P) v) : trim P v = P.erase v:=by
    ext i; constructor
    · intro ht; obtain ⟨hi,he⟩:= Finset.mem_filter.mp ht; exact Finset.mem_erase.mpr ⟨fun e=>he e.ge,hi⟩
    intro he; obtain ⟨he,hi⟩:=Finset.mem_erase.mp he; exact Finset.mem_filter.mpr ⟨hi, fun e=> he (le_antisymm (h.2 hi e) e)⟩
omit [Fintype V] [OrderBot V] in
lemma one_trim (h: Maximal (·∈ P) v) (hw:Maximal (·∈ P) w)(he: w≠v): Maximal (·∈trim P v) w:=by rw [maximal_trim h]; exact ⟨Finset.mem_erase.mpr ⟨he,hw.1⟩,fun {_} h e=> hw.2 (Finset.mem_of_mem_erase h) e⟩
lemma shoot_wait (h: Maximal (·∈ P) v) (hw:Maximal (·∈ P) w)(he:w≠v)(c:Tones U):
    shoot E U (trim P v) w a s x (paint U v p c)=shoot E U P w a s x p:=by
    unfold shoot; rw [glen_kids E P hw,glen_kids E _ (one_trim h hw he)]; refine congr_arg (fun p=>beam U a (s w) _ p _) (funext fun j=>?_) -- annotations
    have hz:= (kid_mem E).mp j.2; change update p v (title U c) j.val=p j.val; exact update_of_ne (fun (e:j.val=v)=> he (le_antisymm (e ▸ hz.1.le) (hw.2 h.1 (e ▸ hz.1.le))).symm.symm) (title U c) p
-- use a distributed double sum
include H
lemma other_bud (h:v∈ rest P)(ht:Maximal (·∈P) v): nests E U D P a s x p=∑ b∈ shades (facets U) (D v), shoot E U P v b s x p * nests E U D (trim P v) a s x (paint U v p b) :=by
    revert H v p; apply Finset.lt_wf.induction P
    intro P ih H p p' h he -- check v p implicit order
    let w:=bud P (show (rest P).Nonempty from ⟨_,h⟩)
    let Q:=(facets U)
    have hN : (rest P).Nonempty:=⟨_,h⟩; have hw : w ∈ rest P:= bud_mem ..; have hf : Maximal _ w := bud_tip P hN
    by_cases e:w=p'
    · rw [nests,dif_pos hN]; rw [← e]
    have hb:=one_trim hf he (Ne.symm e); have hp:= one_trim he hf e
    rw [nests,dif_pos hN]
    let C (q:V) (b:Tones U):= shoot E U P q b s x p
    let Y:= trim P w; let Z:=trim P p'
    let c (b b':Tones U):= nests E U D (trim Y p') a s x (paint U p' (paint U w p b) b')
    change ∑ b∈ shades Q (D w), C w b * nests E U D Y a s x (paint U w p b)=_
    refine Eq.trans (b:=∑ b∈ shades Q (D w),∑ b'∈ shades Q (D p'), C w b * (C p' b' * c b b')) ?_ ?_
    · refine Finset.sum_congr rfl fun b _=> ?_; rw [ih Y (lighter _ hf.1) (remains _ H ((rest_mem ..).1 hw|>.1)) (v:=p') (paint U w p b) ((rest_mem ..).mpr ⟨((rest_mem ..).1 h|>.1),hb.1⟩) hb,← Finset.mul_sum]
      refine congr_arg (C w b * ·) (Finset.sum_congr rfl fun j _=>?_); exact congr_arg (· * c b j) (shoot_wait E U s x j p hf he (Ne.symm e) b)
    rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun b _=> ?_
    rw [ih Z (lighter _ he.1) (remains _ H ((rest_mem ..).1 h|>.1)) (v:=w) (paint U p' p b) ((rest_mem ..).mpr ⟨((rest_mem ..).1 hw|>.1),hp.1⟩) hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _=>?_ ; have hS: trim Y p'=trim Z w:=by rw [maximal_trim hb, maximal_trim hp]; rw [maximal_trim he,maximal_trim hf]; ext; simp only [Finset.mem_erase]; tauto
    rw [shoot_wait E U s x i p he hf e,← hS]; change C w i * (_ * c i b)= C p' b *(C w i * nests _ _ _ _ _ _ _ _); rw [mul_left_comm]; unfold c; unfold paint; rw [update_comm (Ne.symm e)]
end YM.OPE.Arboreal
