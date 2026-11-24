import YM.Frontier6.Forest.Pen.Vault
/-!
# Nesting joint budget: obtaining one revenue bound for every horizon/refusal
 statement respecting clearances and transmitted weight grades
-/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Forest
open Road Function Set Finset Filter Fareway Spec Tale
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
variable {I V:Type}{G:Gauge}{C:Family G}{H:Extraction.Order}{S:Table C.book}{T: Fareway I}{K:Final C H S}{P Q:Fabric I}{A:Art S I}{L L':Finset ℝ}{b a w r:ℝ}{x:I→ E4}
variable (hC:Road.Ribbon C H S)(top:Forest.Top K T L L' r)(he:Pen K T L a P A w) (ha:a∈ L)
include hC top he ha
namespace Face
lemma refuse (h:Face K T L' r a P w A)(hb:b∈L)(hz:b≤a)(hp:Local T P x a)(hx:Contains T P x)(d:ℕ)(hc:Forest.Centered T P x K d): Face K T L' r b P (w-(d+1:ℝ)*(a-b)) (fun i=> reject K (x i) d (A i)):=by
    have hy:= lights K d hc he.intact
    rcases (top.apex _ ha).2.eq_or_lt with ha'|ha'
    · subst r; have hw:= (h.private_ rfl).dye K hC hp (top.apex _ ha).1 d hc hx; refine ⟨fun hh=>?_,fun hv=>?_⟩
      · rw [← Nat.cast_one (R:=ℝ),← Nat.cast_add (R:=ℝ)]; refine deepen hC hw hp hx ((top.apex _ hb).1.trans_lt hh) hz (d+1) ?_
        intro i hi; filter_upwards [hy] with v hv; rw [pitch, absorb_killed K d _ _ hv (by omega),map_zero]
      rwa [hv,sub_self,mul_zero,sub_zero]
    refine ⟨fun hh=>?_,fun hv=> False.elim (by linarith)⟩
    have hr:= (top.apex _ ha).1.trans_lt ha'
    obtain ⟨v,hv,hV⟩:= h.outer ha'; let f(w:ℕ)(i:I):= part K (x i) w (A i); let g(w d:ℕ)(i:I):= part K (x i) w (v d i)
    have hp'(z:Fin (d+1)): Prism K T r P (f z) (g z):=by
       have hZ:= Mist.lower_ready K hc (show (z:ℕ)≤d from Nat.lt_add_one_iff.mp z.isLt); exact Prism.hue z hx (accrue hC top h he ha hp z hZ) (hv.shineout hC hr hZ he.intact (hV.mono fun i hi=> hi.intact))
    have hQ: Prism K T r P (fun i=> all K (x i) d (A i)) (fun j i=> all K (x i) d (v j i)):=by
       refine (Prism.folds Finset.univ (V:=Fin (d+1)) (fun z _=> hp' z)).cf (hy.mono (fun i hi=>(all_from_parts K d _ _ hi).symm)) ?_; exact hV.mono (fun i hi=> (lights K d hc hi.intact).mono fun i hi=>(all_from_parts K d _ _ hi).symm)
    exact ⟨fun j i=> reject K (x i) d (v j i), hv.sub hQ, hV.mono fun i hi=> hi.refuse (top.smaller a ha ha') hz hp hx d hc⟩
lemma summit : Face K T L' r a P w A:=by
    induction he with
    | tip h x=> exact tip h x
    | zero=> exact zero
    | scale hc he ih=> exact (ih ha).scale hc
    | add _ _ ih jh=> exact (ih ha).add (jh ha)
    | cf _ hk ih=> exact (ih ha).cf hk
    | mono _ hk ih=> exact (ih ha).mono hk
    | weaker h he ih=>exact (ih ha).broader he
    | mul _ _ hv ih jh=>exact (ih ha).mul (jh ha) hv
    | feed h ha' hb hp hx ih=> exact feeds hC top (ih ha') ha' hp ha hb hx
    | refuse h ha' he hp hx d hc ih=> exact refuse hC top h ha' (ih ha') ha he hp hx d hc
    | pass h ha' hp hx d hc ih=> exact pass hC top (ih ha') h ha' hp hx d hc
end Face
omit he ha
lemma toppish (hz:(0:ℝ)∈L): Credit K T L:=by
    refine ⟨fun P A w s he=> ?_,fun P A w a he ha d x=> Face.accrue hC top (Face.summit hC top he ha) he ha (d:=d)⟩ -- order
    have hh:= Face.summit hC top he hz; rcases (top.apex _ hz).2.eq_or_lt with hv|hv
    · exact (hh.private_ hv).colorless K hC hv.symm s
    obtain ⟨u,hu,hQ⟩:= hh.outer hv; obtain ⟨k,hk,hU⟩:= (hQ.and (hu.gains hC hv w)).exists; refine ((hU s).add ((top.routed hv).hall P (u k) w s hk)).cf ?_; filter_upwards with i; simp [polled]
omit top
lemma pinnacle (h:L.Nonempty) (hz:(0:ℝ)∈L)(he:∀ v∈ L,0 ≤ v) : Credit K T L:=by
    induction L using Finset.strongInduction with
    | _ L ih=>
       let r:=L.max' h; have hh:r∈ L:= Finset.max'_mem ..; refine toppish hC (L':=L.erase r) ⟨hh,fun a ha=>⟨he a ha,Finset.le_max' _ a ha⟩,fun a ha hb=> mem_erase_of_ne_of_mem (ne_of_lt hb) ha,fun hv=>?_⟩ hz; have ht:(0:ℝ)∈ L.erase r:=mem_erase_of_ne_of_mem (ne_of_lt hv) hz; exact ih _ (Finset.erase_ssubset hh) ⟨_,ht⟩ ht fun v hv=> he v (mem_of_mem_erase hv) -- order
end YM.Frontier6.Forest
