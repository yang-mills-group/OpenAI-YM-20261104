import YM.Pert.Attach.Links

/-! Transport of complete union sets, actual flags and predicate payload permutations. -/

set_option autoImplicit false
noncomputable section
namespace YM.Pert.Attach
open Function Lattice Wilson MeasureTheory RG Finset
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {n : Side} {G : Gauge} {A:Activities G n} {X:Corrections G n} {R:Activities G n}
    {P:BudgetPoint}
local notation "B!" => attach A X P.threshold R
set_option quotPrecheck false

lemma spark_image (T:Old ≃ Old) (aft:Site n→Site n) (haf:Injective aft)
    (ht:∀ i, X.area A (T i)=(X.area A i).image aft) {v:Finset Old} (hv:Ac.Spark (X.area A) v) :
    Ac.Spark (X.area A) (v.image T) := by
   refine ⟨hv.1.image _,?_⟩; intro i hi j hj; obtain ⟨i,h0,rfl⟩:=mem_image.mp hi; obtain ⟨j,h1,rfl⟩:=mem_image.mp hj
   refine Relation.ReflTransGen.lift T (fun a b ⟨ha,hb,x,h₁,h₂⟩=>show Ac.bonds (X.area A) (v.image T) (T a) (T b) from
     ⟨mem_image_of_mem T ha, mem_image_of_mem T hb, aft x, (ht a).symm ▸ mem_image_of_mem aft h₁, (ht b).symm ▸ mem_image_of_mem aft h₂⟩) i j
     (hv.2 i h0 j h1)
lemma separate_image {a b:Support n} (f:Site n→Site n) (hf:Injective f) (h:Disjoint a b): Disjoint (a.image f) (b.image f) := by
    refine disjoint_left.mpr ?_; intro x ha hb; obtain ⟨y,hy,hyf⟩:= mem_image.mp ha; obtain ⟨z,hz,hzf⟩:= mem_image.mp hb
    exact disjoint_left.mp h hy ((hf (hzf.trans hyf.symm)) ▸ hz)
lemma unwedge {u:ℕ≃ℕ}{v:ℕ≃ℕ}{l:Finset Old} {j} : j∈(l.image (u.sumCongr v)).toLeft ↔ u.symm j∈l.toLeft := by
    simp only [mem_toLeft, mem_image]; constructor
    · rintro ⟨i,hi,e⟩; cases i <;> simp_all; simpa [← e] using hi
    intro hi; exact ⟨Sum.inl _,hi,by simp⟩

def uponWord (u v:Equiv.Perm ℕ) (aft:Site n→Site n) (haf:Injective aft)
    (ht:∀ i, X.area A (u.sumCongr v i)=(X.area A i).image aft) (c: Cluster A X) : Cluster A X := by
    let T:=u.sumCongr v; refine ⟨c.val.image T,spark_image T aft haf ht c.property.1,?_,?_⟩
    · obtain ⟨j,hj⟩:=c.property.2.1; exact ⟨u j,unwedge.mpr (by simpa using hj)⟩
    intro i hi j hj e
    have h₁ : Disjoint ((X.area A (Sum.inl (u.symm i))).image aft) ((X.area A (Sum.inl (u.symm j))).image aft) :=
         separate_image aft haf (c.property.2.2 (unwedge.mp hi) (unwedge.mp hj) (u.symm.injective.ne e))
    simp only [← ht,Equiv.sumCongr_apply,Sum.map_inl,Equiv.apply_symm_apply] at h₁; exact h₁
lemma reverse_image (f : Equiv.Perm (Site n)) (T : Equiv.Perm Old)
    (hv:∀ i, X.area A (T i)=(X.area A i).image f) : ∀ i,X.area A (T.symm i)=(X.area A i).image f.symm := by
    intro i; rw [show X.area A i=_ from (by simpa using hv (T.symm i)),image_image]
    simp [Function.comp_def]

def escape {s:Signed}{b:Site n} (h:A.Moves s b) (hw:March X s b) : Equiv.Perm ℕ := by
    let T:=h.kp.sumCongr hw.perm; let f:=Equiv.ofBijective (affine s b) (⟨fun _ _ e=>s.act_injective (add_right_cancel e),Finite.injective_iff_surjective.mp (fun _ _ e=>s.act_injective (add_right_cancel e))⟩)
    have ht : ∀ i,X.area A (T i)=(X.area A i).image f := Sum.rec h.forced_support hw.region
    have hs (x:Old) : Sum.map (fun j=>j) (fun j=>j) x=x := by cases x<;>rfl
    let K : Equiv.Perm (Cluster A X) :=
      ⟨uponWord h.kp hw.perm f f.injective ht,uponWord h.kp.symm hw.perm.symm f.symm f.symm.injective (reverse_image (A:=A) (X:=X) f T ht),
       fun i=> @Subtype.ext _ _ _ _ (by
          simp [uponWord,hs,image_image,Function.comp_def]),
       fun i=> @Subtype.ext _ _ _ _ (by
          simp [uponWord,hs,image_image,Function.comp_def])⟩
    exact ((decoding A X).trans K).trans (decoding A X).symm
lemma parts_escape {s:Signed}{b:Site n} (h:A.Moves s b) (hw:March X s b) (i:ℕ) :
    parts A X (escape h hw i) = (parts A X i).image (h.kp.sumCongr hw.perm) := by
    simp only [escape,parts,Equiv.trans_apply,Equiv.apply_symm_apply]; rfl

open Work.H03 in
def moving {s:Signed} {b:Site n} (h:A.Moves s b) (hR:R.Moves s b) (hw:March X s b) : (B!).Moves s b := by
    let K:=escape h hw; let f:=affine s b; let T:=h.kp.sumCongr hw.perm
    have ht : ∀ j,X.area A (T j)=(X.area A j).image f := Sum.rec h.forced_support hw.region
    have hv : ∀ j,X.inventory A (T j)=(X.inventory A j).image f := Sum.rec h.forced_inventory
      (fun _=> by simp [T,Corrections.inventory])
    have hs i : (page A X (K i)).support = ((page A X i).support).image f := by
       change full _ _ _ = (full _ _ _).image f; rw [show parts A X (K i)=_ from parts_escape h hw _]
       unfold full; rw [image_biUnion, biUnion_image,show (⇑(Equiv.sumCongr _ _))=(T:Old→Old) from rfl]; simp_rw [ht]
    have hi i : (page A X (K i)).inventory = ((page A X i).inventory).image f := by
       change bill _ _ = (bill _ _).image f; simp_rw [bill_union (X:=X),show parts A X (K i)=_ from parts_escape h hw _]
       rw [image_biUnion,biUnion_image,show (⇑(Equiv.sumCongr _ _))=(T:Old→Old) from rfl]; simp_rw [hv]
    have ht i U : (page A X (K i)).extraTest U ↔ (page A X i).extraTest (pull s b U) := by
       change (∀ j∈(parts A X (K i)).toLeft, _) ↔ (∀ j ∈ _, _)
       simp_rw [show K=escape h hw from rfl,parts_escape,unwedge]; constructor
       · intro ha j hj; exact h.forced_tests j U |>.mp (ha (h.kp j) (by simpa only [Equiv.symm_apply_apply]))
       intro ha j hj; simpa only [Equiv.apply_symm_apply] using (h.forced_tests (h.kp.symm j) U).mpr (ha _ hj)
    refine ⟨hR.ep,K,hR.reg_site,hR.reg_support,hs,hi,ht,hR.valuesE,?_⟩
    intro i U; change entry A X _ _ _ = entry A X _ _ _; unfold entry
    rw [eligible_send s b P.threshold U _ _ (hs i) (hi i) (ht i U)]
    split_ifs with he
    · rw [show parts A X (K i)=_ from parts_escape h hw _,prod_image T.injective.injOn]
      apply prod_congr rfl; intro l hl; cases l with
      | inl j=> exact h.valuesK _ U
      | inr j=> exact hw.value _ U
    rfl
end YM.Pert.Attach
