import YM.Frontier6.Multi.Seams.Display
import YM.Frontier6.Multi.Tale.Smooth

/-! Join branches at disjoint roots. Make room GENERIC across roots by
     adjusting centers, not internal relative positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Frontier6.Road
open Function Set Finset Filter Lattice RG Wilson Extraction Cells Next.UVStress Bid Spec Platform Tale OS Word
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C: Family G}{V:Type}[Fintype V][DecidableEq V]
lemma shadow_clear (v w:V)(a:Axis)(z u:ℝ)(h:v≠w): Dense {x:V→ E4| x v a+z≠x w a+u}:=by
    intro x; by_cases hz: x v a+z=x w a+u
    swap; exact subset_closure hz
    let f : ℝ → (V→ E4):=fun t=> update x v (x v + t • basis a)
    have he : f 0=x:=by simp [f]
    have hf : Continuous f:= continuous_pi fun i=> by by_cases h:i=v <;>simp only [f,h,update_self, update_of_ne] <;> fun_prop
    rw [← he]; apply mem_closure_of_frequently_of_tendsto (b:=𝓝[>] (0:ℝ)) _ (hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    refine Eventually.frequently ((show ∀ᶠ t:ℝ in 𝓝[>] (0:ℝ),0<t from self_mem_nhdsWithin).mono fun t ht=>?_)
    change f t v a+z ≠ f t w a+u; simp only [f,update_self, update_of_ne h.symm]; have hq : (x v + t • basis a) a=x v a+t:=by simp
    rw [hq]; linarith

variable {k m l:ℕ}{P:V→Type} {W : (i:V)→P i→Type}
variable (X:∀ i:V,Plan C (P i) (W i)) [_i : ∀ i,Fintype (P i)] [_j : ∀ i b,Fintype (W i b)]
variable {F:Extraction.Order}{S: Table C.book} (K:Final C F S)(s:StateIndex K)
set_option quotPrecheck false
local notation "ι"=> (∀ i:V,P i)
namespace Plan
variable (z:V→ E4)
def clearFamily (k:ℕ)(z:V→ E4):Prop:=∀ x:∀ i:V,P i,∀ a:Axis,Injective (fun i:Slots (W':=W) x=>landing X k z x i a)
def SlotsClear {P:Type}{w:P→Type}(X:Plan C P w)(k:ℕ):Prop:=∀ (i:P)(a:Axis), Injective (fun j:w i=> C.S.gridPoint k (X.point i j) a)
lemma chart_cont (x:ι): Continuous fun z:V→ E4=> landing X k z x := continuous_pi fun b=>by unfold landing; fun_prop
lemma intact (k:ℕ): IsOpen {z:V→ E4| clearFamily X k z}:=by
    let U (x:ι)(i j:Slots (W':=W) x)(a:Axis):={z:V→ E4| i≠j→ landing X k z x i a≠landing X k z x j a}
    have hU (x:ι)(i j:Slots (W':=W) x)(a:Axis):IsOpen (U x i j a):=by
       by_cases h:i=j; rw [show U x i j a=Set.univ from (by ext z; simp [U,h])]; exact isOpen_univ
       unfold U; simp only [ne_eq,h,not_false_eq_true,true_imp_iff]; apply isOpen_ne_fun <;> unfold landing <;> fun_prop
    let A:= ⋂ (x:ι)(i:Slots (W':=W) x)(j:Slots (W':=W) x)(a:Axis), U x i j a
    rw [show {z:V→ E4|_}=A from (by ext z; simp [clearFamily,A,U,Injective]; constructor<;> intro h <;> intros <;> grind)]
    exact isOpen_iInter_of_finite fun i=> isOpen_iInter_of_finite fun j=> isOpen_iInter_of_finite fun k=> isOpen_iInter_of_finite fun a=> hU ..
lemma dense_scene (h:∀ i:V,SlotsClear (X i) k): Dense {z:V→ E4 | clearFamily X k z}:=by
    let U (x:ι)(i j:Slots (W':=W) x)(a:Axis):={z:V→ E4| i.fst≠j.fst→ landing X k z x i a≠landing X k z x j a}
    have hp (x:ι) (i j:Slots (W':=W) x)(a:Axis): IsOpen (U x i j a)∧ Dense (U x i j a):=by
       by_cases hi:i.fst=j.fst; rw [show U x i j a=Set.univ from (by ext z; simp [U,hi])]; exact ⟨isOpen_univ,dense_univ⟩
       unfold U; simp only [ne_eq,hi,not_false_eq_true,true_imp_iff]; refine ⟨?_,?_⟩
       · apply isOpen_ne_fun <;> unfold landing <;> fun_prop
       exact (shadow_clear i.1 j.1 a (C.S.gridPoint k ((X i.1).point _ i.2) a) (C.S.gridPoint k ((X j.1).point _ j.2) a) hi).mono fun z hz=>by
         intro he; refine hz ?_;  change _ + z _ a=_ + z _ a at he; rwa [add_comm,add_comm (z j.fst a)]
    let A:= ⋂ (x:ι)(i:Slots (W':=W) x)(j:Slots (W':=W) x)(a:Axis), U x i j a
    have hs:Dense A:=by
       apply dense_iInter_of_isOpen (fun x=>isOpen_iInter_of_finite (fun i=>isOpen_iInter_of_finite (fun j=>isOpen_iInter_of_finite (fun a=>(hp x i j a).1)))) (fun x=> dense_iInter_of_isOpen (fun i=> isOpen_iInter_of_finite (fun j=>isOpen_iInter_of_finite (fun a=>(hp x i j a).1))) (fun i=>dense_iInter_of_isOpen (fun j=> isOpen_iInter_of_finite (fun a=>(hp x i j a).1)) (fun j=>dense_iInter_of_isOpen (fun a=>(hp x i j a).1) (fun a=>(hp x i j a).2))))
    apply hs.mono; intro z hz x a; rintro ⟨i,j⟩ ⟨p,q⟩ he; by_cases hm:i=p
    · subst p; refine congr_arg (Sigma.mk i) ((h i _ a) ?_); exact add_right_cancel (show _ + z i a=_+z i a from he)
    exact False.elim (Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp (Set.mem_iInter.mp hz x) _) _) a hm he)

lemma reads_cont {z:V→ E4}(hz:∀ x:ι,Injective (landing X k z x)) : ContinuousAt (fun z:V→ E4=> poll S (state K s) (∏ i:V,(X i).syntaxR k (z i) S)) z:=by
    simp_rw [route,map_sum,map_smul]; apply tendsto_finsetSum
    intro i _; exact (assembly_cont K s (chart_cont X _).continuousAt (hz i) _).const_smul (relationRow X i)
lemma reads_move {z:V→ E4}(p:E4) : poll S (state K s) (∏ i:V,(X i).syntaxR k (z i+p) S)= poll S (state K s) (∏ i:V,(X i).syntaxR k (z i) S):=by simp_rw [route,map_sum,map_smul]; refine Finset.sum_congr rfl fun i _=>congr_arg (relationRow X i • ·) ?_; rw [draw,draw,show landing X k (fun i=> z i+p) i=(fun j=>landing X k z i j+p) from (by ext j; simp [landing,add_assoc])]; exact translating ..
end Plan
end YM.Frontier6.Road
