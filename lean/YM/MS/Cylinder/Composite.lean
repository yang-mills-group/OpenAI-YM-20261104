import YangMills.WilsonProof.NativeSupport.YM.MS.Cylinder.Variable
/-!
# Test by std letters

Quantum fields. Extern legs with any ell² color finite. Change-of-coordinates extends
 to combined source terms. No assertions on unbounded rank, stencil yes.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Cylinder.Slim
open Function Set Finset Koszul
variable {A B D E R:Type*}[CommRing R]{K:B→A→R}{T:D→B→R}
-- turn restricted. Auxiliary lemma computes route through any finite intermediate sites.
def meld (V:B→A→R) (h:Slim V)(T:D→B→R)(i:D)(j:A): R:= shade T (arrive V h (single j)) [i]
variable (h:Slim K)
include h
private lemma possible (s:Finset A): ∃ J:Finset B, ∀ i∈s,(support fun j=>K j i) ⊆ (J:Set B):= by
    classical
    exact ⟨s.biUnion fun i=>(h i).toFinset, fun i hi _ hx=>mem_biUnion.mpr ⟨i,hi,(h _).mem_toFinset.mpr hx⟩⟩
lemma merge (T:D→B→R) (F:Cyl A R) : shade T (arrive K h F)=shade (meld K h T) F:= by
   funext l; induction l generalizing F with
   | nil=> simp
   | cons i l ih=>
       obtain ⟨s,hs⟩:=fromCyl F; obtain ⟨t,ht⟩:=possible h s; have he : Uses (t:Set B) (arrive K h F).val:= stretch F hs ht
       have hh (j:A)(hj:j∈s): meld K h T i j= ∑ v∈t,T i v*K v j:= by
          have hL : Uses (t:Set B) (arrive K h (single j)).val:= stretch (single j) (near_letter j) (by rintro _ hh; exact (Set.mem_singleton_iff.mp hh) ▸ ht j hj)
          unfold meld; rw [deriv_lum T i _ hL]; refine Finset.sum_congr rfl (fun a ha=>?_); simp only [shade_nil,enterp,at_D,lands,name]
       rw [deriv_lum _ i F hs,deriv_lum _ i _ he]; simp_rw [h.drop _ _ hs,map_sum,map_smul, Finset.sum_apply,Pi.smul_apply,Finset.mul_sum, ih]; rw [Finset.sum_comm]; refine Finset.sum_congr rfl (fun j hj=>?_); rw [hh j hj, Finset.sum_mul]; exact Finset.sum_congr rfl fun i _=> (mul_assoc ..).symm -- check orientation
lemma commute {U:E→A→R}{L:D→E→R}(f:Slim U) (Z:Cyl A R)(H:∀ i,shade T (arrive K h (single i))=shade L (arrive U f (single i))): shade T (arrive K h Z)=shade L (arrive U f Z) := by rw [merge,merge]; rw [show meld K h T=meld U f L from funext fun i=> funext fun j=> congr_fun (H j) [i]]
lemma reaches_same {U:D→A→R} (Z:Cyl A R)(H:∀ i,shade T (arrive K h (single i))=shade U (single i)): shade T (arrive K h Z)=shade U Z:= by
    rw [merge]; rw [show meld K h T=U from funext fun i=> funext fun j=>by simp only [meld,H,name]]

end YM.MS.Cylinder.Slim
