import YM.RG11Proof.Fields.Compatible
import YM.Pert.Rigid.Camera

/-!
# Genuine smaller-horizon frozen tests still constrain the larger Buffer
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG11.Rigidity.Ice
open Fields Horizon Labels Pert.Position Pert Maxwell Function Extra.FD
open scoped Classical BigOperators
variable {G : Gauge} {F : Frames G} {d e:ℕ}

def Frigid (b : Buffer F d) : Prop := ∀ (r : ℕ) (p : Fin r→E F d) (x : Points r),x∈conf r→∑ i,visible F d x (update p i (b.val (p i)))=0

set_option maxHeartbeats 450000 in
lemma readBefore (b : Buffer F d)(h : e ≤ d): ∃ v : Buffer F e,∀ p, b.val (up F h p)=up F h (v.val p) := by
  let B:=tower F d; let A:=tower F e
  let q:= rise F h
  have hp : Adapted.Gives A B h q:= basis_rise F _
  have H:= Adapted.Gives.coherent hp
  obtain ⟨r,rfl⟩:= B.toBasis.covers b
  let t : A.toBasis.guard.vary:= ⟨Horizon.take q r.val,H.legal r⟩
  refine ⟨A.toBasis.operates t,fun p=> ?_⟩
  have hz (i) : B.toBasis.liftRows r.val (up F h (A.b i))=up F h (A.toBasis.liftRows t.val (A.b i)):=by
    rw [←hp,Basis.row_basis,Basis.row_basis,Basis.put_sum,Basis.put_sum,map_sum]
    simp_rw [map_smul,← (show ∀ i,_=up F h (A.b i) from hp)]
    change _= ∑ x:A.toBasis.J,(r.val (q i) (q x) : ℂ) • B.b (q x)
    rw [← Finset.sum_map (Finset.univ (α:=A.toBasis.J)) q (fun j=> (r.val (q i) j : ℂ) • B.toBasis.b j)] -- t.val definitional?
    refine (Finset.sum_subset (Finset.subset_univ _) (fun j _ he=>by
      rw [H.anchored r i j ?_, Complex.ofReal_zero,zero_smul]
      rintro ⟨c,rfl⟩; exact he (Finset.mem_map_of_mem q (Finset.mem_univ c)))).symm
  change B.toBasis.liftRows r.val (up F h p)=up F h (A.toBasis.liftRows t.val p)
  rw [←A.b.sum_equivFun p]
  simp_rw [map_sum,map_smul,hz]

lemma Frigid.smaller {b : Buffer F d}(H : Frigid b)(h:e ≤ d){v : Buffer F e}(hv:∀ p,b.val (up F h p)=up F h (v.val p)): Frigid v := by
  intro r p x hx
  rw [← H _ (up F h ∘ p) _ hx]; refine Finset.sum_congr rfl fun i _=> ?_
  rw [← up_moment (F:=F) h]
  congr 1; ext1 j; by_cases he:j=i <;> simp [he,hv]

lemma Frigid.four {b : Buffer F d}(H : Frigid b)(h:4≤d)(hG:G.Simple)(p:E F 4): b.val (up F h p)=0 := by
  obtain ⟨v,hv⟩:=readBefore b h; rw [hv,show v=0 from Rigid.frozen_four F hG v (H.smaller h hv)]
  exact map_zero _
end YM.RG11.Rigidity.Ice
