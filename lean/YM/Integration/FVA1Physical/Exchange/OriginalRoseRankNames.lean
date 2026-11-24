import YM.XSpace.Laurel
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon

/-! The heterogeneous source grades survive the original complete
Daylight dictionary. This includes the two grade-four sources as filed in
the common grade-six shell. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
namespace YM.Integration.FVA1Physical.Exchange.RoseNoise
open Finset XSpace XSpace.Normalize XSpace.Chiral Maxwell Maxwell.Free
open MvPolynomial MS MS.Menus MS.Theater
open scoped Classical BigOperators
variable {G:Gauge}

def originalRoseDegree : Fin 3 → ℕ×ℕ:=![ (6,3),(4,2),(4,2)]

theorem original_rose_slot_degree (i:Fin 3):
    IsWeightedHomogeneous (fun a:Maxwell.Slot G=>(a.1+2,(1:ℕ))) (Rose.tag G i).val (originalRoseDegree i):=by
  let wt:=fun a:Maxwell.Slot G=>(a.1+2,(1:ℕ))
  have b:IsWeightedHomogeneous wt (B G) (6,3):=by
    unfold B
    apply IsWeightedHomogeneous.sum;intro i _
    apply IsWeightedHomogeneous.sum;intro j _
    apply IsWeightedHomogeneous.sum;intro k _
    apply (weightedHomogeneousSubmodule ℂ wt ((6,3):ℕ×ℕ)).smul_mem
    exact ((symbol_hom (arm true (G:=G) i) (fun i=>(i+2,(1:ℕ)))).mul
      (symbol_hom (arm true (G:=G) j) (fun i=>(i+2,(1:ℕ))))).mul
      (symbol_hom (arm true (G:=G) k) (fun i=>(i+2,(1:ℕ))))
  have u:IsWeightedHomogeneous wt (U G) (4,2):=by
    unfold U
    apply (weightedHomogeneousSubmodule ℂ wt ((4,2):ℕ×ℕ)).smul_mem
    apply IsWeightedHomogeneous.sum;intro i _
    exact (symbol_hom (arm false (G:=G) i) (fun i=>(i+2,(1:ℕ)))).mul
      (symbol_hom (arm false (G:=G) i) (fun i=>(i+2,(1:ℕ))))
  fin_cases i
  · exact (weightedHomogeneousSubmodule ℂ wt ((6,3):ℕ×ℕ)).smul_mem ((Rose.f:ℂ)^3) b
  · exact (weightedHomogeneousSubmodule ℂ wt ((4,2):ℕ×ℕ)).smul_mem ((Rose.f:ℂ)^2) u
  · exact (weightedHomogeneousSubmodule ℂ wt ((4,2):ℕ×ℕ)).smul_mem ((Rose.f:ℂ)^2) u

theorem original_supported_glyph {d:ℕ}(D:MS.Local.Physical.Deck G)(p:Sec G d)(z:ℕ×ℕ)
    (hom:IsWeightedHomogeneous (fun a:Maxwell.Slot G=>(a.1+2,(1:ℕ))) p.val z)
    (b:Glyph D d)(other:z≠(b.size,b.grade)):(Daylight D d).repr p b=0:=by
  classical
  let T:=Daylight D d
  let a:=fun j:Glyph D d=>T.repr p j
  let v:=fun j:Glyph D d=>if z=(j.size,j.grade) then a j else 0
  have view(j:Glyph D d):(T j).val=Letters D j:=congrArg Subtype.val (Theater.readHeight D d j)
  have original:∑j:Glyph D d,a j • Letters D j=p.val:=by
    simpa only [Submodule.coe_sum,SetLike.val_smul,view] using congrArg Subtype.val (T.sum_repr p)
  have correct:∑j:Glyph D d,v j • Letters D j=p.val:=by
    have image:=congrArg (biasW G z) original
    rw [hom.weightedHomogeneousComponent_same] at image
    simp only [map_sum,map_smul,bias_C] at image
    rw [←image];apply Finset.sum_congr rfl;intro j _
    by_cases hj:z=(j.size,j.grade)
    · simp [v,hj,Glyph.size,Glyph.grade]
    · simp [v,hj,Glyph.size,Glyph.grade]
  have back:∑j:Glyph D d,v j • T j=p:=by
    apply Subtype.ext;simpa only [Submodule.coe_sum,SetLike.val_smul,Theater.readHeight,T] using correct
  have take:T.repr (∑j:Glyph D d,v j • T j) b=v b:=by
    rw [map_sum,Finsupp.finsetSum_apply];simp [Finsupp.single_apply]
  rw [back] at take
  exact take.trans (if_neg other)

theorem original_rose_glyph_rank (D:MS.Local.Physical.Deck G)(i:Fin 3)(b:Glyph D 6)
    (nonzero:(Daylight D 6).repr (Rose.tag G i) b≠0):
    (b.size,b.grade)=originalRoseDegree i:=by
  by_contra other
  exact nonzero (original_supported_glyph _ _ _ (original_rose_slot_degree i) b (Ne.symm other))

end YM.Integration.FVA1Physical.Exchange.RoseNoise
