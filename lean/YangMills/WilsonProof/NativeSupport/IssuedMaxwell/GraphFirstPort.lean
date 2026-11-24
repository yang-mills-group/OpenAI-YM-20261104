import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCover
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphPrices
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphFirstPort
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.O.Project YM.FVA2.Scale YM.FVA2.Scale.Equator
open PowerSeries YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}

theorem original (b:Fin m→Ordinary.Label (B g))(w k:ℕ)(x:Points (m+1)):
    ∃f:Sec g.core w→ₗ[ℂ]ℂ,∀v:Sec g.core w,read g (m+1) k (Fin.cons (α:=fun _:Fin (m+1)=>Ordinary.Label (B g)) ⟨w,v⟩ b) x=f v:=by
  by_cases hx:x∈conf (m+1)
  · let H:=w+sky g b
    have hw:w≤H:=Nat.le_add_right .. 
    have hb (i:Fin m):(b i).1≤H:=
      le_trans (Finset.single_le_sum (f:=fun i=>(b i).1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left ..)
    let peers:Fin (m+1)→Sec g.core H:=Fin.cons 0 (fun i=>up (hb i) (b i).2)
    let F:=Dframe.meteor (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core) H x k
    refine ⟨(F.toLinearMap peers 0).comp (up hw),fun v=>?_⟩
    have room (i:Fin (m+1)):((Fin.cons (α:=fun _:Fin (m+1)=>Ordinary.Label (B g)) ⟨w,v⟩ b) i).1≤H:=by
      refine Fin.cases ?_ (fun j=>?_) i
      · simpa only [Fin.cons_zero] using hw
      · simpa only [Fin.cons_succ] using hb j
    rw [GraphCover.original _ _ H room x k,if_pos hx]
    change F _=F (Function.update peers 0 (up hw v))
    congr 1
    funext i
    refine Fin.cases ?_ (fun j=>?_) i
    · apply Subtype.ext
      change ((Fin.cons (α:=fun _:Fin (m+1)=>Ordinary.Label (B g)) ⟨w,v⟩ b) 0).2.val= _
      simp only [Function.update_self]
      rfl
    · apply Subtype.ext
      change ((Fin.cons (α:=fun _:Fin (m+1)=>Ordinary.Label (B g)) ⟨w,v⟩ b) j.succ).2.val=_
      simp only [Fin.cons_succ,Function.update_of_ne (Fin.succ_ne_zero j),peers]
      rfl
  · exact ⟨0,fun v=>collision _ _ _ _ hx⟩

theorem price (b:Fin m→Ordinary.Label (B g))(w k j:ℕ)(p:FLog g.core n)(t:ℝ)(x:Points n)(y:Points (m+1)):
    read g (m+1) k (Fin.cons ⟨w,GraphPrices.entered g p w j t x⟩ b) y=
      ∑i:Grade g.core w,coeff j (p t x (own i))*read g (m+1) k (Fin.cons ⟨w,vertex i⟩ b) y:=by
  obtain ⟨f,linear⟩:=original g b w k y
  simp_rw [linear]
  let r (i:Grade g.core w):=coeff j (p t x (own i))
  change f (∑i:Grade g.core w,r i • vertex i)=_
  calc
    _=∑i:Grade g.core w,f (r i • vertex i):=map_sum f _ _
    _=_:=Finset.sum_congr rfl fun i _=>f.map_smul (r i) (vertex i)
end IssuedMaxwell.GraphFirstPort
end
