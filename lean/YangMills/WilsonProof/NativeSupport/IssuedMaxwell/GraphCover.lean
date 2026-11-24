import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCorrelation
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphCover
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.Scale YM.FVA2.Scale.Equator
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}

theorem original (a:Fin n→Ordinary.Label (B g))(H:ℕ)(room:∀i,(a i).1≤H)(x:Points n)(k:ℕ):
    read g n k a x=if x∈conf n then Dframe.meteor (Teller.logNu 1)
      (WilsonCapturedPhysicalMSDatum.original g.core) H x k (fun i=>up (room i) (a i).2) else 0:=by
  by_cases hx:x∈conf n
  · rw [if_pos hx,regular _ _ _ _ hx]
    let T:=WilsonCapturedPhysicalMSDatum.original g.core
    let ν:=Teller.logNu 1
    let C:=max (sky g a) H
    have l:sky g a≤C:=le_max_left .. 
    have r:H≤C:=le_max_right ..
    have left:=wave_walk ν T l n ⟨x,hx⟩ k (stamped g a)
    have right:=wave_walk ν T r n ⟨x,hx⟩ k (fun i=>up (room i) (a i).2)
    have eq:(up l ∘ stamped g a)=(up r ∘ (fun i=>up (room i) (a i).2)):=by
      funext i
      apply Subtype.ext
      rfl
    rw [eq] at left
    exact left.trans right.symm
  · rw [if_neg hx,collision _ _ _ _ hx]

def stage (h:Fin n→ℕ)(k:ℕ)(x:Points n):MultilinearMap ℂ (fun i=>(B g).sector (h i)) ℂ:=
  if x∈conf n then
    (Dframe.meteor (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core)
      (∑i,h i) x k).compLinearMap (fun i=>up
        (Finset.single_le_sum (f:=h) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)))
  else 0

theorem entered (h:Fin n→ℕ)(v:∀i,(B g).sector (h i))(k:ℕ)(x:Points n):
    read g n k (fun i=>⟨h i,v i⟩) x=stage g h k x v:=by
  by_cases hx:x∈conf n
  · rw [regular _ _ _ _ hx,stage,if_pos hx]
    rfl
  · rw [collision _ _ _ _ hx,stage,if_neg hx]
    rfl
end IssuedMaxwell.GraphCover
end
