import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphCover
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphFields
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.Scale YM.FVA2.Scale.Equator YM.FVA2.Dframe YM.FVA2.O YM.FVA2.O.Score
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}
theorem same (a b:Fin n→Ordinary.Label (B g))(equal:∀i,(a i).2.val=(b i).2.val)(k:ℕ)(x:Points n):
    read g n k a x=read g n k b x:=by
  let H:=sky g a+sky g b
  have room (v:Fin n→Ordinary.Label (B g))(i:Fin n):(v i).1≤ sky g v:=
    Finset.single_le_sum (f:=fun j=>(v j).1) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
  rw [GraphCover.original _ a H (fun i=>(room a i).trans (Nat.le_add_right ..)),
      GraphCover.original _ b H (fun i=>(room b i).trans (Nat.le_add_left ..))]
  by_cases hx:x∈conf n
  · simp only [if_pos hx]
    congr 1
    funext i
    exact Subtype.ext (equal i)
  · rw [if_neg hx,if_neg hx]

theorem original (a:Fin n→Ordinary.Label (B g))(x:Points n)(k:ℕ):
    read g n k a x=∑s:(∀i,Toon g.core (a i).1),
      (∏i,coord (s i) (a i).2)*read g n k (labels g (fun i=>flash (s i))) x:=by
  let h (i:Fin n):=(a i).1
  let F:=GraphCover.stage g h k x
  let v (i:Fin n):Sec g.core (h i):=(a i).2
  have eval:F v=read g n k a x:=(GraphCover.entered g h v k x).symm
  rw [←eval]
  have pieces:v=(fun i=>∑s:Toon g.core (h i),coord s (v i) • theory s):=funext (fun i=>(all_sig (v i)).symm)
  calc
    F v=F (fun i=>∑s:Toon g.core (h i),coord s (v i) • theory s):=congrArg F pieces
    _=∑s:(∀i,Toon g.core (h i)),F (fun i=>coord (s i) (v i) • theory (s i)):=F.map_sum _
    _=_:=by
      refine Finset.sum_congr rfl fun s _=>?_
      have linear:=F.map_smul_univ (fun i=>coord (s i) (v i)) (fun i=>theory (s i))
      calc
        _=(∏i,coord (s i) (v i))*F (fun i=>theory (s i)):=linear
        _=_:=by
          congr 1
          exact (GraphCover.entered g h (fun i=>theory (s i)) k x).symm.trans
            (same g (fun i=>⟨h i,theory (s i)⟩) (labels g (fun i=>flash (s i))) (fun i=>rfl) k x)
end IssuedMaxwell.GraphFields
end
