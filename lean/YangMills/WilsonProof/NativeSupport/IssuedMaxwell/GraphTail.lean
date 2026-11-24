import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphArms
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphLabelPorts
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphTail
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.Scale YM.FVA2.Scale.Equator YM.FVA2.Dframe YM.FVA2.O YM.FVA2.O.Score
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}

theorem original (a:Fin n→Ordinary.Label (B g))(h:Fin m→ℕ)(k:ℕ)(z:Points (n+m)):
    ∃F:MultilinearMap ℂ (fun i=>(B g).sector (h i)) ℂ,∀v:∀i,(B g).sector (h i),
      read g (n+m) k (Fin.append a (fun i=>⟨h i,v i⟩)) z=F v:=by
  by_cases hz:z∈conf (n+m)
  · let H:=sky g a+∑i,h i
    have left (i:Fin n):(a i).1≤H:=(Finset.single_le_sum (f:=fun j=>(a j).1) (fun _ _=>Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_right ..)
    have right (i:Fin m):h i≤H:=(Finset.single_le_sum (f:=h) (fun _ _=>Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_left ..)
    let A:=meteor (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core) H z k
    let earlier (i:Fin n):Sec g.core H:=up (left i) (a i).2
    let F:MultilinearMap ℂ (fun i=>(B g).sector (h i)) ℂ:=
      (GraphArms.held A earlier).compLinearMap (fun i=>up (right i))
    refine ⟨F,fun v=>?_⟩
    let later (i:Fin m):Ordinary.Label (B g):=⟨h i,v i⟩
    have room (i:Fin (n+m)):(Fin.append a later i).1≤H:=by
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [Fin.append_left] using left j
      · intro j
        simpa only [Fin.append_right] using right j
    rw [GraphCover.original g (Fin.append a later) H room z k,if_pos hz]
    exact congrArg A (GraphLabelPorts.stock g a later H left right room)
  · exact ⟨0,fun v=>collision _ _ _ _ hz⟩

abbrev entry (b:Fin m→Ordinary.Label (B g)):=∀i,Toon g.core (b i).1
def income (b:Fin m→Ordinary.Label (B g))(s:entry g b):ℂ:=∏i,coord (s i) (b i).2
def marks (b:Fin m→Ordinary.Label (B g))(s:entry g b):Scan g.core m:=fun i=>flash (s i)
theorem expanded (a:Fin n→Ordinary.Label (B g))(b:Fin m→Ordinary.Label (B g))(k:ℕ)(z:Points (n+m)):
    read g (n+m) k (Fin.append a b) z=
      ∑s:entry g b,income g b s*read g (n+m) k (Fin.append a (labels g (marks g b s))) z:=by
  let h (i:Fin m):=(b i).1
  let v (i:Fin m):Sec g.core (h i):=(b i).2
  obtain ⟨F,line⟩:=original g a h k z
  have eq:F v=read g (n+m) k (Fin.append a b) z:=(line v).symm
  rw [←eq]
  have pieces:v=(fun i=>∑s:Toon g.core (h i),coord s (v i) • theory s):=funext (fun i=>(all_sig (v i)).symm)
  calc
    F v=F (fun i=>∑s:Toon g.core (h i),coord s (v i) • theory s):=congrArg F pieces
    _=∑s:(∀i,Toon g.core (h i)),F (fun i=>coord (s i) (v i) • theory (s i)):=F.map_sum _
    _=_:=by
      refine Finset.sum_congr rfl fun s _=>?_
      have linear:=F.map_smul_univ (fun i=>coord (s i) (v i)) (fun i=>theory (s i))
      let source (i:Fin m):Ordinary.Label (B g):=⟨h i,theory (s i)⟩
      let goal:=labels g (marks g b s)
      have title:=GraphLabelPorts.transfer g a source goal (fun i=>rfl)
      calc
        _=income g b s*F (fun i=>theory (s i)):=linear
        _=_:=congrArg (fun q:ℂ=>income g b s*q) ((line (fun i=>theory (s i))).symm.trans
          (GraphFields.same g _ _ title k z))
end IssuedMaxwell.GraphTail
end
