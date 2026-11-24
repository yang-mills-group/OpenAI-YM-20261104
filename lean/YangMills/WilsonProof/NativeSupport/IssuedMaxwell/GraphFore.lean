import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphFirstArms
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphLabelPorts
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphGrade
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphFore
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.Scale YM.FVA2.Scale.Equator YM.FVA2.Dframe YM.FVA2.O YM.FVA2.O.Score
open YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n m:ℕ}

theorem original (h:Fin n→ℕ)(b:Fin m→Ordinary.Label (B g))(k:ℕ)(z:Points (n+m)):
    ∃F:MultilinearMap ℂ (fun i=>(B g).sector (h i)) ℂ,∀v:∀i,(B g).sector (h i),
      read g (n+m) k (Fin.append (fun i=>⟨h i,v i⟩) b) z=F v:=by
  by_cases hz:z∈conf (n+m)
  · let H:=(∑i,h i)+sky g b
    have left (i:Fin n):h i≤H:=(Finset.single_le_sum (f:=h) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)).trans
      (Nat.le_add_right ..)
    have right (i:Fin m):(b i).1≤H:=(Finset.single_le_sum (f:=fun j=>(b j).1) (fun _ _=>Nat.zero_le _)
      (Finset.mem_univ i)).trans (Nat.le_add_left ..)
    let A:=meteor (Teller.logNu 1) (WilsonCapturedPhysicalMSDatum.original g.core) H z k
    let later (i:Fin m):Sec g.core H:=up (right i) (b i).2
    let F:MultilinearMap ℂ (fun i=>(B g).sector (h i)) ℂ:=
      (GraphFirstArms.held A later).compLinearMap (fun i=>up (left i))
    refine ⟨F,fun v=>?_⟩
    let earlier (i:Fin n):Ordinary.Label (B g):=⟨h i,v i⟩
    have room (i:Fin (n+m)):(Fin.append earlier b i).1≤H:=by
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [Fin.append_left] using left j
      · intro j
        simpa only [Fin.append_right] using right j
    rw [GraphCover.original g (Fin.append earlier b) H room z k,if_pos hz]
    exact congrArg A (GraphLabelPorts.stock g earlier b H left right room)
  · exact ⟨0,fun v=>collision _ _ _ _ hz⟩

abbrev grades (a:Fin n→Ordinary.Label (B g)):=∀i,Grade g.core (a i).1
def income (a:Fin n→Ordinary.Label (B g))(s:grades g a):ℂ:=∏i,paygrade (s i) (a i).2
def mask (a:Fin n→Ordinary.Label (B g))(s:grades g a):Scan g.core n:=fun i=>own (s i)

theorem expanded (a:Fin n→Ordinary.Label (B g))(homo:∀i,Ordinary.homogeneous (B g) (a i).1 (a i).2.val)
    (b:Fin m→Ordinary.Label (B g))(k:ℕ)(z:Points (n+m)):
    read g (n+m) k (Fin.append a b) z=
      ∑s:grades g a,income g a s*read g (n+m) k (Fin.append (labels g (mask g a s)) b) z:=by
  let h (i:Fin n):=(a i).1
  let v (i:Fin n):Sec g.core (h i):=(a i).2
  obtain ⟨F,line⟩:=original g h b k z
  have pieces:v=(fun i=>∑s:Grade g.core (h i),paygrade s (v i) • vertex s):=funext
    (fun i=>(whole_grade _ ((GraphGrade.original g _).mp (homo i))).symm)
  calc
    _=F v:=line v
    _=F (fun i=>∑s:Grade g.core (h i),paygrade s (v i) • vertex s):=congrArg F pieces
    _=∑s:grades g a,F (fun i=>paygrade (s i) (v i) • vertex (s i)):=F.map_sum _
    _=_:=by
      refine Finset.sum_congr rfl fun s _=>?_
      have linear:=F.map_smul_univ (fun i=>paygrade (s i) (v i)) (fun i=>vertex (s i))
      calc
        _=income g a s*F (fun i=>vertex (s i)):=linear
        _=_:=congrArg (fun q:ℂ=>income g a s*q) (line (fun i=>vertex (s i))).symm
end IssuedMaxwell.GraphFore
end
