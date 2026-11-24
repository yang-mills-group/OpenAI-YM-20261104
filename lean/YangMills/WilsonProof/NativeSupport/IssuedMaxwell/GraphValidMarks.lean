import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphInverseExterior
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphExteriorMarket
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphValidMarks
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.Dframe YM.FVA2.Scale
open PowerSeries Set YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphCorrelation
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}

theorem exact (u:Scan g.core n)(i:Fin n):
    Ordinary.homogeneous (B g) (labels g u i).1 (labels g u i).2.val:=by
  apply (GraphGrade.original g _).mpr
  exact vertex_at (u i).item

theorem settled (simple:g.IsSimple){O:Ordinary.OPE (B g)}(purchased:Ordinary.Valid (B g) (read g) O)
    (u:Scan g.core n)(h k:ℕ)(x:Points n):
    (O n h k (labels g u) x).val=
      ∑w:Fin (h+1),(GraphBasisExterior.price g u w.val k 0 x).val:=by
  obtain ⟨p,paid,_,word⟩:=purchased.homogeneousWord n (labels g u) (exact g u)
  rw [←GraphInverseExterior.original g simple u p paid]
  exact word h k x

theorem expanded {O:Ordinary.OPE (B g)}(purchased:Ordinary.Valid (B g) (read g) O)
    (a:Fin n→Ordinary.Label (B g))(h k:ℕ)(x:Points n):
    O n h k a x=∑s:GraphTail.entry g a,GraphTail.income g a s • O n h k (labels g (GraphTail.marks g a s)) x:=by
  let heights (i:Fin n):=(a i).1
  let v (i:Fin n):Sec g.core (heights i):=(a i).2
  obtain ⟨F,paid⟩:=purchased.multilinear n h k heights x
  have live:O n h k a x=F v:=paid v
  have pieces:v=(fun i=>∑s:Toon g.core (heights i),coord s (v i) • theory s):=
    funext (fun i=>(all_sig (v i)).symm)
  calc
    _=F v:=live
    _=F (fun i=>∑s:Toon g.core (heights i),coord s (v i) • theory s):=congrArg F pieces
    _=∑s:(∀i,Toon g.core (heights i)),F (fun i=>coord (s i) (v i) • theory (s i)):=F.map_sum _
    _=_:=by
      refine Finset.sum_congr rfl fun s _=>?_
      have linear:=F.map_smul_univ (fun i=>coord (s i) (v i)) (fun i=>theory (s i))
      let initial (i:Fin n):Ordinary.Label (B g):=⟨heights i,theory (s i)⟩
      have earned:=purchased.sameInputs n h k initial (labels g (GraphTail.marks g a s)) x (fun _=>rfl)
      calc
        _=GraphTail.income g a s • F (fun i=>theory (s i)):=linear
        _=_:=congrArg (fun z=>(GraphTail.income g a s) • z) ((paid (fun i=>theory (s i))).symm.trans earned)

theorem original (simple:g.IsSimple){O Q:Ordinary.OPE (B g)}(hO:Ordinary.Valid (B g) (read g) O)
    (hQ:Ordinary.Valid (B g) (read g) Q):O=Q:=by
  funext n h k a x
  rw [expanded g hO,expanded g hQ]
  refine Finset.sum_congr rfl fun s _=>?_
  congr 1
  apply Subtype.ext
  exact (settled g simple hO _ _ _ _).trans (settled g simple hQ _ _ _ _).symm
end IssuedMaxwell.GraphValidMarks
end
