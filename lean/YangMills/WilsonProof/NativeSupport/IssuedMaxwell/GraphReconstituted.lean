import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphReaderScope
import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphHomogeneous
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphReconstituted
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.Dframe YM.FVA2.Scale
open Set YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphReader
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}

theorem held (a:Fin n→Ordinary.Label (B g))(pure:∀i,Ordinary.homogeneous (B g) (a i).1 (a i).2.val)
    (h k:ℕ)(x:Points n):
    name g n h k a x=∑s:GraphFore.grades g a,GraphFore.income g a s • earned g (GraphFore.mask g a s) h k x:=by
  let d (i:Fin n):=(a i).1
  let v (i:Fin n):Sec g.core (d i):=(a i).2
  let F:=form g d h k x
  have pieces:v=(fun i=>∑s:Grade g.core (d i),paygrade s (v i) • vertex s):=
    funext (fun i=>(whole_grade _ ((GraphGrade.original g _).mp (pure i))).symm)
  calc
    name g n h k a x=F v:=rfl
    _=F (fun i=>∑s:Grade g.core (d i),paygrade s (v i) • vertex s):=congrArg F pieces
    _=∑s:GraphFore.grades g a,F (fun i=>paygrade (s i) (v i) • vertex (s i)):=F.map_sum _
    _=_:=by
      refine Finset.sum_congr rfl fun s _=>?_
      have cash:=F.map_smul_univ (fun i=>paygrade (s i) (v i)) (fun i=>vertex (s i))
      have filed:F (fun i=>vertex (s i))=earned g (GraphFore.mask g a s) h k x:=by
        exact marked g d (fun i=>low (own (s i)) le_rfl) h k x
      exact cash.trans (congrArg (fun z=>GraphFore.income g a s • z) filed)

theorem paid (a:Fin n→Ordinary.Label (B g))(pure:∀i,Ordinary.homogeneous (B g) (a i).1 (a i).2.val)
    (h k:ℕ)(x:Points n):
    name g n h k a x=∑w:Fin (h+1),up (Nat.le_of_lt_succ w.isLt) (GraphHomogeneous.price g a w.val k 0 x):=by
  rw [held g a pure]
  unfold earned
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _=>?_
  let row:Sec g.core w.val→ₗ[ℂ]Sec g.core h:=up (Nat.le_of_lt_succ w.isLt)
  let field (s:GraphFore.grades g a):Sec g.core w.val:=GraphBasisExterior.price g (GraphFore.mask g a s) w.val k 0 x
  have combine:GraphHomogeneous.price g a w.val k 0 x=∑s,GraphFore.income g a s • field s:=
    GraphTender.posting g (GraphFore.income g a) _ w.val k 0 x
  calc
    _=∑s:GraphFore.grades g a,row (GraphFore.income g a s • field s):=
      Finset.sum_congr rfl (fun s _=>(row.map_smul _ _).symm)
    _=row (∑s:GraphFore.grades g a,GraphFore.income g a s • field s):=(map_sum row _ _).symm
    _=_:=congrArg row combine.symm

theorem original (a:Fin n→Ordinary.Label (B g))(pure:∀i,Ordinary.homogeneous (B g) (a i).1 (a i).2.val)
    (h k:ℕ)(x:Points n):
    (name g n h k a x).val=∑w:Fin (h+1),(GraphHomogeneous.price g a w.val k 0 x).val:=by
  rw [paid g a pure]
  change (coeS h) (∑w:Fin (h+1),up (Nat.le_of_lt_succ w.isLt) (GraphHomogeneous.price g a w.val k 0 x))=_
  rw [map_sum]
  rfl
end IssuedMaxwell.GraphReconstituted
end
