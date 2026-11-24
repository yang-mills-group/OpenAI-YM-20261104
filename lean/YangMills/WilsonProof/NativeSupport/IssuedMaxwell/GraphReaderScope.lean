import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphReader
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphReaderScope
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.Dframe YM.FVA2.Scale
open PowerSeries Set YangMills.MSbar IssuedMaxwell.Reports IssuedMaxwell.GraphReader
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}

theorem inherited (d D:Fin n→ℕ)(room:∀i,d i≤D i)(v:∀i,Sec g.core (d i))(h k:ℕ)(x:Points n):
    form g d h k x v=form g D h k x (fun i=>up (room i) (v i)):=by
  let F:MultilinearMap ℂ (fun i=>(B g).sector (d i)) ((B g).sector h):=
    (form g D h k x).compLinearMap (fun i=>up (room i))
  have pieces:v=(fun i=>∑s:Toon g.core (d i),coord s (v i) • theory s):=
    funext (fun i=>(all_sig (v i)).symm)
  rw [recorded]
  change _=F v
  symm
  calc
    F v=F (fun i=>∑s:Toon g.core (d i),coord s (v i) • theory s):=congrArg F pieces
    _=∑s:(∀i,Toon g.core (d i)),F (fun i=>coord (s i) (v i) • theory (s i)):=F.map_sum _
    _=_:=by
      refine Finset.sum_congr rfl fun s _=>?_
      have linear:=F.map_smul_univ (fun i=>coord (s i) (v i)) (fun i=>theory (s i))
      have promoted (i:Fin n):up (room i) (theory (s i))=theory (enroll (room i) (s i)):=lift_sig ..
      have filed:F (fun i=>theory (s i))=earned g (fun i=>flash (s i)) h k x:=by
        change form g D h k x (fun i=>up (room i) (theory (s i)))=_
        simp_rw [promoted]
        exact marked g D (fun i=>enroll (room i) (s i)) h k x
      exact linear.trans (congrArg (fun z=>(∏i,coord (s i) (v i)) • z) filed)

theorem original (a b:Fin n→Ordinary.Label (B g))(equal:∀i,(a i).2.val=(b i).2.val)(h k:ℕ)(x:Points n):
    name g n h k a x=name g n h k b x:=by
  let D (i:Fin n):=max (a i).1 (b i).1
  have left (i:Fin n):(a i).1≤D i:=le_max_left .. 
  have right (i:Fin n):(b i).1≤D i:=le_max_right ..
  have same:(fun i=>up (left i) (a i).2)=(fun i=>up (right i) (b i).2):=funext (fun i=>Subtype.ext (equal i))
  calc
    _=form g D h k x (fun i=>up (left i) (a i).2):=inherited g _ D left _ h k x
    _=form g D h k x (fun i=>up (right i) (b i).2):=congrArg (form g D h k x) same
    _=_:=(inherited g _ D right _ h k x).symm

theorem collision (simple:g.IsSimple)(a:Fin n→Ordinary.Label (B g))(h k:ℕ)(x:Points n)(hx:x∉conf n):
    name g n h k a x=0:=by
  unfold name
  rw [recorded]
  refine Finset.sum_eq_zero fun s _=>?_
  have zero:earned g (fun i=>flash (s i)) h k x=0:=by
    unfold earned
    refine Finset.sum_eq_zero fun w _=>?_
    rw [(GraphExteriorMarket.original g simple (fun i=>flash (s i))).collision w.val k 0 x hx]
    exact (up (Nat.le_of_lt_succ w.isLt)).map_zero
  rw [zero,smul_zero]
  rfl
end IssuedMaxwell.GraphReaderScope
end
