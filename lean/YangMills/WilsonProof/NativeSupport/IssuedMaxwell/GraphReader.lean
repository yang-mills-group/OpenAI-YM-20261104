import YangMills.WilsonProof.NativeSupport.IssuedMaxwell.GraphExteriorMarket
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace IssuedMaxwell.GraphReader
open YM YM.Integration YM.FVA2 YM.XSpace YM.XSpace.Normalize YM.XSpace.Structure1
open YM.FVA2.O YM.FVA2.O.Score YM.FVA2.Dframe YM.FVA2.Scale
open PowerSeries Set YangMills.MSbar IssuedMaxwell.Reports
open scoped BigOperators Classical
variable (g:YangMills.GaugeGroup){n:ℕ}

def earned (u:Scan g.core n)(h k:ℕ)(x:Points n):Sec g.core h:=
  ∑w:Fin (h+1),up (Nat.le_of_lt_succ w.isLt) (GraphBasisExterior.price g u w.val k 0 x)

theorem issued (u:Scan g.core n)(h k:ℕ)(x:Points n):(earned g u h k x).val=
    ∑w:Fin (h+1),(GraphBasisExterior.price g u w.val k 0 x).val:=by
  change (coeS h) (∑w:Fin (h+1),up (Nat.le_of_lt_succ w.isLt) (GraphBasisExterior.price g u w.val k 0 x))=_
  rw [map_sum]
  rfl

def form (d:Fin n→ℕ)(h k:ℕ)(x:Points n):MultilinearMap ℂ (fun i=>(B g).sector (d i)) ((B g).sector h):=
  ∑s:(∀i,Toon g.core (d i)),(MultilinearMap.mkPiRing ℂ (Fin n) (earned g (fun i=>flash (s i)) h k x)).compLinearMap
    (fun i=>coord (s i))

def name:Ordinary.OPE (B g):=fun _ h k a x=>form g (fun i=>(a i).1) h k x (fun i=>(a i).2)

theorem recorded (d:Fin n→ℕ)(v:∀i,Sec g.core (d i))(h k:ℕ)(x:Points n):
    form g d h k x v=∑s:(∀i,Toon g.core (d i)),(∏i,coord (s i) (v i)) • earned g (fun i=>flash (s i)) h k x:=by
  simp only [form,sum_apply]
  exact Finset.sum_congr rfl fun s _=>rfl

theorem marked (d:Fin n→ℕ)(s:∀i,Toon g.core (d i))(h k:ℕ)(x:Points n):
    form g d h k x (fun i=>theory (s i))=earned g (fun i=>flash (s i)) h k x:=by
  rw [recorded,Finset.sum_eq_single s]
  · have unit (i:Fin n):coord (s i) (theory (s i))=(1:ℂ):=(pivotδ (s i) (s i)).trans (if_pos rfl)
    simp only [unit,Finset.prod_const_one,one_smul]
  · intro a _ ha
    have diff:∃i,a i≠s i:=by by_contra! eq;exact ha (funext eq)
    obtain ⟨i,hi⟩:=diff
    have zero:(∏j,coord (a j) (theory (s j)))=0:=Finset.prod_eq_zero (Finset.mem_univ i)
      (by rw [pivotδ,if_neg (Ne.symm hi)])
    rw [zero,zero_smul]
  · simp
end IssuedMaxwell.GraphReader
end
