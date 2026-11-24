import YM.Integration.WilsonReceivedDepositedAlias
import YM.Integration.WilsonReceivedDepositedSocketRows

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedDepositedOrbitalSlice
open Finset Marker Multi Comparison.RG02 Comparison.RG02.Order
open scoped Classical BigOperators
variable {V W:Type} [DecidableEq V][Fintype V][DecidableEq W][Fintype W]
variable {A:Census V}{J:Census W}{r:ℕ}

/-- The complete marked polynomial with one particular set of thermal labels. -/
def slice (x:Grade A r)(t:Index r):Poly A:=
  Poly.inject fun s=>x.part (Join.pair s t)

private lemma reorder {X Y:Type}[Fintype X][Fintype Y](f:X→Y→X→Y→ℂ):
    (∑i,∑u,∑k,∑v,f i u k v)=∑u,∑v,∑i,∑k,f i u k v:=by
  rw [Finset.sum_comm (s:=univ (α:=X)) (t:=univ (α:=Y))]
  refine Finset.sum_congr rfl fun u _=>?_
  calc
    (∑i,∑k,∑v,f i u k v)=∑i,∑v,∑k,f i u k v:=
      Finset.sum_congr rfl fun i _=>Finset.sum_comm
    _=∑v,∑i,∑k,f i u k v:=Finset.sum_comm

theorem slice_mul (x y:Grade A r)(t:Index r):
    slice (x*y) t=∑u:Index r,∑v:Index r,
      if Poly.merges u v t then slice x u*slice y v else 0:=by
  apply Marker.Poly.ext
  intro s
  change (x*y).part (Join.pair s t)=_
  rw [Join.pair_product]
  rw [reorder]
  simp_rw [Poly.part_sum]
  refine Finset.sum_congr rfl fun u _=>Finset.sum_congr rfl fun v _=>?_
  by_cases h:Poly.merges u v t
  · simp only [h,if_true,and_true,Poly.part_mul]
    rfl
  · simp [h]

theorem slice_one (t:Index r):
    slice (1:Grade A r) t=if t=(indices r).quiet then 1 else 0:=by
  apply Marker.Poly.ext
  intro s
  change (1:Grade A r).part (Join.pair s t)=_
  rw [Join.one_pair]
  by_cases h:t=(indices r).quiet <;> simp [h,Poly.one_part]

def lift (F:Poly A →ₐ[ℂ] Poly J)(x:Grade A r):Grade J r:=
  Poly.inject fun k=>(F (slice x (Join.right k))).part (Join.left k)

theorem at_pair (F:Poly A →ₐ[ℂ] Poly J)(x:Grade A r)(s:J.Mode)(t:Index r):
    (lift F x).part (Join.pair s t)=(F (slice x t)).part s:=by
  change (F (slice x (Join.right (Join.pair s t)))).part (Join.left (Join.pair s t))=_
  simp only [Join.right_pair,Join.left_pair]

theorem at_slice (F:Poly A →ₐ[ℂ] Poly J)(x:Grade A r)(t:Index r):
    slice (lift F x) t=F (slice x t):=Marker.Poly.ext fun s=>at_pair F x s t

def hom (F:Poly A →ₐ[ℂ] Poly J)(r:ℕ):Grade A r →ₐ[ℂ] Grade J r where
  toFun:=lift F
  map_zero' :=Join.both_parts fun s t=>by
    rw [at_pair,show slice (0:Grade A r) t=0 from rfl,map_zero]; rfl
  map_one' :=Join.both_parts fun s t=>by
    rw [at_pair,slice_one,Join.one_pair]
    by_cases h:t=(indices r).quiet <;> simp [h,Poly.one_part]
  map_add' x y:=Join.both_parts fun s t=>by
    rw [at_pair,show slice (x+y) t=slice x t+slice y t from rfl,map_add,
      Poly.part_plus,Poly.part_plus,at_pair,at_pair]
  map_mul' x y:=Join.both_parts fun s t=>by
    change (slice (lift F (x*y)) t).part s=(slice (lift F x*lift F y) t).part s
    rw [at_slice,slice_mul,slice_mul]
    simp_rw [map_sum,at_slice]
    congr 1
    refine Finset.sum_congr rfl fun u _=>Finset.sum_congr rfl fun v _=>?_
    by_cases h:Poly.merges u v t <;> simp [h]
  commutes' c:=Join.both_parts fun s t=>by
    rw [Algebra.algebraMap_eq_smul_one,Algebra.algebraMap_eq_smul_one]
    change (lift F (c • (1:Grade A r))).part _=(c • (1:Grade J r)).part _
    rw [at_pair,show slice (c • (1:Grade A r)) t=c • slice (1:Grade A r) t from rfl,
      map_smul,Poly.part_smul,Poly.part_smul,slice_one,Join.one_pair]
    by_cases h:t=(indices r).quiet <;> simp [h,Poly.one_part]

theorem observe (F:Poly A →ₐ[ℂ] Poly J)(x:Grade A r)(j:ℕ):
    Order.observe J r (hom F r x) j=F (Order.observe A r x j):=by
  unfold Order.observe
  by_cases h:j≤r
  · rw [if_pos h,if_pos h]
    change ((j.factorial:ℂ)⁻¹) • slice (lift F x) (pick r j)=F (((j.factorial:ℂ)⁻¹) • slice x (pick r j))
    rw [at_slice,map_smul]
  · rw [if_neg h,if_neg h,map_zero]

end YM.Integration.WilsonReceivedDepositedOrbitalSlice
end
