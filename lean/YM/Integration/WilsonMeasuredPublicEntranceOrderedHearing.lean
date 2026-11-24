import YM.Integration.WilsonMeasuredPublicEntranceOrderedBasis
/-! Signed readings of finite physical panels use one ultraviolet limit per true period, uniformly over every bounded choice of the original input columns. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceOrderedHearing
open Filter Finset Function Extraction Table Spec Next.UVStress
open WilsonMeasuredPublicEntranceOrderedBasis
open scoped Classical Topology BigOperators
variable {G:Gauge}{C:Family G}{order:Extraction.Order}{S:Table C.book}{n:ℕ}
  {d:Fin n→ℕ}{φ:Test n}{H:Fin n→ℝ}(r:Release (C:=C) (order:=order) (S:=S) d φ H)
  {I:Type*}(s:Finset I)(μ:I→ℂ)

theorem sum_bound {A B:I→ℂ}{t:ℝ}(paid:∀i∈s,‖A i-B i‖≤t):
    ‖(∑i∈s,μ i*A i)-(∑i∈s,μ i*B i)‖≤(∑i∈s,‖μ i‖)*t:=by
  simp only [←sum_sub_distrib,←mul_sub,sum_mul]
  apply (norm_sum_le _ _).trans
  exact sum_le_sum (fun i hi=>by rw [norm_mul];exact mul_le_mul_of_nonneg_left (paid i hi) (norm_nonneg _))

theorem fine (N p:ℕ)(v:I→C.book.Vector d)(cap:∀i∈s,∀j,‖v i j‖≤H j):
    ‖(∑i∈s,μ i*finiteValue d φ N p (v i))-(∑i∈s,μ i*form d (r.period p) (v i))‖≤
      (∑i∈s,‖μ i‖)*r.ultraviolet N p:=
  sum_bound s μ (fun i hi=>r.fine N p (v i) (cap i hi))

theorem volume (p:ℕ)(v:I→C.book.Vector d)(cap:∀i∈s,∀j,‖v i j‖≤H j):
    ‖(∑i∈s,μ i*form d (r.period p) (v i))-(∑i∈s,μ i*publicValue (S:=S) d φ (v i))‖≤
      (∑i∈s,‖μ i‖)*r.volume p:=
  sum_bound s μ (fun i hi=>r.outer p (v i) (cap i hi))

include r in
theorem ordered {ε:ℝ}(ep:0<ε):order.late fun N p=>
    ∀v:I→C.book.Vector d,(∀i∈s,∀j,‖v i j‖≤H j) →
      ‖(∑i∈s,μ i*finiteValue d φ N p (v i))-(∑i∈s,μ i*publicValue (S:=S) d φ (v i))‖≤
        (∑i∈s,‖μ i‖)*ε:=by
  have small:0<ε/2:=half_pos ep
  filter_upwards [r.suitable,r.second.eventually (gt_mem_nhds small)] with k room outer
  filter_upwards [(r.first (order.per k) room).eventually (gt_mem_nhds small)] with j inner
  intro v cap
  apply sum_bound s μ
  intro i hi
  calc
    _ ≤ ‖finiteValue d φ (order.mesh j) (order.per k) (v i)-form d (r.period (order.per k)) (v i)‖+
        ‖form d (r.period (order.per k)) (v i)-publicValue (S:=S) d φ (v i)‖:=norm_sub_le_norm_sub_add_norm_sub .. 
    _ ≤ r.ultraviolet (order.mesh j) (order.per k)+r.volume (order.per k):=
      add_le_add (r.fine _ _ _ (cap i hi)) (r.outer _ _ (cap i hi))
    _ ≤ ε:=by change r.ultraviolet (order.mesh j) (order.per k)<ε/2 at inner;change r.volume (order.per k)<ε/2 at outer;linarith

end YM.Integration.WilsonMeasuredPublicEntranceOrderedHearing
end
