import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionFundedAnnulus
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionCrossingDeterminant

/-! Original positive physical gallery. At most m predetermined balls
are tested. The same crossing sum, true scalar, and original singleton
means occur in the exact equation and the four-row analytic price. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace YM.Integration.FVA1Physical.Exchange.RoseCut
open Finset Lattice RG Wilson Marker QuadraticLocal Push.AbsoluteSums Push.AbsoluteSums.Animals
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}{V T I:Type}[Fintype V][DecidableEq V]{C:Census V}
  {o:V→Site n}{P:Rep G n}(A:Gallery T I o P C)

abbrev midBall (x:Site n)(j w:ℕ):Support n:=neighbors (j*(2*w)+w) x

/-- No geometric hypothesis on a physical individual actor and no nonzero
condition on a truncated scalar. The sole exceptional set is a fixed,
measurable true marginal event on the original torus. -/
theorem filed_annular_pair (w:V→ℝ)(wp:∀v,0<w v)(e κ:ℝ)
    (paid:A.K.Paid w P.p.B e κ)(en:0≤e)(small:κ≤1)(t:T)(U:Config G n)(live:0<P.eval U)
    (a b:V)(s:C.Mode)(pair:s.val={a,b})(m D:ℕ)
    (far:m*(2*width P.p D)<separation (o a) (o b))
    (out:U∉crowd P.p.threshold (neighbors (m*(2*width P.p D)) (o a)) m):
    ∃j:Fin m,U∈firstClear P.p.threshold (o a) j (width P.p D) ∧
    let L:=midBall (o a) j (width P.p D)
    let E:=crossedCash P.activities P.p U (fun i=>A.K.hard t i U) L
    let ν:ℂ:=P.activities.gas P.p U
    let u:=(A.gas t U).part (C.fire a)/ν
    let v:=(A.gas t U).part (C.fire b)/ν
    Poly.price w E≤Real.exp (-(e*D))*(ballCost (m*(2*width P.p D))*κ) ∧
    (ν-E.part C.quiet)*(ν*filedRow A t s U-
      (E.part s-u*E.part (C.fire b)-v*E.part (C.fire a)+u*v*E.part C.quiet))=
      (E.part (C.fire a)-u*E.part C.quiet)*(E.part (C.fire b)-v*E.part C.quiet):=by
  let h:=width P.p D
  obtain ⟨j,chosen⟩:=select_annulus P.p.threshold U (o a) m h out
  refine ⟨j,chosen,?_⟩
  let L:=midBall (o a) j h
  have booked:=selected_long P.activities P.p U (fun i=>A.K.hard t i U)
    (fun i=>A.K.charged t i U) (o a) j D chosen.1
  have order:(j:ℕ)*(2*h)+h≤m*(2*h):=by
    calc (j:ℕ)*(2*h)+h≤((j:ℕ)+1)*(2*h):=by rw [Nat.succ_mul j.val (2*h)];omega
         _≤m*(2*h):=Nat.mul_le_mul_right _ j.isLt
  have inside:o a∈L:=(neighbors_mem ..).2 (by simp)
  have outside:o b∉L:=fun n=>far.not_ge (((neighbors_mem ..).1 n).trans order)
  refine ⟨?_,filed_crossing_determinant A wp paid en t U live L a b inside outside s pair⟩
  have price:=crossed_cash_price A w wp e κ paid en small L L D t U
    (fun i active crosses=>⟨(booked i active crosses).1.le,(booked i active crosses).2⟩)
  have bigger:L⊆neighbors (m*(2*h)) (o a):=fun v seen=>(neighbors_mem ..).2 (((neighbors_mem ..).1 seen).trans order)
  have counted:L.card≤ballCost (m*(2*h)):=(card_le_card bigger).trans (neighbors_card ..)
  have κ0:=budget_nonneg (rooted_crossing_budget A w wp e κ paid en small (o a) D t U)
  exact price.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr counted) κ0) (Real.exp_nonneg _))

end YM.Integration.FVA1Physical.Exchange.RoseCut
