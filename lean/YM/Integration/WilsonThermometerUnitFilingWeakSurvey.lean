import YM.Integration.WilsonThermometerUnitFilingWeakKernel
import YM.FormalBulk08.Flat.Plans
import YM.Next.FREE_KERNELS.Primal
import YM.Next.FREE_KERNELS.Current

/-! Common pre-length strip for the repeated Gaussian maps and the singly inserted conditional covariance. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingWeakSurvey
open Function Filter Finset Lattice Laurent Bloch Metric Exterior Precision RG Next.Free Work.F08 Craft Bid
open FormalBulk08 Flat Work.F08 Stationary
open scoped Classical BigOperators Matrix
variable {G:Gauge}{j t:ℕ}

structure Staff (G:Gauge) (K:KernelChoices) (j t:ℕ) (σ b:ℝ) : Prop where
  linear : ∀P:Flight j t, RepeatPrices K.penalty σ b P
  curvature : ∀P:Flight j t,∀l:List Axis,l.length≤j-2→
    (advanceC P.L (Flight.psi K.penalty P) l).strip σ (b/(P.L.val:ℝ)^(2+l.length))
  conditional : ∀P:Patch,P.J=j→∀F:Lodge P,∃c:ℝ,0<c ∧
    ∀(A:Levels G)(i N M:ℕ),i<N→N≤M→A.clock.J i=t→
    ∀h:(A.clock.op i 0).patch=P,∀hh:(A.clock.op i 0).patch.Branches K G,
    let z:=destination A N i
    let f:Lodge (A.clock.op i 0).patch:=h.symm ▸ F
    (Flat.gamma G K z f hh).strip σ c ∧ (Flat.locating G K z f).strip σ c ∧
      (Flat.roots G K z f).strip σ c

theorem original (G:Gauge) (K:KernelChoices) {j t:ℕ}(hj:4≤j)(ht:4≤t):
    ∃σ b:ℝ,0<σ ∧ 0<b ∧ Staff G K j t σ b:=by
  obtain ⟨w,B,wp,Bp,repeated,paid⟩:=Flat.may_use G K j t hj ht
  obtain ⟨η,C,ηp,Cp,curv⟩:=(Flight.status_quote K.penalty K.penalty_pos hj ht).honored hj 2
  refine ⟨min w η,max B C,lt_min wp ηp,Bp.trans_le (le_max_left ..),?_,?_,?_⟩
  · intro P l hl
    obtain ⟨a,b⟩:=repeated P l hl
    exact ⟨strip_mono a (min_le_left ..) (div_le_div_of_nonneg_right (le_max_left ..) (by positivity)),
           strip_mono b (min_le_left ..) (div_le_div_of_nonneg_right (le_max_left ..) (by positivity))⟩
  · intro P l hl
    have h:(advanceC P.L (Flight.psi K.penalty P) l).strip η (C/(P.L.val:ℝ)^(2+l.length)):=by
      simpa only [div_eq_mul_inv,Flight.fee,Flight.psi] using curv P l hl
    exact strip_mono h (min_le_right ..) (div_le_div_of_nonneg_right (le_max_right ..) (by positivity))
  · intro P stage F
    obtain ⟨c,cp,ch⟩:=paid P stage F
    refine ⟨c,cp,?_⟩
    intro A i N M hi nm start he hh
    have claim:=ch A i N M hi nm start he hh
    exact ⟨strip_mono claim.single (min_le_left ..) le_rfl,
      strip_mono claim.mean (min_le_left ..) le_rfl,strip_mono claim.root (min_le_left ..) le_rfl⟩

/-- Exterior differentiation selects the actual curvature prolongation on every finite course replica. -/
theorem differentiated (K:KernelChoices) {j t:ℕ}(D:Flight j t)(ht:4≤t)(c:Side):
    let f:=c*D.L
    let v:=D.visitRatio (show f.val=c.val*D.L.val from PNat.mul_coe ..)
    Exterior.d 1 f * installed v (D.duo K.penalty).A0=installed v (D.psi K.penalty)*Exterior.d 1 c:=by
  let f:=c*D.L
  have hc:f.val=c.val*D.L.val:=PNat.mul_coe ..
  let v:=D.visitRatio hc
  let k:=K.penalty
  let B:=(blue k D.wing).acts f
  let A:=(pink k D.wing).acts f
  let W:=(pink k D.land).acts c
  let T:=installed v (D.duo k).T
  let X:=installed v (D.duo k).A0
  change d 1 f*X=installed v (D.psi k)*d 1 c
  rw [D.psi_bridge k K.penalty_pos ht hc]
  change d 1 f*X=((B*T)*W)*d 1 c
  have he:A*B=1:=(heart_inverse k K.penalty_pos D.legal D.wing _).1
  have hp:T*W*d 1 c=A*d 1 f*X:=(D.tangent K ht hc).2.2
  rw [Matrix.mul_assoc B,Matrix.mul_assoc B,hp,←Matrix.mul_assoc,←Matrix.mul_assoc,
    _root_.mul_eq_one_comm.mp he,Matrix.one_mul]

end YM.Integration.WilsonThermometerUnitFilingWeakSurvey
