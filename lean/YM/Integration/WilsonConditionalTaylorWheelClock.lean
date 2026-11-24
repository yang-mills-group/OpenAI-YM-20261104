import YM.Integration.WilsonConditionalTaylorMarkedStamp
import YM.WilsonCoeffUV.Vacuum.UV.RatioLimit

/-! The two original finite-field algorithms for a coupling change agree on
the very same incoming scalar, with their signed field and power factors.
The scalar read from distinct vacuum fields is kept separate. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelClock
open PowerSeries FormalBulk08 FormalBulk08.Wine FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava
open Lattice RG Wilson WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Blue
open scoped Classical BigOperators
variable {G:Gauge}

theorem root (H:Cost) (hc:constantCoeff H=1):Blue.pace H=Wine.nextU H:=by
  have hf:Wine.Fresh H:=(coeff_zero_eq_constantCoeff_apply H).trans hc
  have nz:H≠0:=fun h=>by rw [h,map_zero] at hc;exact zero_ne_one hc
  have squares:(Blue.pace H)^2=(Wine.nextU H)^2:=
    mul_left_cancel₀ nz ((Blue.pace_tax hc).trans (Wine.post_grid H hf).symm)
  have price:(Blue.pace H-Wine.nextU H)*(Blue.pace H+Wine.nextU H)=0:=by
    calc
      _=(Blue.pace H)^2-(Wine.nextU H)^2:=by ring
      _=0:=sub_eq_zero.mpr squares
  rcases mul_eq_zero.mp price with same|opposite
  · exact sub_eq_zero.mp same
  · have paid:=congrArg PowerSeries.constantCoeff opposite
    have one:constantCoeff (Wine.nextU H)=1:=(coeff_zero_eq_constantCoeff_apply _).symm.trans (Wine.fresh_N H)
    rw [map_add,Blue.pace_cc hc,one,map_zero] at paid
    norm_num at paid

theorem returned (H:Cost) (hc:constantCoeff H=1):Blue.back H=Wine.bookH H:=by
  have old:Blue.oldG H=Wine.wake H:=by rw [Blue.oldG,Wine.wake,root H hc,mul_comm]
  have fresh:Blue.freshG H=Wine.runic H:=by
    rw [Blue.freshG,dif_pos hc]
    unfold Wine.runic
    congr 1
  have cancellation:=Blue.fresh_back (f:=H)
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R:=ℝ))
  calc
    X*Blue.back H=Blue.back H*X:=mul_comm _ _
    _=Blue.freshG H:=cancellation
    _=Wine.runic H:=fresh
    _=X*Wine.bookH H:=(Wine.forward_green H).symm

theorem outgoing (H:Cost) (hc:constantCoeff H=1):(Blue.back H)⁻¹=Wine.bookU H:=by
  rw [returned H hc]
  have one:constantCoeff (Wine.bookH H)=1:=(coeff_zero_eq_constantCoeff_apply _).symm.trans (Wine.book_fresh H)
  have nz:Wine.bookH H≠0:=fun h=>by rw [h,map_zero] at one;exact zero_ne_one one
  apply mul_left_cancel₀ nz
  exact (PowerSeries.mul_inv_cancel _ (one.trans_ne one_ne_zero)).trans (Wine.book_equal H).symm

theorem allRows {V:Type} (H:Cost) (hc:constantCoeff H=1) (T:OrbitV V):
    Blue.mix (Blue.back H) T=Wine.stamp (Wine.bookH H) (Wine.bookU H) T:=by
  funext e r
  change (∑i∈Finset.range (e+1), coeff (e-i) ((Blue.back H)^i*((Blue.back H)⁻¹)^r) • T i r)=_
  rw [outgoing H hc,returned H hc]
  rfl

theorem onRealm {e:ℕ} (Q:Realm G (e+1) Credit.leanC) (N t:ℕ) (live:t<N):
    ratioHigh Q.draws Q.paid N t=Wine.bookH (pitch Q.draws Q.paid N t) ∧
    (ratioHigh Q.draws Q.paid N t)⁻¹=Wine.bookU (pitch Q.draws Q.paid N t) ∧
    ∀(V:Type)(T:OrbitV V),Blue.mix (ratioHigh Q.draws Q.paid N t) T=
      Wine.stamp (Wine.bookH (pitch Q.draws Q.paid N t)) (Wine.bookU (pitch Q.draws Q.paid N t)) T:=by
  have due:=angle_tilt (A:=Q.draws) Q.hG Q.green live
  exact ⟨returned _ due,outgoing _ due,fun _ T=>allRows _ due T⟩

end YM.Integration.WilsonConditionalTaylorWheelClock
end

