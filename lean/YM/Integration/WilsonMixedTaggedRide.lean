import YM.Integration.WilsonMixedTaggedStart

/-! Normalize a genuine adjacent Wilson ride and insert its vacant tagged copy. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMixedTaggedRide
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Bid
open Extra.Histories Push Local Planned.GuardedAtom Guard MergeProof RG05Readout RG05Readout.Address
open WilsonMixedTaggedRoster WilsonMixedTaggedOutput
open scoped Topology Classical

variable {G:Gauge}{n m:Side}{F:Rep G m}{R:Rep G n}{D:GaugeDoor F R}{S:StepData n m}

theorem normal {a:Site m}{b:Site n}{ν:ℂ}{I:Three G m}{Q:Three G n}{l:ℝ}
    (h:Ride S a b D ν I Q l) (unit:1 ≤ ‖ν‖) : Ride S a b D 1 I (ν⁻¹ • Q) l := by
  have paid:=h.matchPay 1 ν⁻¹ 1 (show _=_ by
    rw [inv_mul_cancel₀,one_mul]
    exact norm_pos_iff.mp (zero_lt_one.trans_le unit))
  rw [one_smul,norm_one,norm_inv,max_eq_left (inv_le_one_of_one_le₀ unit),one_mul] at paid
  exact paid

theorem doubled {V:Type}{I:V → Three G m}{Q:V → Three G n}{l:V → ℝ}
    {a:V → Site m}{b:V → Site n} (h:∀v,Ride S (a v) (b v) D 1 (I v) (Q v) (l v)) :
    ∀v:V×Bool,Ride S (a v.1) (b v.1) D 1 (liveRow I v) (liveRow Q v) (liveRow l v) := by
  rintro ⟨v,bit⟩
  cases bit
  · exact h v
  · exact Ride.vac

theorem room {V:Type} {w l:V → ℝ} (cost:∀i,2*w i*l i ≤ 1) :
    ∀v:V×Bool,2*w v.1*liveRow l v ≤ 1 := by
  rintro ⟨v,bit⟩
  cases bit
  · exact cost v
  · simp [liveRow]

end YM.Integration.WilsonMixedTaggedRide
