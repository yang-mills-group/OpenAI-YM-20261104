import YM.Integration.WilsonRootedKioskRegularRate
import YM.Integration.WilsonMovingMentorPageCoupling

/-! The explicit input stipend used by the received Q course, priced together
with the actual dated original burn and the full course fidelity. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonOriginalCompensatedTuition
open Filter RG Pressure PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6 QuadraticLocal AllOrder
open scoped Topology

theorem salary {G:Gauge} (R:Run G) (simple:G.Simple) (p grade k:ℕ)
    (deep:2*p+8≤grade) (old:p+3≤3*k+2) {ε:ℝ} (positive:0<ε) :
    ∀ᶠ i:ℕ in atTop,∀ N per,i<N → ∀ Ω:ℝ,0<Ω →
      Ω≤R.alloy.B.a.clock.hatBeta (i+1)^(Beaming.grain (R.alloy.B.a.clock.J i)) →
      let x:=R.alloy.B.a.clock.hatBeta (i+1)
      let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
      let fine:=betaF G (R.alloy.B.a.clock.hatBeta i) (R.rolls.L (R.alloy.B.a.clock.J (i+1)))
      8*Ω*(Ω⁻¹*x^(-(grade:ℝ))+Burn.young x k+fine^Mentor.Tuition.need grade
        (Mentor.Tolerance (R.alloy.B.a.clock.J i)))≤ε*g^p := by
  have wage:=WilsonRootedKioskRegularRate.salary R simple (p+1) grade k (by omega) (by omega)
  have rent:=WilsonMovingMentorMarkedRate.original R simple p (p+1) (by omega)
    (div_pos positive (by norm_num : (0:ℝ)<16))
  have slack:=WilsonMovingMentorPageCoupling.repaid R simple 0 p
    (div_pos positive (by norm_num : (0:ℝ)<2))
  filter_upwards [wage,rent,slack] with i first second fitted
  intro N per live Ω op cap x g fine
  obtain ⟨e,ep,_,budget⟩:=first N per live Ω op.le cap
  have lower:-(grade:ℝ)≤WilsonMovingMentorMarkedRate.exponent (p+1):=by
    have bound:(2:ℝ)*p+8≤grade:=by exact_mod_cast deep
    unfold WilsonMovingMentorMarkedRate.exponent
    push_cast
    have np:0≤(p:ℝ):=by positivity
    linarith
  have xg:1≤x:=(R.alloy.B.a.fits.delayed _).le
  have money:x^(-(grade:ℝ))≤(ε/16)*g^p :=
    (Real.rpow_le_rpow_of_exponent_le xg lower).trans
      (second N per (i+1) (by omega) (by omega))
  have tau:g^(p+1)≤(ε/2)*g^p:=by
    simpa only [pow_zero,one_mul] using fitted Ω op.le cap N per live
  let bill:=Burn.young x k+fine^Mentor.Tuition.need grade (Mentor.Tolerance (R.alloy.B.a.clock.J i))
  have billPaid:8*Ω*bill≤g^(p+1):=by
    calc
      8*Ω*bill ≤ 8*Ω*(e+bill):=mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ep.le) (by positivity)
      _ ≤ g^(p+1):=by simpa only [bill,add_assoc] using budget
  have cancel:8*Ω*(Ω⁻¹*x^(-(grade:ℝ))+bill)=8*x^(-(grade:ℝ))+8*Ω*bill:=by
    field_simp [op.ne']
  change 8*Ω*(Ω⁻¹*x^(-(grade:ℝ))+Burn.young x k+_)≤_
  rw [add_assoc,cancel]
  linarith [billPaid.trans tau]

end YM.Integration.WilsonOriginalCompensatedTuition
