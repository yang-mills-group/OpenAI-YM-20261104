import YM.Integration.WilsonPhysicalHistoryRetainedSpringTemperature

/-! The two true signed finite pitch sums can each be spent at any fixed
subpower of the incoming regulator. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.OriginalMarkedRunAction
open Filter Lattice Wilson RG Precision Comparison.RG02 Comparison.RG02.Assembly
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Blue WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Wheel
open WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Physical WilsonLimitConstruction PowerSeries
open scoped Topology BigOperators Classical
variable {G : Gauge}

theorem pitch_subpower (R : Run G) (simple : G.Simple) (v : ℕ→Gear G→ℝ)
    (rows : FundedMarkedCoverRows.prices v R.kit) (r : ℕ) {η : ℝ} (ep : 0<η) :
    ∀ᶠ j : ℕ in atTop, ∀ N>j,∀ n : ℕ,
      let g:=Pert.Asymptotics.regulatorRun R.family N n j
      let c:=(r-2+1:ℕ)*g^(-η)
      |R.alloy.B.kin.alpha N j|≤g^(-η) ∧ |pitchPolynomial R N j r g|≤c ∧ |pitchTail R N j r g|≤c := by
  obtain ⟨T,paid⟩:=cofinal_pitch R simple v rows (r+2)
  filter_upwards [paid,exp_at_band T R.family.path.levels simple η ep,
    IterationFour.Currency.g_small simple R.makes 1 zero_lt_one] with j credit bound small
  intro N later n g c
  have gp : 0<g:=IterationFour.Currency.g_pos R.makes N n j later.le
  have size : |g|≤1:=by rw [abs_of_pos gp]; exact (small N n later.le).le
  have cap : T.buy (zz R.family.path.levels j)≤g^(-η):=by
    apply le_trans _ (bound (R.family.path.β N n j) (R.makes.wilson.represents N n j later.le).band.1)
    linarith [Real.add_one_le_exp (T.buy (zz R.family.path.levels j))]
  have costs:=poly_price R N j r size (credit N later)
  have scaled:=mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α:=ℝ) (r-2+1))
  have head : coeff 2 (pitch R.family.path.levels R.metals.O N j)=R.alloy.B.kin.alpha N j :=
    (alpha_stable simple R.alloy.B.ratio R.alloy.B.support later.le).2 later
  exact ⟨(head ▸ credit N later 2 (by omega)).trans cap,costs.1.trans scaled,costs.2.trans scaled⟩

end YM.Integration.OriginalMarkedRunAction
