import YM.Integration.WilsonVacuumPreResetFiniteIntegral

/-! The unaliased finite Wilson history, advanced by its own numerator and the measured cover reset. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonVacuumPreResetFiniteHistory
open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato
open WilsonVacuumPreResetFiniteIntegral (posted read)
open WilsonVacuumPreResetIndependentForecast (prescription)
open WilsonConditionalTaylorWheelRawCenter (collected)
open scoped Classical Topology BigOperators
variable {G:Gauge} (R:Run G) (u:G.ColorIndex)
local notation "V" => R.family.path.levels
variable (tags:∀j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)

def output (N j:ℕ) (n:Side) (X:Pap (wire G (n*(destination V N j).patch.L))):PChart G n:=
  let C:=prescription R u N j
  Wine.stamp (Wine.bookH C) (Wine.bookU C) (collected (posted R N j n (tags j n) X))

def action (N:ℕ):ℕ→ℕ→(n:Side)→Pap (wire G n)
  | 0,_,n=>Reef.seed G n
  | d+1,j,n=> -Blue.flash (output R u tags N j n (action N d (j+1) (n*(destination V N j).patch.L)))

theorem payment (simple:G.Simple) (v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(live:j<N)(n:Side):
    (story V R.metals.O N j).1 n=output R u tags N j n (read R N (j+1) (n*(destination V N j).patch.L)):=by
  let C:=pitch V R.metals.O N j
  let P:=destination V N j
  let S:=primary P.patch (V).clock.kernel n
  let upper:=(story V R.metals.O N (j+1)).1
  let X:=unripe V R.metals.O N j upper n
  let Y:=posted R N j n (tags j n) (read R N (j+1) (n*P.patch.L))
  obtain ⟨evaluated,bounds,pure⟩:=WilsonVacuumPreResetFiniteIntegral.original R simple live n (tags j n)
  have clean:lop X=collected Y:=WilsonConditionalTaylorWheelRawCenter.acquired X 2 bounds pure Y (plugζ S R.metals.O) evaluated
  have unit:constantCoeff C=1:=angle_tilt (A:=V) simple R.alloy.B.ratio live
  have named:C=prescription R u N j:=WilsonVacuumPreResetIndependentForecast.pitch_eq R u simple v rows live
  calc
    (story V R.metals.O N j).1 n=Blue.mix (Blue.back C) (lop X):=by
      rw [story_stride V R.metals.O live]
      rfl
    _=Wine.stamp (Wine.bookH C) (Wine.bookU C) (lop X):=WilsonConditionalTaylorWheelClock.allRows C unit _
    _=output R u tags N j n (read R N (j+1) (n*P.patch.L)):=by rw [named,clean];rfl

theorem birth (N:ℕ)(n:Side):read R N N n=Reef.seed G n:=by
  rw [WilsonVacuumPreResetFiniteIntegral.read,story_top]
  change -Blue.flash (topW G n)=Reef.seed G n
  rw [WilsonConditionalTaylorWheelBare.original,neg_neg,Mesa.top_word]

/-- Every finite period uses the same globally centered prior from the preceding age. -/
theorem original (simple:G.Simple) (v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    {N j:ℕ}(date:j≤N):∀n,read R N j n=action R u tags N (N-j) j n:=by
  induction date using Nat.decreasingInduction with
  | self=>
    intro n
    rw [Nat.sub_self,action,birth]
  | of_succ k live previous=>
    intro n
    rw [show N-k=(N-(k+1))+1 by omega,action,WilsonVacuumPreResetFiniteIntegral.read,payment R u tags simple v rows live]
    rw [previous _]

end YM.Integration.WilsonVacuumPreResetFiniteHistory
end
