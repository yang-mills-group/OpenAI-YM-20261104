import YM.Integration.WilsonConditionalTaylorWheelVacuum
import YM.Integration.WilsonConditionalTaylorWheelBare
import YM.Integration.WilsonConditionalTaylorBulkHistory

/-! Exact agreement of the periodized *cover* Wilson birth used by the
upper winding estimator with the actual independent UV field, including
all periodic aliases on every, possibly short, finite torus. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorWheelBirth
open Lattice Wilson RG Precision Tree PhysicalNext.Repeat.Legato FormalBulk08 FormalBulk08.Reef FormalBulk08.Flat
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonConditionalTaylorBulkHistory WilsonConditionalTaylorWheelVacuum
open scoped Classical

theorem folded (G:Gauge) (n:Side): Winding.emera (lop (moon G)) n=topW G n:=by
  funext e r
  cases r with
  | zero=>rfl
  | succ r=>
    change lagoon ((lop (moon G)) e (r+1)) n=(lop (sprig (eWilson (G:=G) (c:=n)) 2)) e (r+1)
    simpa only [lop,Nat.succ_ne_zero,if_false] using (moon_wrap G e r n).symm

theorem original {G:Gauge} (R:Run G) (u:G.ColorIndex)
    (wood:∀j,Lodge (R.family.path.levels.clock.op j 0).patch)
    (tags:∀j n,(primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (N:ℕ) (n:Side):
    signed R N N n=course R u wood tags N N n:=by
  rw [ultraviolet,signed,actionW,story_top]
  change -flash (Winding.emera (lop (moon G)) n)=Reef.seed G n
  rw [folded,WilsonConditionalTaylorWheelBare.original,neg_neg,Mesa.top_word]

end YM.Integration.WilsonConditionalTaylorWheelBirth
end

