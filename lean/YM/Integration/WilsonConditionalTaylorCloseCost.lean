import YM.Integration.WilsonConditionalTaylorCapture
import YM.WilsonCoeffUV.Emit.Expense
import YM.Pert.Asymptotics.RawAxis

/-! The short span keeps its genuine dilation *and* its number of dates. A
fixed polynomial allowance in the log-log clock spends arbitrarily little
true coupling, simultaneously for every physical cutoff and side. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonConditionalTaylorCloseCost
open Filter Lattice RG Wilson Next.Foundations PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark WilsonCoeffUV.Wheel.Cadenza
open WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Shard WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Mer.Patrol
open WilsonCoeffUV.Embroider WilsonConditionalTaylorSeparatedPurchase WilsonConditionalTaylorCapture
open scoped Classical BigOperators Topology
variable {G:Gauge}

theorem priced (R:Run G) (simple:G.Simple) (T U:Credit) (η:ℝ) (pos:0<η):
    let A:=R.family.path.levels
    ∀ᶠ b:ℕ in atTop, ∀m≥b,∀N≥m,∀per:ℕ,
    A.S.scale m-A.S.scale b+((m-b:ℕ):ℝ)≤U.buy (zz A b) →
    Real.exp (T.buy (zz A b+(A.S.scale m-A.S.scale b)+((m-b:ℕ):ℝ))) ≤
        (Pert.Asymptotics.regulatorRun R.family N per b)^(-η):=by
  intro A
  let S:=Credit.leanC.plus U
  have quote:=WilsonCoeffUV.Physical.exp_at_band (T.usingC S) A simple η pos
  filter_upwards [quote,(WilsonCoeffUV.Physical.stamp_lim A simple).eventually_ge_atTop 1] with b pay warm
  intro m bm N mn per short
  have before:1≤zz A b+(A.S.scale m-A.S.scale b)+((m-b:ℕ):ℝ):=by
    linarith [PathCost.scales A.S bm,show 0≤((m-b:ℕ):ℝ) by positivity]
  have size:=Credit.fuel Credit.leanC U warm
  have unit:Credit.leanC.buy (zz A b)=zz A b:=by simp [Credit.leanC,Credit.buy]
  rw [unit] at size
  have charged:=T.elder before (show zz A b+(A.S.scale m-A.S.scale b)+((m-b:ℕ):ℝ) ≤ S.buy (zz A b) by linarith)
  have band: A.clock.hatBeta b/2 ≤ R.family.path.β N per b :=(R.makes.wilson.represents N per b (bm.trans mn)).band.1
  have paid:=pay _ band
  rw [Credit.stock_up] at paid
  exact (Real.exp_le_exp.mpr charged).trans paid

end YM.Integration.WilsonConditionalTaylorCloseCost
end

