import YM.Integration.WilsonRootedHeldAffineWallet
import YM.Integration.WilsonRootedPhysicalTagLaw

/-! The co-bought normal-center estimate on the actual original Cash station at every held medium. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonRootedHeldAffineStation
open Function Lattice Wilson RG Tree Pressure Pressure.Stores Matrix
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open ConnectedActivityE6 Coat Control Window Census Blaze Matter Greenbelt
open RG.Supply RG.Shoot Input Org Push Push.PriceCompiler Precision SectorMeasure Oriented
open WilsonLimitConstruction
open scoped Topology BigOperators Classical

variable {G:Gauge}(R:Run G){N per m:ℕ} (P:FundedCensusVacuum.Station R N per m)
local notation "A₀" => R.alloy.B.a
local notation "Sₘ" => R.alloy.B.a.clock.op m per
local notation "Tₘ" => Pressure.Testing.ships R.alloy.B N m per
local notation "J₁" => R.alloy.B.a.clock.J (m+1)
local notation "J₀" => R.alloy.B.a.clock.J m
local notation "xₘ" => R.alloy.B.a.clock.hatBeta m
local notation "oₘ" => R.kit.shape.o J₁ J₀

include P

theorem original (paid:WilsonRootedHeldAffineWallet.Eligible R.kit) (χ:Chi)
    (V:Config G (R.family.side m per)) (p:Molecule Sₘ)(i:Greenbelt.Reserve Sₘ)
    (tag:(Sₘ).Choices)(y:(Greenbelt.allot i).Slice G):
    let X:=WilsonRootedHeldAffineCenter.held Tₘ xₘ (oₘ).K χ V p i tag y
    X.manifest ∧ X.plate *ᵥ WilsonRootedHeldAffineCenter.full X+X.linearBill=0 ∧
      ‖X.μ-erect G (WilsonRootedHeldAffineCenter.full X)‖≤
        (betaF G xₘ (R.rolls.L J₁))^(-(J₀:ℝ)):=by
  intro X
  obtain ⟨trueX,eqn,-,-,each⟩:=WilsonRootedHeldAffineCenter.original P.guide χ V p i tag y
  refine ⟨trueX,eqn,?_⟩
  have time:=paid J₁ J₀ (step_paid A₀ m) xₘ (R.alloy.B.valid.pays m)
  have bound:(Fintype.card G.ColorIndex:ℝ)*(2*((oₘ).ample*distPay (oₘ).eta (oₘ).gap (oₘ).ample
      (tubularPrice G (R.rolls.L J₁)) X.B)*((oₘ).cap*X.t))≤betaF G xₘ (R.rolls.L J₁)^(-(J₀:ℝ)):=by
    change (Fintype.card G.ColorIndex:ℝ)*(2*((oₘ).ample*distPay _ _ _ _ _)*((oₘ).cap*
      fiery G xₘ (Sₘ).patch.L))≤_
    rw [P.guide.laws.data.funds.length_eq]
    exact time
  let e:Bond (R.family.side (m+1) per):=Classical.arbitrary _
  exact (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans ((each e).trans bound))).mpr
    (fun k=> (each k).trans bound)

end YM.Integration.WilsonRootedHeldAffineStation
