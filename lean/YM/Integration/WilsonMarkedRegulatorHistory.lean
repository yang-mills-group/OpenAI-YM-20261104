import YM.Integration.WilsonMarkedRegulatorProgram
import YM.Integration.WilsonPointChildLocatedDeposit

/-! The regulator Ward tests of the full original independent marked history.
A complete ordinary deposited word and its connected component have separate receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMarkedRegulatorHistory
open Function Finset Lattice RG Wilson Laurent Precision Next.Foundations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Winding
open FormalBulk08 Sierra Pose Stationary RegulatorIR.Binding RegulatorIR.Ward PowerSeries
open WilsonMarkedRegulatorProgram (table copied)
open WilsonPointChildCenteredPortfolio (bank)
open WilsonPointChildNamedResponse (output)
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{ι:Type}[Fintype ι][DecidableEq ι]{h k:ι→ℕ}

/-- Both signed programs use the same orbit and polarization. -/
def Warps (a:ℕ)(P:Era G ℝ):Prop:=∀(n:Side)(x y:ℝ→ Horizon G n),
    ContDiffAt ℝ ω x 0 → ContDiffAt ℝ ω y 0 → reel_prop x y → ∀e:ℕ,
    coeff e (RegulatorIR.Ward.reel (table (P.1 n)) a y)=coeff e (RegulatorIR.Ward.reel (table (P.1 n)) a x) ∧
    coeff e (RegulatorIR.Ward.reel (table (copied P.2 n)) a y)=coeff e (RegulatorIR.Ward.reel (table (copied P.2 n)) a x)

omit [Fintype ι] in
/-- The actual prior at N and original receiving reset supply every older date,
including a nonbare planting at b. -/
theorem original (R:Run G)(simple:G.Simple)(o:Loc G 1)(K:ι→ℕ)(seed:Outerm G h)(income:Wellness k seed)
    (N b j:ℕ)(born:b≤N)(age:j≤b)(y:ι→ Cover)(S:Finset ι)(f:Pen h S→L[ℝ]ℝ):
    let H:=Gears R.family.path.levels R.metals.O K k N b j seed y
    Warps (mass k S) (tuftV f (H S)) ∧ Warps (mass k S) (tuftV f (levelsO H S)):=by
  intro H
  have wages:Eu k H:=(Cog R.family.path.levels R.metals.O born seed income simple R.alloy.B.ratio age).level' y
  exact ⟨fun _=>WilsonMarkedRegulatorProgram.original (wages S) o f,
    fun _=>WilsonMarkedRegulatorProgram.original (placedO H wages S) o f⟩

omit [Fintype ι] in
/-- Two genuine original filings can be submitted as the complete intake on
the same original N for every later age and every subset, including the
connected and ordinary ABC with its AB times C. -/
theorem deposited (R:Run G)(simple:G.Simple)(o:Loc G 1)(u:ι→G.ColorIndex)(depth:∀s,k s<h s)
    (m N j:ℕ)(live:m+1 < N)(age:j ≤ m)(K:ι→ℕ)(d₁ d₂:ι→∀i,Site (R.family.S.block i))
    (v₁ v₂:∀s,Letter (R.family.labels.level (k s)))(T:Finset ι)
    (z:ι→Site (ll R.family.path.levels m).L)(z':ι→Site (ll R.family.path.levels (m+1)).L)
    (y:ι→ Cover)(S:Finset ι)(f:Pen h S→L[ℝ]ℝ):
    let A:=R.family.path.levels
    let old:=bank R u depth d₁ N (m+2) v₁
    let fresh:=bank R u depth d₂ N (m+1) v₂
    let seed:=fun a=>output A R.metals.O m N k T old fresh a z z'
    let H:=Gears A R.metals.O K k N m j seed y
    Warps (mass k S) (tuftV f (H S)) ∧ Warps (mass k S) (tuftV f (levelsO H S)):=by
  intro A old fresh seed H
  have before:=WilsonPointChildLocatedDeposit.located R simple u depth o d₁ N (m+2) (by omega) v₁
  have birth:=WilsonPointChildLocatedDeposit.located R simple u depth o d₂ N (m+1) (by omega) v₂
  have purchased:=WilsonPointChildLocatedDeposit.returned R simple m N live T old fresh before birth z z'
  exact original R simple o K seed purchased N m j (by omega) age y S f

end YM.Integration.WilsonMarkedRegulatorHistory
end
