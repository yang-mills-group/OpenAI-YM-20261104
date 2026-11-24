import YM.Integration.WilsonVacuumPreResetFiniteHistory
import YM.WilsonCoeffUV.Reclosure.PacketWard

/-! The finite, centered Wilson action retains its nonlinear gauge identity on the
original torus at every age, after the cover kinetic coin has been applied. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
noncomputable section

namespace YM.Integration.WilsonVacuumPreResetFiniteWard

open Function Matrix Filter Lattice Laurent Wilson RG Precision Tree Bloch Exterior
open Comparison.RG02 FreeResolvent WilsonCoeffUV Push.Uniform
open FormalBulk08 FormalBulk08.Flat FormalBulk08.Reef FormalBulk08.Orb FormalBulk08.Series FormalBulk08.Jets FormalBulk08.Shore FormalBulk08.Lava FormalBulk08.Wine
open FormalBulk08.Gorge FormalBulk08.Lotus FormalBulk08.Mesa
open Work.F03 Work.F05 Work.F08 PowerSeries Next.Free Stationary
open WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Blue
open WilsonCoeffUV.Mer WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding WilsonCoeffUV.Bank.Ticket
open Next.Foundations PhysicalNext.Repeat.Legato

open FormalBulk08 Flat Reef Jets Wick Gorge Lotus Mesa Orb WilsonCoeffUV WilsonCoeffUV.Bank
open Comparison.RG02 Push.Uniform Work.F03 Work.F05 Work.F08
open PhysicalNext.Repeat.Legato PowerSeries Filter WilsonCoeffUV.Power WilsonCoeffUV.Blue
open scoped Classical Topology ContDiff
open WilsonVacuumPreResetFiniteHistory WilsonVacuumPreResetFiniteIntegral

variable {G : Gauge} (R : Run G)
local notation "V" => R.family.path.levels

private theorem substitution {U I:Type} (y:U→Ink I):
    Blue.train y=Wick.roam ℝ y:=by
  apply Blue.serial_ext
  · rw [Blue.train_X,constantCoeff_X]
  · intro a;rw [Blue.train_C,Wick.roam,Series.change_C];rfl
  · rw [Blue.train_X,Wick.roam,Series.change_X]

private theorem angles {I U:Type} [Fintype I] [DecidableEq I] (f:Rays I→Rays U):
    Blue.spool f=Jets.motor f:=by
  funext i
  apply PowerSeries.ext;intro e
  simp only [Blue.spool,Jets.motor,Jets.afterX,coeff_mk,WilsonConditionalTaylorWheelBare.germ,Nat.add_comm 1 e]

theorem measured (simple : G.Simple) {N j : ℕ} (live : j ≤ N) (n : Side) :
    Reef.Civic (read R N j n) := by
  have paid := ((WilsonCoeffUV.Bank.old V R.metals.O simple R.alloy.B.ratio N j live).basis n).valid
  intro s x I hf a b k ha hb da db hk constant held
  classical
  have shift : TurnsG s x k a b :=
    ⟨da, db, ha, hb, hk, by simpa only [WilsonCoeffUV.Bank.Mosaic.mantle_input] using held⟩
  have ward := paid s x shift
  rw [substitution, substitution, angles, angles] at ward
  simpa only [WilsonVacuumPreResetFiniteIntegral.read, map_neg] using congrArg Neg.neg ward

theorem original (u : G.ColorIndex)
    (tags : ∀ j n, (primary (R.family.path.levels.clock.op j 0).patch R.family.path.levels.clock.kernel n).Choices)
    (simple : G.Simple) (v : ℕ → Gear G → ℝ) (rows : FundedMarkedCoverRows.prices v R.kit)
    {N j : ℕ} (live : j ≤ N) (n : Side) :
    let A := action R u tags N (N-j) j n
    coeff 0 A = Reef.crunch (Reef.kernelP G (V).clock.kernel.penalty (location V N j) n) ∧
      Reef.Civic A := by
  dsimp only
  rw [← WilsonVacuumPreResetFiniteHistory.original R u tags simple v rows live n]
  exact ⟨WilsonVacuumPreResetFiniteIntegral.head R simple live n, measured R simple live n⟩


end YM.Integration.WilsonVacuumPreResetFiniteWard
end
