import YM.Integration.WilsonReceivedChronologicalInstallment

/-! At the flat date itself the true compulsory contribution vanishes on its own original gallery. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalCurrentFlat
open Function Finset Filter MeasureTheory Lattice Wilson RG Tree Marker QuadraticLocal Ac Source Labels
open QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonOriginalCensusAngularFace
open scoped BigOperators Classical

variable {G:Gauge} (R:Run G) (simple:G.Simple) {m j N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀i,RG.Rep G (R.family.side i per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ j)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "marks" => Stock.census V
local notation "actors" => WilsonOriginalMixedBlockRows.room V
local notation "nulls" => fun _:V => (⊥:Submodule ℝ ℂ)
variable {S S': V → ℝ}{a a':ℕ}
variable (rows:∀i:ℕ,Config G (R.family.side i per) → Marker.Poly (Stock.census V))
variable (upper:WilsonOriginalDatedCensusInput.Filed (i:=j+1) (N:=N) R hk D Q π Γ Ψ books (Nat.le_succ_of_le base) ahead S a (rows (j+1+1)))
  (lower:WilsonOriginalDatedCensusInput.Filed (i:=j) (N:=N) R hk D Q π Γ Ψ books base ahead S' a' (rows (j+1)))
local notation "high" => upper.post
local notation "low" => lower.post
local notation "vac" => Ψ (j+1)
open MergeProof.Accent Extra.Histories.Relay FVA1Physical.Round2.CP5
open WilsonOriginalOccupiedWindow

theorem at_current {T:Type}[Fintype T][DecidableEq T](J:Marker.Census T)
    {t N per:ℕ}(Ψ:∀ j,RG.Rep G (R.family.side j per))
    (row:Slice R J (Ψ t))(s:J.Mode)(U:Config G (R.family.side t per))
    (clean:flags (Ψ t).p.threshold U=∅):
    credit R J (N:=N) (le_refl t) Ψ row s U=0:=by
  unfold credit
  rw [gust_base,gust_base]
  rw [Gallery.density,gallery_gas_one row.A row.x U clean,mul_one,Rep.eval,
    (Ψ t).activities.gas_one (p:=(Ψ t).p) clean,mul_one]
  simp

theorem original (s:(marks).Mode)(p:ℕ)
    (sale:WilsonReceivedChronologicalInstallment.Sale R simple hk D Q π Γ Ψ books base ahead rows upper lower
      (le_refl (j+1)) s p (1:Config G (R.family.side (j+1) per))):
    ‖WilsonOriginalJointTrialHearing.fee R N per (1:Config G (R.family.side (j+1) per)) rows (j+1) s‖ ≤
      WilsonOriginalOrdinaryFaceOrder.constant s s.val.card*(regulatorRun R.family N per (j+1))^p:=by
  have paid:=WilsonReceivedChronologicalInstallment.paid R simple hk D Q π Γ Ψ books base ahead rows upper lower
    (le_refl (j+1)) s p 1 sale
  rw [at_current _ _ _ _ _ _ (UVNext.CouplingReset.flags_one (Ψ (j+1)).p),sub_zero] at paid
  exact paid

end YM.Integration.WilsonReceivedChronologicalCurrentFlat
end
