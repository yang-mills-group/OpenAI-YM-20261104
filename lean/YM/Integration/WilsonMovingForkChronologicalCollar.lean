import YM.Integration.WilsonMovingForkChronologicalSale

/-! The real two-stop optical interval has one date-count cost. Each edge
is heard on the original nominated stop, including when the captured
programme switches ears between its fine and coarse parts. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkChronologicalCollar
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity QuadraticLocal.Sunrise Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonMovingForkChronologicalTable (density)
open WilsonMovingForkPrintedFile (Program allSlots)
open WilsonMovingForkChronologicalSale (Mounted)
open WilsonThermometerUnitFilingFlatTelescope (feeAt)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){m k:ℕ}(hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin){φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)
  (ahead:Mentor.Forecast D R.rolls Q φ books)

theorem original (cost n:ℕ):∃start:ℕ,∀{N per b L:ℕ},start ≤ b → b+L ≤ N → R.family.S.a b/R.family.S.a (b+L) ≤ (R.family.path.levels.clock.hatBeta b)^cost → ∀(d:Fin n → ℕ)(prog:Program R d (b+L))(w:∀a,R.family.label (d a))
      (pins:Fin n → Site (R.family.side (b+L) per))(Ψ:∀i,Rep G (R.family.side i per))
      (u p size:ℕ)(η:ℝ),0 ≤ η → ∀(days:Finset ℕ), (∀j∈days,b ≤ j+1) → (∀j∈days,j+1 < b+L) → (∀j∈days,Mounted prog N per w pins (j+1) ∧ Mounted prog N per w pins (j+2)) → (∀j∈days,WilsonReceivedChronologicalDualInterval.Owned (N:=N) R simple hk D Q π Γ Ψ books ahead
        (density prog N per w pins) j u b (allSlots n) (p+1) size η) → ∀(stop:ℕ → ℕ),(∀j∈days,u ≤ stop j ∧ stop j ≤ b) → let s:=allSlots n
      ∑j∈days,‖feeAt R N per (stop j) (WilsonMovingForkPrintedFile.row prog N per w pins) (j+1)‖ ≤ (4*(cost:ℝ)/Real.log 3)*
        (WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*(2:ℝ)^(p+1)*WilsonOriginalCensusFiledHousing.fare s size)*
        (regulatorRun R.family N per b)^p:=by
  obtain ⟨start,run⟩:=WilsonReceivedChronologicalDualInterval.original (V:=Fin n) R simple hk D Q π Γ books ahead cost
  refine ⟨start,?_⟩
  intro N per b L base kn aperture d prog w pins Ψ u p size η pos days lo hi mounted sales stop bounded s
  refine le_trans (le_of_eq (Finset.sum_congr rfl (fun j hj=>?_)))
    (run base kn aperture Ψ (density prog N per w pins) s u p size η pos days lo hi sales stop bounded)
  apply congrArg norm
  have old: j+1 ≤ b+L:=(hi j hj).le
  have younger: j+2 ≤ b+L:=hi j hj
  exact WilsonMovingForkChronologicalTable.dated prog N per w pins ((bounded j hj).2.trans (lo j hj))
    (lt_of_lt_of_le (hi j hj) kn)
    (WilsonMovingForkChronologicalSale.integrable prog N per w pins old kn (mounted j hj).1)
    (WilsonMovingForkChronologicalSale.integrable prog N per w pins younger kn (mounted j hj).2)

end YM.Integration.WilsonMovingForkChronologicalCollar
