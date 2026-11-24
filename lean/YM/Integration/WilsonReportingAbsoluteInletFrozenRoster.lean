import YM.Integration.WilsonReportingAbsoluteInletFundedRun
import YM.Integration.WilsonReportingAbsoluteInletForecastBookIncome

/-! Actual signed, fully engineered aperture receipt with its separately
filed finite bookH polynomial at the true regulator coupling. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingAbsoluteInletFrozenRoster
open Function Filter Finset Lattice RG Wilson RGComparison.Core16 RGComparison.Core16.Spool
open PhysicalNext.Repeat PhysicalNext.Repeat.Legato Pert.Asymptotics Next.Foundations Labels
open WilsonConditionalTaylorLabels WilsonOffsetJointRoster WilsonUniformUnmarkedInletEnergySites
open WilsonUniformUnmarkedInletBondRemainder WilsonUniformUnmarkedInletConnectedShift
open InletSusceptibility.Packet WilsonReportingAbsoluteInletNativeDates
open WilsonReportingAbsoluteInletNativeCoordinates WilsonReportingAbsoluteInletNativeInvoice
open scoped Classical BigOperators Topology
open WilsonReportingAbsoluteInletCaptured
variable {G:Gauge}

open FormalBulk08.Wine WilsonReportingAbsoluteInletForecastBooks
open WilsonReportingAbsoluteInletForecastReciprocal WilsonReportingAbsoluteInletForecastBookStep
open WilsonReportingAbsoluteInletFundedRun
def Receipt (R:Run G)(κ c:ℝ)(P q:ℕ)(b:Roster G)(D:ℕ→ℕ→ℕ→PowerSeries ℝ):Prop:=
  let n:=rank κ P q b+2
  let h:=fun N per j=>value n (bookH (D N per j)) (regulatorRun R.family N per j)
  ∀ {ε:ℝ},0<ε→
    ∀ᶠ k:ℕ in atTop,∀s:Finset (Fin b.length),s.Nonempty→∀u,ultraviolet R.family c k≤u →
      let t:=inlet R P u
      let N:=u+1
      ∃tu:t≤u,∀per,∀ T:Slices R.family.path.levels per,∀ (o:Fin b.length→Site (R.family.side N per)) i,i∈s→
        ∀ (z e:Site (R.family.side N per)) (part:Bool),
          let d:=traversal T (tu.trans u.le_succ)
          let x:=shifts R per t N
          let v:=finite R N per t (h N per)
          let δ:=x-v
          let g:=regulatorRun R.family N per N
          let β:=Descent.offset v g
          let φ:=WilsonReportFrozenTraversal.planted R b s o i z e part
          let A:=WilsonReportingAbsoluteInletGust.physical R (tu.trans u.le_succ) φ 1-d.conditioned β φ 1
          (∀r∈Set.Icc (0:ℝ) 1,(∑j∈interior d,|picture d β δ 1 φ r j|)≤cost κ P b s/g^loss κ P b s) ∧
          (∃r∈Set.Ioo (0:ℝ) 1,A=∑j∈interior d,δ (WilsonUniformUnmarkedInletEnergySites.lag d j)*picture d β δ 1 φ r j) ∧
          |A|/g^engineering b s≤ε*g^(q+1)


theorem purchased (R:Run G)(simple:G.Simple){κ c:ℝ}(fund:Reported R κ)(hc:1<c)
    (P q:ℕ)(b:Roster G)(D:ℕ→ℕ→ℕ→PowerSeries ℝ)
    (hats:∀i,R.family.path.levels.clock.hatBeta (i+1) ≤ 2*R.family.path.levels.clock.hatBeta i)
    (forward:Forward R (rank κ P q b+2)
      (fun N per j=>value (rank κ P q b+2) (bookU (D N per j)) (regulatorRun R.family N per j)))
    (tariff:Cost R (rank κ P q b+2) D):Receipt R κ c P q b D:=by
  have payment:=WilsonReportingAbsoluteInletForecastBookIncome.inverse R simple (rank κ P q b) D hats forward tariff
  dsimp only [Receipt]
  intro ε ep
  exact fund hc P q b _ payment ep
end YM.Integration.WilsonReportingAbsoluteInletFrozenRoster
