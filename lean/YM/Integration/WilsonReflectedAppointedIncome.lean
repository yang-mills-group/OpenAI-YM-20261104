import YM.Integration.WilsonReflectedFullPanel
/-! Completion of a previously assigned guarded reporter on its own
upper matrix and complete measured coordinates. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedAppointedIncome
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Extra.Histories.Relay
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open RG05Readout RG05Readout.Address RG05Readout.Records WilsonOriginalNullCorridor MergeProof MergeProof.Accent
open WilsonOriginalMicroscopicGuardedPage WilsonOriginalMicroscopicGuardedReporters WilsonReflectedFullPanel
open scoped Classical
variable {G:Gauge}(R:Run G)
local notation "C₀" => R.family

theorem original (simple:G.Simple)(d:ℕ):∀ᶠ j:ℕ in atTop,∀K N p q (lo:j≤K)(hi:K≤N)(η:ℝ)
    (A:(C₀).label d≃ₗ[ℂ](C₀).label d)(Y:(C₀).label d)(bank:ℝ),
    Arrived R d j K N p q lo hi η A (full R d N p j Y) →
    ((C₀).labels.level d).coeffSize (A.symm (full R d N p j Y))≤
     WilsonOriginalMicroscopicGuardedReporters.stretch R η j K*((1+wrapCost R d j)*bank) →
    receipt R d j K N p q lo hi η A Y bank:=by
  filter_upwards [WilsonAddressedRestartedFiled.original R d simple] with j file
  intro K N p q lo high η A Y bank issued paid
  refine ⟨issued,paid,?_⟩
  let y:=((C₀).factory d N p).terminal.symm Y
  have same:full R d N p j Y=page (C:=C₀) d p j (((C₀).factory d N p).entries j y):=
    page_at R d (lo.trans high) Y
  rw [same] at issued
  intro f early late o
  have made:=file N p K lo high q η A y issued f early late o
  rwa [←same] at made

end YM.Integration.WilsonReflectedAppointedIncome
end
