import YM.Integration.WilsonPhysicalExteriorFirstCutPrice
import YM.Integration.WilsonPhysicalExteriorRunningRows

/-! On the very same funded positive run, the prescribed independent MS
datum purchases the exact physical Foundations section in every marked
column. The same register buys the finite errors on both periods and the
full three-clock reexpression, before all positions, fields and cutoffs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalExteriorFundedRows
open Lattice RG PhysicalNext.Repeat.Legato MS MS.Land MS.Menus MS.Rake MS.Tide
open FVA2 Register Precision RegulatorIR RegulatorIR.FVAAlt2 RegulatorIR.FVAAlt2.Lodge
open FVAAlt2 Lobby WilsonPhysicalExteriorRegisteredRows WilsonPhysicalExteriorRunningRows
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G)
local notation "B₀" => Press.portDeck G
local notation "M₀" => MS_Data G (Position.OpenAxis.Plot B₀)
local notation "Y₀" => Oracle.books R.family.path.levels.clock.kernel

theorem section_eq (d:ℕ) : (basisR R).use d = Next.Foundations.localSection G d := rfl
theorem actual_book (B:MS.Local.Physical.Deck G) : Lobby.Table (basisR R) B =
    Shop.richBook B R.family.labels R.family.params (Next.Foundations.localSection G)
      R.makes.sections (fun d=>Next.Foundations.valuation G d) := rfl

def Repriced (Q:Prescription B₀) : Prop :=
  ∀ (n N per:ℕ) (p:Fin n→Label B₀) (v eps:Fin n→ℝ) (y z e:ℝ)
    (x:Fin n→Site (R.family.side N per)),(∀i,eps i≠0) → e≠0 →
    WilsonPhysicalExteriorSlotReference.report R.metals.O (basisR R) Q p z v eps x =
      PowerSeries.C (WilsonPhysicalExteriorSlotReference.engineering eps p) *
      ∑ a:Array B₀ (fun i=>(p i).h),
        (∏ i:Fin n,coordinates Q (p i).h (v i) y z (Land.read (p i).item) (a i))*
        (PowerSeries.C ((e:ℂ)^wt (fun i=>owner (a i))) *
          reprice Q.team y z (newEra R.metals.O (basisR R) Q y (fun i=>owner (a i)) x e))

def Returned (M:M₀) (S:Prescription B₀) : Prop :=
  ∃ (Z:∀ b:Patch,b.Branches R.family.path.levels.clock.kernel G)
    (ledger:Lodge.Contract R Y₀ Z) (Q:Prescription B₀),
    Q.team=S.team ∧
    TaylorOKPl M (Shop.richBook B₀ R.family.labels R.family.params (Next.Foundations.localSection G)
      R.makes.sections (fun d=>Next.Foundations.valuation G d)) Q ∧
    WilsonPhysicalExteriorFundedPeriod.Periods R Z ledger Q ∧
    WilsonPhysicalExteriorFirstCutPrice.Rows R M Q ∧ Repriced R Q

theorem on_run {hG:G.Simple} (N:WilsonPrescription G) {M:M₀} {S:Prescription B₀}
    {dial:Bool} (hS:Main.Match N hG M S dial) (hR:NativeFVAPlateau.Correlations R) :
    Returned R M S := by
  obtain ⟨Z,L,Q,team,taylor,periods,rows⟩:=WilsonPhysicalExteriorFirstCutPrice.funded R N hS hR
  refine ⟨Z,L,Q,team,taylor,periods,rows,?_⟩
  intro n N per p v eps y z e x ok he
  exact WilsonPhysicalExteriorRunningRows.measured R.metals.O (basisR R) Q p v eps y z e x ok he

/-- No post-hoc Taylor or field-inverse hypothesis: purchase the two
genuine suppliers on the independently announced D and the selected R. -/
theorem funded (hG:G.Simple) (N:WilsonPrescription G) (M:M₀) (dial:Bool)
    (hR:NativeFVAPlateau.Correlations R) :
    ∃ S:Prescription B₀,Main.Match N hG M S dial ∧ Returned R M S := by
  obtain ⟨S,hs⟩:=Main.wilson_to_MS N hG M dial
  exact ⟨S,hs,on_run R N hs hR⟩

end YM.Integration.WilsonPhysicalExteriorFundedRows
end
