import YM.Integration.WilsonPositionScaleLawGuardBookedFinal

set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawTraceTerminal
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open Lattice Wilson RG Source RG17 WilsonPositionThermometerCapStation
open WilsonPositionScaleLawWindow (RangeSpec)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawBooked (filed)
open scoped Topology Classical Asymptotics
open WilsonPositionScaleLawGuardBooked (fieldPaid)
open WilsonPositionScaleLawGuardBookedFinal (finite full)
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family f S)(J:ℝ→tower S)(simple:G.Simple)
    {ℓ:Ultrafilter (ℕ×ℕ)}(Y:(Bel R.family.book).Hierarchy){arch:Trace.Terrace.Arch R.family}
local instance half : RangeSpec := ⟨1/2,by norm_num⟩
def Booked : Prop :=
  ∀(Z:WilsonPrescription G)(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}, Main.Match Z simple M σ b →
  ∀(ν:ℝ){D T B:ℕ}{δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) Y arch D T s.val)
    (A:ℝ→Group R.family 6), 0<δ → ∀(k:Fin (D+1)), 6≤k.val → ∀(avoid:Finset E4), 0<B →
    WilsonPositionCapTransport.Book (f:=f) (l:=ℓ) (H:=Y) A J → ∀(axis:ℝ×(ℕ×ℕ)→ℝ),
    (∀ᶠw in trail.curry (ℓ:Filter (ℕ×ℕ)),0<axis w) →
    Tendsto (fun w=>WilsonPositionRawCutoff.thermometer Z F J A w.1 w.2/axis w) (trail.curry (ℓ:Filter (ℕ×ℕ))) (𝓝 1) →
    Tendsto (fun w=>axis w/WilsonPositionThermometerSevenFaceRate.temperature (R:=R) simple (B:=B) w.1 w.2)
      (trail.curry (ℓ:Filter (ℕ×ℕ))) (𝓝 1) →
    ∃v:(Bel R.family.book).Field k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      (filed F J books k avoid v a→∀d≤k.val,
        (fieldPaid Z M ν F J d 2→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J 2→finite Z M ν F J d) ∧
        ((∀q,2≤q→fieldPaid Z M ν F J d q)→(∀q,2≤q→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J q)→full Z M ν F J d))

theorem original (bliss:Bliss F ℓ arch Y)(slow:WilsonWindowReportingPace.Slow R.kit)
    (below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)(paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d):
    Booked F J simple (ℓ:=ℓ) Y (arch:=arch) := by
  intro Z M σ b matchData ν D T B δ books A δp k six avoid hB book axis live measured dates
  exact WilsonPositionScaleLawGuardBookedFinal.original Z M matchData ν F J books A bliss slow δp below lead paid k six avoid hB book axis live measured dates

end YM.Integration.WilsonPositionScaleLawTraceTerminal
end
