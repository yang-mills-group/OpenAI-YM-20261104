import YM.Integration.WilsonPositionScaleLawBooked
import YM.Integration.WilsonPositionScaleLawThermometerScale

/-! The pre-elected original two-book report selects the scalar branch. All seven amplitude errors are measured on the same near physical home. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawBookedThermometer
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open WilsonPositionScaleLawWindow (RangeSpec Ratio sweep)
open WilsonPhysicalPositionBookedBranch (home Admitted station)
open WilsonPositionScaleLawThermometerPay (Fits target)
open WilsonPositionScaleLawThermometerScale (Earned)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPhysicalPositionDirectedPins (cutoff)
open WilsonPhysicalPositionDirectedTest (baseline)
open scoped Topology Classical Asymptotics
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)

variable (Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {ℓ:Ultrafilter (ℕ×ℕ)}{Y:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T:ℕ}{δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) Y arch D T s.val)

def window (W:RangeSpec)(q:ℕ):Prop:=
  letI := W
  (∃L T:ℝ,0≤L ∧ 0≤T ∧ ∀ᶠ z in sweep,∀e:ℝ,0≤e→e≤1→Fits Z M ν F J q z e→
    |kinetic Z F J (z.2.val*z.1)-(target Z M ν F J q z).re|≤L*e+T*|kinetic Z F J z.1|^(q+1)) ∧
  (Earned Z M ν F J q →
    (fun z:ℝ×Ratio=>kinetic Z F J (z.2.val*z.1)-(target Z M ν F J q z).re)=o[sweep] (fun z=>kinetic Z F J z.1^q)) ∧
  (∀z:ℝ×Ratio,starRingEnd ℂ (target Z M ν F J q z)=target Z M ν F J q z)

include H in
theorem original (bliss:Bliss F ℓ arch Y)(slow:WilsonWindowReportingPace.Slow R.kit)
    (δp:0<δ)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(k:Fin (D+1))(six:k.val=6)(avoid:Finset E4):
    ∃v:(Bel R.family.book).Field k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      (WilsonPositionScaleLawBooked.filed F J books k avoid v a→∀c:ℝ,∀hc:0<c,∀q:ℕ,window F J Z M ν ⟨c,hc⟩ q):=by
  obtain ⟨v,hv,a,ha,choose⟩:=WilsonPhysicalPositionBookedBranch.original F J books hG bliss slow δp below lead Z.store k avoid
  refine ⟨v,hv,a,ha,?_⟩
  intro vote c hc q
  letI :RangeSpec:=⟨c,hc⟩
  have selected:=choose vote c hc
  rw [six] at selected
  have paidRaw:=WilsonPositionScaleLawBooked.raw J 6 selected
  exact ⟨WilsonPositionScaleLawThermometerPay.original Z M H ν F J lead paid q paidRaw,
    WilsonPositionScaleLawThermometerScale.qinterg Z M H ν F J lead paid q paidRaw,
    WilsonPositionScaleLawThermometerScale.real Z M H ν F J q⟩

end YM.Integration.WilsonPositionScaleLawBookedThermometer
end
