import YM.Integration.WilsonPositionScaleLawBooked
import YM.Integration.WilsonPositionScaleLawSingleGrade

/-! The two original booked cutoff homes select all-order scale comparisons and
the highest-grade fixed-field law. The measured real kinetic reading is bought
on the same underlying extraction and regulator by its original cap book. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawBookedPhysical
open Function Filter Set Asymptotics Spec Table Extraction OPE OPE.Orbits Climb Trace.Pilot PhysMS
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Normalize MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival
open Lattice Wilson RG Source RG17 WilsonPositionThermometerCapStation
open WilsonPositionScaleLawWindow (RangeSpec)
open WilsonPositionScaleLawClock (radius)
open WilsonPositionScaleLawKinetic (kinetic)
open WilsonPositionScaleLawBooked (filed)
open scoped Topology Classical Asymptotics
variable {G:Gauge}(Z:WilsonPrescription G){hG:G.Simple}(M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)
    {R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)
    {ℓ:Ultrafilter (ℕ×ℕ)}{Y:(Bel R.family.book).Hierarchy}{arch:Trace.Terrace.Arch R.family}{D T B:ℕ}{δ:ℝ}
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→WilsonOriginalTwoFlatPublicBooks.Book F (l:=ℓ) Y arch D T s.val)
    (A:ℝ→Group R.family 6)
local notation "visits"=>trail.curry (ℓ:Filter (ℕ×ℕ))
local notation "therm"=>WilsonPositionRawCutoff.thermometer Z F J A
local notation "gcut"=>WilsonPositionThermometerSevenFaceRate.temperature (R:=R) hG (B:=B)

include H in
theorem original (bliss:Bliss F ℓ arch Y)(slow:WilsonWindowReportingPace.Slow R.kit)
    (δp:0<δ)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(k:Fin (D+1))(avoid:Finset E4)
    (hB:0<B)(book:WilsonPositionCapTransport.Book (f:=f) (l:=ℓ) (H:=Y) A J)
    (axis:ℝ×(ℕ×ℕ)→ℝ)(live:∀ᶠw in visits,0<axis w)
    (measured:Tendsto (fun w=>therm w.1 w.2/axis w) visits (𝓝 1))
    (dates:Tendsto (fun w=>axis w/gcut w.1 w.2) visits (𝓝 1)):
    ∃v:(Bel R.family.book).Field k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      (filed F J books k avoid v a→
        (∀c:ℝ,∀hc:0<c,∀q:ℕ,WilsonPositionScaleLawCompactAll.window Z M ν F J ⟨c,hc⟩ k.val q) ∧
        ∀r:ℝ,0<r→Tendsto (fun n:ℕ=>((n:ℝ)+1)*kinetic Z F J (radius r n)^2) atTop (𝓝 ((2*Trace.Over.b0 G*Real.log 2)⁻¹)) ∧
          (WilsonPositionScaleLawOneFee.Earned Z M ν F J k.val r→WilsonPositionScaleLawContinuum.Controlled Z F J k.val r)):=by
  obtain ⟨v,hv,a,ha,choose⟩:=WilsonPhysicalPositionBookedBranch.original F J books hG bliss slow δp below lead Z.store k avoid
  have funded:Coupling G (kinetic Z F J):=(WilsonMaxwellThermometerKineticRunning.original Z F J A hG slow hB bliss book lead axis live measured dates).2
  refine ⟨v,hv,a,ha,?_⟩
  intro vote
  constructor
  · intro c hc q
    letI :RangeSpec:=⟨c,hc⟩
    have raw:=WilsonPositionScaleLawBooked.raw J k.val (choose vote c hc)
    exact ⟨WilsonPositionScaleLawCompactJacobian.original F J Z.store lead k.val raw,
      WilsonPositionScaleLawCompactQinter.original Z M H ν F J lead paid k.val q raw,
      WilsonPositionScaleLawCompactQinter.qinter Z M H ν F J lead paid k.val q raw⟩
  · intro r hr
    letI :RangeSpec:=⟨1/2,by norm_num⟩
    have selected:WilsonPositionScaleLawBranch.Raw J k.val:=WilsonPositionScaleLawBooked.raw J k.val (choose vote (1/2) (by norm_num))
    exact ⟨WilsonPositionScaleLawClock.rate funded r hr,fun ear=>WilsonPositionScaleLawSingleGrade.original Z M H ν F J lead paid k.val selected r hr ear funded⟩

end YM.Integration.WilsonPositionScaleLawBookedPhysical
end
