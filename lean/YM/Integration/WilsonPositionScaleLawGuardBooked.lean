import YM.Integration.WilsonPositionScaleLawGuardLittle
import YM.Integration.WilsonPositionScaleLawGuardNest
import YM.Integration.WilsonPositionScaleLawBookedFirst

/-! One original two-book reading prices all smaller homogeneous scales with exactly the same kinetic thermometer. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardBooked
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

local instance half:RangeSpec:=⟨1/2,by norm_num⟩
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawGuardLittle (scale)

def fieldPaid (d q:ℕ):Prop:=(WilsonPositionScaleLawQinter.measured Z M ν F J d q)=o[sweep] (fun z=>kinetic Z F J z.1^q)

include H in
theorem original (bliss:Bliss F ℓ arch Y)(slow:WilsonWindowReportingPace.Slow R.kit)
    (δp:0<δ)(below:(ℓ:Filter (ℕ×ℕ))≤f.fuse)(lead:Leading F J)
    (paid:∀d,∀ᶠr in trail,Frame.obedient F Y (J r) d)(k:Fin (D+1))(six:6≤k.val)(avoid:Finset E4)
    (hB:0<B)(book:WilsonPositionCapTransport.Book (f:=f) (l:=ℓ) (H:=Y) A J)
    (axis:ℝ×(ℕ×ℕ)→ℝ)(live:∀ᶠw in visits,0<axis w)
    (measured:Tendsto (fun w=>therm w.1 w.2/axis w) visits (𝓝 1))
    (dates:Tendsto (fun w=>axis w/gcut w.1 w.2) visits (𝓝 1)):
    ∃v:(Bel R.family.book).Field k.val,WilsonPhysicalPositionAdmissible.real R.family k.val v=v ∧ ∃a:ℝ,0<a ∧
      (filed F J books k avoid v a→
        (∀d≤k.val,∀q:ℕ,fieldPaid Z M ν F J d q→WilsonPositionScaleLawThermometerScale.Earned Z M ν F J q→scale F J Z M ν d q) ∧
        (∀d≤k.val,fieldPaid Z M ν F J d 1→scale F J Z M ν d 1) ∧
        ∀r:ℝ,0<r→Tendsto (fun n:ℕ=>((n:ℝ)+1)*kinetic Z F J (radius r n)^2) atTop (𝓝 ((2*Trace.Over.b0 G*Real.log 2)⁻¹))):=by
  obtain ⟨v,hv,a,ha,choose⟩:=WilsonPhysicalPositionBookedBranch.original F J books hG bliss slow δp below lead Z.store k avoid
  have funded:Coupling G (kinetic Z F J):=(WilsonMaxwellThermometerKineticRunning.original Z F J A hG slow hB bliss book lead axis live measured dates).2
  refine ⟨v,hv,a,ha,?_⟩
  intro vote
  have branch:WilsonPositionScaleLawCompactBranch.Raw J k.val:=WilsonPositionScaleLawBooked.raw J k.val (choose vote (1/2) (by norm_num))
  have small (d:ℕ)(hd:d≤k.val):WilsonPositionScaleLawCompactBranch.Raw J d:=WilsonPositionScaleLawGuardNest.original F J lead hd branch
  refine ⟨fun d hd q field clock=>WilsonPositionScaleLawGuardLittle.original F J Z M H ν lead paid funded d q (small d hd) (small 6 six) field clock,?_,
    fun r hr=>WilsonPositionScaleLawClock.rate funded r hr⟩
  intro d hd field
  apply WilsonPositionScaleLawGuardLittle.measured F J Z M H ν lead paid funded d 1
  · exact WilsonPositionScaleLawQinter.qinter Z M H ν F J lead paid d 1 (small d hd) field
  · have speed:(fun z:ℝ×Ratio=>kinetic Z F J (z.2.val*z.1)-kinetic Z F J z.1)=o[sweep] (fun z:ℝ×Ratio=>kinetic Z F J z.1):=
      WilsonPositionScaleLawKineticRatio.first (W:=half) hG funded
    simpa only [WilsonPositionScaleLawBookedFirst.printed Z M H ν F J,Complex.ofReal_re,pow_one] using speed

end YM.Integration.WilsonPositionScaleLawGuardBooked
end
