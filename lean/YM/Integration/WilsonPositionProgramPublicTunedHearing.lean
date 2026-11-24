import YM.Integration.WilsonPositionProgramPublicDirectoryHearing
import YM.Integration.WilsonPositionBareSimultaneous

/-! The measured real thermometer, its ordered finite readings, and one
Handoff chosen before both physical regulators for the whole oriented
finite field panel. The four signed readings all use that very directory. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicTunedHearing
open Filter Function Extraction Table Spec PhysMS Lattice Source Labels Maxwell MS MS.Menus
open Wilson RG PhysicalNext.Repeat.Legato RG17 Trace.Pilot Climb OPE OPE.Orbits
open XSpace XSpace.Normalize XSpace.Cirrus Table.Pairing Local.Physical
open WilsonThermometerUnitFilingFourSquare WilsonPositionProgramPublicContrast
open WilsonPositionProgramPublicFourPrice WilsonPositionProgramPublicWide
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open Pert.Asymptotics FVA2 FVA2.Scale MS.Fleet FVA2.Register MS.Land
open WilsonPositionSeparatedProfileMatching WilsonPositionThermometerRunning
open scoped Topology BigOperators Classical
variable {G:Gauge} {B:Deck G} {h:ℕ} {K:Type} [Fintype K] (leg:K→Glyph B h)
    {I:Type} [Fintype I] {R:Run G} {S:Table R.family.book} {f:Extraction.Order}
    {l:Ultrafilter (ℕ×ℕ)} {Y:(Bel R.family.book).Hierarchy} {d:ℕ} (F:Final R.family f S)
    {x:I→S.Field d}(arm:(i:I)→Bool→Arm R.family S (l:Filter _) d (x i))(axis:Axis)
    (J:ℝ→PhysMS.tower S)(Z:WilsonPrescription G){g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{σ:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g M σ dial) {B₀:ℕ}(hB:0<B₀)
    (pace:WilsonWindowReportingPace.Slow R.kit)(fine index:ℝ→ℕ)
    (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=g) (B:=B₀) Z fine index)
    (A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "Λ" => WilsonPositionAuxiliaryReporterCalendar.scale R g (B:=B₀)
local notation "parameter" => WilsonPositionBareSimultaneous.parameter Z index θ
local notation "degree" => WilsonPositionBareSimultaneous.degree Z index θ
local notation "thermal" => WilsonPositionRawCutoff.thermometer Z F J A

def source (r:ℝ)(moving:Bool)(z:ℕ×ℕ):ℝ:=if moving then thermal r z else θ r

include H hB pace schedule in
theorem original (each:Injective leg)(order:(l:Filter _)≤f.fuse)(lead:Leading F J)
    (cap:WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)(coordinate:Coupling G θ)
    (q:ℕ)(ε:ℝ)(hε:0<ε):
    ∃(b:Bulb (center axis) axis)(k:ℝ),0<k ∧
      ∀ᶠ r in trail, ∃P:Handoff.Directory Z (index r) (Handoff.Directory.budget G 2 h+q),
      ∀ moving:Bool,let read:=source F J Z A r moving
                     let bare:=fun z=>parameter r (read z)
                     (∀ᶠ z in (l:Filter _),|bare z|≤8*θ r ∧
                       WilsonPositionRawMesh.forward Z (Z.run.step (index r)) (degree r) (bare z)=read z ∧
                       |WilsonPositionRawMesh.forward Z (Z.run.step (index r)) q (bare z)-read z|≤ε*|θ r|^q) ∧
                     ∀c∈(Z.run.step (index r)).Box,∀(t:ℝ)(ht:0<t),r≤t →
                      ∀(w:ℕ×ℕ→I→ℂ)(u:ℕ×ℕ→Bool→K→ℂ)(A' e:ℝ),
                      (∀ᶠ z in (l:Filter _),charge (w z)≤A') →
                      (∀ᶠ z in (l:Filter _),∀a v,‖assay (weighted leg (r/t) (u z a))
                        (weighted leg (r/t) (u z v))
                        (WilsonPositionProgramPublicDirectoryBoard.table Z axis b q leg P (bare z) c)-
                        WilsonPositionProgramPublicWideHearing.paid F arm axis b ht (w z) z a v‖≤e) →
                      ∀η:ℝ,0<η → ∀ᶠ z in (l:Filter _),k*((r/t)^h*‖u z false-u z true‖)^2≤4*e+η := by
  obtain ⟨b,k,hk,table⟩:=WilsonPositionProgramPublicDirectoryHearing.original leg F arm axis Z H each order q
  have actual:=WilsonPositionRawCutoff.measured Z F J lead A cap g order
  have tickets:=WilsonPositionBareSimultaneous.priced Z index θ g hB pace coordinate H schedule q ε hε
  have fixed:=WilsonPositionProgramInversionBill.interval R g hB pace θ coordinate Z H q (show 0<(1:ℝ) by norm_num)
  have lr:=Real.log_pos (show 1<(Z.run.ratio:ℝ) by
    exact_mod_cast (show 1<Z.run.ratio from (by decide:1<3).trans_le Z.run.large))
  have clock:=(WilsonPositionAuxiliaryReporterCalendar.measured R g hB pace θ coordinate).eventually_lt_const
    (show (2:ℝ)<3 by norm_num)
  have grows:Tendsto Λ trail atTop := tendsto_atTop_add_const_left _ _
    ((WilsonAdmissionScale.logarithm_tendsto R.family.path.levels g).comp
      (WilsonMeasuredWindow.stop_tendsto R.family.path.levels g B₀ hB))
  refine ⟨b,k,hk,?_⟩
  filter_upwards [table trail θ coordinate.positive (coordinate.conforms g) 2 (48/Real.log Z.run.ratio),
    tickets,actual,schedule,fixed,clock,grows.eventually_ge_atTop 6,coordinate.positive,RG17.positiveLength] with
    r tab price observed scheduled invoice one far positive hr
  obtain ⟨_,lo,hi,_⟩:=scheduled
  have floor:=(invoice (index r) lo hi).1
  have hi':(index r:ℝ)≤48/Real.log Z.run.ratio*(-Real.log (θ r))^2:=by
    have power:(Λ r)^((3:ℝ)/2)≤(Λ r)^2:=by
      rw [←Real.rpow_natCast];exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have head:Λ r≤4*(-Real.log (θ r)):=by linarith
    have rect:(Λ r)^2 ≤ (4*(-Real.log (θ r)))^2:=by gcongr
    have size:(index r:ℝ)≤48*(-Real.log (θ r))^2 /Real.log Z.run.ratio:=
      (le_div_iff₀ lr).mpr (by nlinarith only [hi,power,rect,mul_nonneg (by linarith : 0≤Λ r-1) (by linarith : 0≤Λ r)])
    exact size.trans_eq (by ring)
  obtain ⟨P⟩:=H.packets (index r) (Handoff.Directory.budget G 2 h+q)
  refine ⟨P,?_⟩
  intro moving
  dsimp only
  have heard:∀ᶠ z in (l:Filter _),|source F J Z A r moving z|≤2*θ r:=by
    cases moving
    · filter_upwards [] with z
      change |θ r|≤2*θ r
      rw [abs_of_pos positive];linarith
    · have bound:=observed.abs.eventually_lt_const (show |θ r|<2*θ r by rw [abs_of_pos positive];linarith)
      exact bound.mono fun z hz=>hz.le
  have paid:=heard.mono fun z hz=>price (source F J Z A r moving z) hz
  refine ⟨paid,?_⟩
  intro c hc t ht hrt w u A' e weights four η hη
  exact tab (index r) floor hi' P (le_refl _) c hc t r ht hr hrt w u
    (fun z=>parameter r (source F J Z A r moving z)) A' e weights (paid.mono fun z h=>h.1)
    four η hη
end YM.Integration.WilsonPositionProgramPublicTunedHearing
