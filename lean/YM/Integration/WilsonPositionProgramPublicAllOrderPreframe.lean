import YM.Integration.WilsonPositionProgramPublicPreframe

/-! A physical preframe adopted once before the accuracy is used on the
common inversion at every finite order and both measured scalar choices. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicAllOrderPreframe
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot MergeProof.East PhysicalNext.Repeat.Legato
open RG17 FullVolume Climb Next.UVStress PhysMS Maxwell XSpace XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Scale MS MS.Fleet MS.Land FVA2.Register MS.Menus Local.Physical Table.Pairing
open WilsonMatrixTicketLanesSmearedPivot WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicBank
open WilsonPositionProgramPublicStations WilsonPositionProgramPublicGram WilsonPositionProgramPublicMeasuredAxes
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open WilsonPositionProgramPublicWide WilsonPositionProgramPublicTunedHearing
open WilsonPositionProgramPublicPositionNormalization WilsonPositionProgramPublicFourOperator
open WilsonPositionProgramPublicFittedInverse
open scoped Topology BigOperators Classical
variable {G:Gauge}{R:Run G}{S:Table R.family.book}{f:Extraction.Order}
    {l:Ultrafilter (ℕ×ℕ)}{Y:(Bel R.family.book).Hierarchy}{d D:ℕ}(F:Final R.family f S)
    (J:ℝ→tower S)(Z:WilsonPrescription G)(B:Deck G)(axis:Axis)
    (A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6)(index:ℝ→ℕ)
    (p:Profiles R d)(b:Bulb (center axis) axis)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "Γ" => Glyph B d
local notation "parameter" => WilsonPositionBareSimultaneous.parameter Z index θ
local notation "degree" => WilsonPositionBareSimultaneous.degree Z index θ

def Earned {C r:ℝ}{cap:d≤D}{s a:ℝ}{stock:Bank F l D s a}
    (frame:WilsonPositionProgramPublicPreframe.Frame F J Z B p (Y:=Y) C r cap stock)
    (k:ℝ)(q:ℕ){budget:ℕ}(P:Handoff.Directory Z (index r) budget):Prop:=
  BasisHearing F J Z B axis A index p b k frame.positive q P frame.pair.arm frame.decoder ∧
  ∀c∈(Z.run.step (index r)).Box,∀moving:Bool,∀(t:ℝ)(ht:0<t),r≤t→∀e:ℝ,
    (∀ᶠ z in (l:Filter _),∀i:Γ,comparison F J Z B axis A index p b frame.positive q P
       frame.pair.arm frame.decoder c moving ht e z i)→
    ∀η:ℝ,0<η→∀ᶠ z in (l:Filter _),
      k*((r/t)^d*‖(frame.change z).toLinearMap.toContinuousLinearMap-ContinuousLinearMap.id ℂ (Γ→ℂ)‖)^2≤
        (Fintype.card Γ:ℝ)^2*condition R B d^2*(4*e+η)

theorem received {C r:ℝ}{cap:d≤D}{s a:ℝ}{stock:Bank F l D s a}
    (frame:WilsonPositionProgramPublicPreframe.Frame F J Z B p (Y:=Y) C r cap stock)
    {k:ℝ}(hk:0<k)(q:ℕ){budget:ℕ}(P:Handoff.Directory Z (index r) budget)
    (order:(l:Filter _)≤f.fuse)
    (listen:BasisHearing F J Z B axis A index p b k frame.positive q P frame.pair.arm frame.decoder):
    Earned F J Z B axis A index p b frame k q P:=by
  obtain ⟨V,fits,rates⟩:=WilsonPositionProgramPublicFourOperator.original F J Z B axis A index p b
    frame.positive q P frame.pair.arm frame.decoder hk.le order frame.reads listen
  have same:∀ᶠ z in (l:Filter _),V z=frame.change z:=by
    filter_upwards [fits,frame.observed,frame.unique] with z fresh original inj
    ext1 x
    exact inj ((fresh.1 x).trans (original.1 x).symm)
  refine ⟨listen,?_⟩
  intro c hc moving t ht wide e fees η hη
  filter_upwards [same,rates c hc moving t ht wide e fees η hη] with z eq cost
  rwa [←eq]

variable {g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{σ:Prescription (Press.portDeck G)}
    {dial:Bool}(H:Main.Match Z g M σ dial){B₀:ℕ}(hB:0<B₀)(pace:WilsonWindowReportingPace.Slow R.kit)
    (fine:ℝ→ℕ)(schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=g) (B:=B₀) Z fine index)

include H hB pace schedule in
theorem original {arch:Arch R.family}(bliss:Bliss F l arch Y)(lead:Leading F J)
    (income:∀d,∀ᶠ r in trail,PhysMS.Frame.obedient F Y (J r) d)(cap:d≤D)
    (group:WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)(meter:Coupling G θ):
    ∃(T:ℕ)(p:Profiles R d)(C:ℝ)(b:Bulb (center axis) axis)(k:ℝ),0<C ∧ 0<k ∧
      (∀ᶠ r in trail,
        (let s:=WilsonThermometerUnitFilingFourPoolShell.radius arch T r
         ∃stock:Bank F l D s (dock s^T),Nonempty (WilsonPositionProgramPublicPreframe.Frame F J Z B p (Y:=Y) C r cap stock)) ∧
        ∀s w (stock:Bank F l D s w),Nonempty (WilsonPositionProgramPublicPreframe.Frame F J Z B p (Y:=Y) C r cap stock)) ∧
      ∀(q:ℕ)(ε:ℝ),0<ε→∀ᶠ r in trail,∃P:Handoff.Directory Z (index r) (Handoff.Directory.budget G 2 d+q),
        (∀moving:Bool,let read:=source F J Z A r moving
                       let bare:=fun z=>parameter r (read z)
                       ∀ᶠ z in (l:Filter _),|bare z|≤8*θ r ∧
                         WilsonPositionRawMesh.forward Z (Z.run.step (index r)) (degree r) (bare z)=read z ∧
                         |WilsonPositionRawMesh.forward Z (Z.run.step (index r)) q (bare z)-read z|≤ε*|θ r|^q) ∧
        ∀s w (stock:Bank F l D s w)(frame:WilsonPositionProgramPublicPreframe.Frame F J Z B p (Y:=Y) C r cap stock),
          Earned F J Z B axis A index p b frame k q P:=by
  obtain ⟨T,p,C,hC,stock⟩:=WilsonPositionProgramPublicPreframe.original F J Z B g bliss lead income cap
  obtain ⟨b,k,hk,rates⟩:=WilsonPositionProgramPublicEnrolledRates.original (id:Γ→Γ) F axis J Z H hB pace
    fine index schedule A Function.injective_id bliss.lies lead group meter
  refine ⟨T,p,C,b,k,hC,hk,stock,?_⟩
  intro q ε hε
  filter_upwards [rates q ε hε] with r available
  obtain ⟨P,paid⟩:=available
  refine ⟨P,fun moving=>(paid moving).mono fun z h=>⟨h.1,h.2.1,h.2.2.1⟩,?_⟩
  intro s w stage frame
  apply received F J Z B axis A index p b frame hk q P bliss.lies
  intro c hc moving t ht wide w A' e mass
  exact fun four η hη=>WilsonPositionProgramPublicEnrolledMatrix.oriented (id:Γ→Γ) F
    (fun i br=>frame.pair.arm br (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) i)) axis
    bliss.lies b hk ht frame.positive wide w (fun z branch=>coordinate B F J Z p frame.positive frame.pair.arm
    frame.decoder branch z (w z)) _ mass ((paid moving).mono fun z inc=>inc.2.2.2 c hc) four η hη

end YM.Integration.WilsonPositionProgramPublicAllOrderPreframe
