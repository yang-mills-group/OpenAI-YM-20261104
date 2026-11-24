import YM.Integration.WilsonPositionProgramPublicEnrolledRates

/-! One measured frame on the original Wilson hierarchy and one independently
issued inversion on all its own field indices. Each signed entry uses the
actual decoded measured coordinates and its two genuinely occupied roots. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicPositionNormalization
open Function Filter Lattice Wilson RG Source Extraction Table Spec OPE
open GapsContact GapsContact.Stamps GapsContact.Seams GapsContact.Ascent
open Trace Trace.Terrace Trace.Pilot MergeProof.East PhysicalNext.Repeat.Legato
open RG17 FullVolume Climb Next.UVStress PhysMS Maxwell XSpace XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Scale MS MS.Fleet MS.Land FVA2.Register MS.Menus Local.Physical Table.Pairing
open WilsonPositionHomogeneousFrame WilsonMatrixTicketLanesSmearedPivot
open WilsonThermometerUnitFilingFourSquare WilsonMeasuredPublicBank
open WilsonPositionProgramPublicStations WilsonPositionProgramPublicGram
open WilsonPositionProgramPublicOriented WilsonPositionProgramPublicContrast
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicReflectedRead
open WilsonPositionProgramPublicWide WilsonPositionProgramPublicMeasuredAxes
open WilsonPositionProgramPublicTunedHearing
open scoped Topology BigOperators Classical

variable {G:Gauge} {R:Run G} {S:Table R.family.book} {f:Extraction.Order}
    {l:Ultrafilter (ℕ×ℕ)} {Y:(Bel R.family.book).Hierarchy} {d D:ℕ} (F:Final R.family f S)
    (J:ℝ→tower S)(Z:WilsonPrescription G)(B:Deck G)(axis:Axis)
    (A:ℝ→WilsonPositionThermometerCapStation.Group R.family 6)(index:ℝ→ℕ)
    (p:Profiles R d)(b:Bulb (center axis) axis)(k C:ℝ)
local notation "θ" => WilsonPositionHomogeneousFrame.reading F J Z
local notation "Γ" => Glyph B d
local notation "parameter" => WilsonPositionBareSimultaneous.parameter Z index θ
local notation "degree" => WilsonPositionBareSimultaneous.degree Z index θ

def BasisHearing {r:ℝ}(hr:0<r)(q:ℕ){budget:ℕ}(P:Handoff.Directory Z (index r) budget)
    (arms:Bool→(y:S.Field d)→Arm R.family S (l:Filter _) d y)
    (L:(p.probes.index→ℂ)→L[ℂ](Bel R.family.book).Field d):Prop:=
  ∀c∈(Z.run.step (index r)).Box,∀moving:Bool,∀(t:ℝ)(ht:0<t),r≤t →
  ∀(w:ℕ×ℕ→Γ→ℂ)(A' e:ℝ),(∀ᶠ z in (l:Filter _), charge (w z)≤A') →
    let entry :=fun z branch => coordinate B F J Z p hr arms L branch z (w z)
    let matrix:=fun z=>WilsonPositionProgramPublicDirectoryBoard.table Z axis b q (id:Γ→Γ)
      P (parameter r (source F J Z A r moving z)) c
    let arm:=fun (i:Γ) br=>arms br (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) i)
    (∀ᶠ z in (l:Filter _),∀br s, ‖assay (weighted (id:Γ→Γ) (r/t) (entry z br))
        (weighted (id:Γ→Γ) (r/t) (entry z s)) (matrix z)-
        WilsonPositionProgramPublicWideHearing.paid F arm axis b ht (w z) z br s‖≤e) →
    ∀η:ℝ,0<η→ ∀ᶠ z in (l:Filter _),k*((r/t)^d*‖entry z false-entry z true‖)^2≤4*e+η

def Posted (r:ℝ)(cap:d≤D){s w:ℝ}(stock:Bank F l D s w)(q:ℕ)
    {budget:ℕ}(P:Handoff.Directory Z (index r) budget):Prop:=
  ∃(n:ℕ)(fits:D≤n)(W:Vane R.family n)(T:Spin.change S d)
    (pair:Pair F stock cap W fits T r)(hr:0<r),
    W.checked f Y n ∧ W.wheel.r=r ∧ D≤W.k ∧
    (0<purchaseWidth W ∧ 20*R.family.S.a (purchaseWidth W)<R.family.S.a (purchaseWidth W-1) ∧
      R.family.S.a (purchaseWidth W-1)<r*LogV r/32) ∧
    ∃L:(p.probes.index→ℂ)→L[ℂ](Bel R.family.book).Field d,‖L‖≤C ∧
    (∀y,L (samples F J Z p r y)=y) ∧ (∀y,‖y‖^2≤C^2*square (samples F J Z p r y)) ∧
    (∀ᶠ z in (l:Filter _),Roster F J Z (axes R B d) p hr (issued B F J Z (r:=r) pair.arm) L z) ∧
    BasisHearing F J Z B axis A index p b k hr q P pair.arm L

variable {g:G.Simple}
    {M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}{σ:Prescription (Press.portDeck G)}
    {dial:Bool} (H:Main.Match Z g M σ dial) {B₀:ℕ}(hB:0<B₀) (pace:WilsonWindowReportingPace.Slow R.kit)
    (fine:ℝ→ℕ)(schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=g) (B:=B₀) Z fine index)

include H hB pace schedule in
theorem original {arch:Arch R.family} (bliss:Bliss F l arch Y)(lead:Leading F J)
    (income:∀d,∀ᶠ r in trail,Frame.obedient F Y (J r) d)
    (cap:d≤D)(group:WilsonPositionCapTransport.Book (f:=f) (l:=l) (H:=Y) A J)(meter:Coupling G θ):
    ∃(T:ℕ)(p:Profiles R d)(C:ℝ)(b:Bulb (center axis) axis)(k:ℝ),0<C ∧ 0<k ∧
    ∀(q:ℕ)(ε:ℝ),0<ε→∀ᶠ r in trail,
      ∃P:Handoff.Directory Z (index r) (Handoff.Directory.budget G 2 d+q),
      (∀moving:Bool,∀ᶠ z in (l:Filter _),let value:=source F J Z A r moving z
                                        let u:=parameter r value
                                        |u|≤8*θ r ∧ WilsonPositionRawMesh.forward Z (Z.run.step (index r)) (degree r) u=value ∧
                                          |WilsonPositionRawMesh.forward Z (Z.run.step (index r)) q u-value|≤ε*|θ r|^q) ∧
      (let s:=WilsonThermometerUnitFilingFourPoolShell.radius arch T r
       ∃stock:Bank F l D s (dock s^T), Posted F J Z B axis A index p b k C (Y:=Y) r cap stock q P) ∧
      ∀s w (stock:Bank F l D s w),Posted F J Z B axis A index p b k C (Y:=Y) r cap stock q P :=by
  obtain ⟨T,p,C,hC,frames⟩:=WilsonPositionProgramPublicFourFrame.original F J Z (axes R B d) g bliss lead income cap
  obtain ⟨b,k,hk,rates⟩:=WilsonPositionProgramPublicEnrolledRates.original (id:Γ→Γ) F axis J Z H hB pace
    fine index schedule A Function.injective_id bliss.lies lead group meter
  refine ⟨T,p,C,b,k,hC,hk,?_⟩
  intro q ε hε
  filter_upwards [frames,rates q ε hε] with r available book
  obtain ⟨P,paid⟩:=book
  refine ⟨P,fun moving=>(paid moving).mono fun z cost=>⟨cost.1,cost.2.1,cost.2.2.1⟩,?_⟩
  have carry (s w:ℝ)(stock:Bank F l D s w) :
      Posted F J Z B axis A index p b k C (Y:=Y) r cap stock q P:=by
    obtain ⟨n,nd,W,turn,pair,hr,good,atR,high,width,L,bound,read,gram,sale,_⟩:=available.2 s w stock
    refine ⟨n,nd,W,turn,pair,hr,good,atR,high,width,L,bound,read,gram,sale,?_⟩
    intro c hc moving t ht wide w A' e hA
    exact fun four η hη=>WilsonPositionProgramPublicEnrolledMatrix.oriented (id:Γ→Γ) F
      (fun i br=>pair.arm br (WilsonPositionProgramPublicMeasuredAxes.position B F J Z (r:=r) i)) axis bliss.lies b hk ht hr wide w
      (fun z branch=>coordinate B F J Z p hr pair.arm L branch z (w z)) _ hA
      ((paid moving).mono fun z inc=>inc.2.2.2 c hc) four η hη
  exact ⟨⟨available.1.choose,carry _ _ _⟩,carry⟩
end YM.Integration.WilsonPositionProgramPublicPositionNormalization
