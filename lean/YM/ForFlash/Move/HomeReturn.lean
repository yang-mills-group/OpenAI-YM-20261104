import YM.ForFlash.Move.Lodging
import YM.Integration.WilsonOriginalGeneralRosterHomeReturn
/-! Flash lodgings: moving upper sizes and absolute gap prices, on the
genuine roster. Variants of WilsonOriginalGeneralRoster* (point version,
including the licensed scalar phase). -/
set_option autoImplicit false
set_option quotPrecheck false

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterFile
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReflectedMixedSharedAxis (Pinned)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonMeasuredPublicEntrancePanel (Panel Reading accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker
open Climb Maxwell Maxwell.Free Trace.Terrace Trace.Physical Trace.Physical.Germ GapsContact
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    {books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E e:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ//0<s ∧ s<δ}}
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool)
local notation "g" => fun v:Fin n=>(d (port v)).val
local notation "slots" => fun v:Fin n=>WilsonReflectedPublicStationFare.station F ((books (ρ (port v))).rows (d (port v))) (branch v)
local notation "names" N:max per:max => fun v:Fin n=>
  (((books (ρ (port v))).rows (d (port v))).arm (branch v) (field (port v) (ρ (port v)) (mode v) (branch v))).source (N,per)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "reg" => Stock.census (Fin n)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

structure IssuedForFlash {f K N per u j request desired:ℕ}{fk:f≤K}{cut:K≤N}
    (file:Filed R (g) K)(box slit:ℝ)
    (turn:Grow R n box slit f per→Fin n→Motion)
    (panels:Grow R n box slit f per→Panel R (g) N per f K fk cut request power t (capital R D tuition)):Prop where
  slotsEq : ∀a,(panels a).slot=file.station
  axesEq : ∀a,(panels a).axis=file.A N per
  namesEq : ∀a,(panels a).names=names N per
  salary : ∀a,(panels a).M=M∘port
  location : ∀a,(panels a).loc=a.val
  motion : ∀a,(panels a).turn=turn a
  spent : ∀a i,Next.Rank.Spindle.paid (C) ((g) i) f N per ((panels a).names i)≤M (port i)*(β f)^(E (port i))
  density : ∀a,WilsonOriginalGeneralRosterDensity.Restored (panels a)
  hearing : ∀a v,u≤v→v≤j→∀vf:v≤f, Reading R (g) (panels a) vf
  cell : ∀v,u≤v→v≤j→∀vk:v≤K,∀s:(reg).Mode,∀a:Grow R n box slit f per,
    ‖WilsonMeasuredPublicEntranceCutoffHearing.difference R (g) file fk cut vk (names N per) (turn a) a.val s‖≤
      price (R:=R) (g) (M∘port) f desired s


end YM.Integration.WilsonOriginalGeneralRosterFile
end

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterUnionFile
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonReflectedMixedSharedAxis (Pinned)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonMeasuredPublicEntrancePanel (Panel Reading accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker
open Climb Maxwell Maxwell.Free Trace.Terrace Trace.Physical Trace.Physical.Germ GapsContact
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    {books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val}
    {field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:I→ℝ}{E e:I→ℕ}{tuition:ℝ}{power target:ℕ}{ρ:I→{s:ℝ//0<s ∧ s<δ}}
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool)
local notation "g" => fun v:Fin n=>(d (port v)).val
local notation "slots" => fun v:Fin n=>WilsonReflectedPublicStationFare.station F ((books (ρ (port v))).rows (d (port v))) (branch v)
local notation "names" N:max per:max => fun v:Fin n=>
  (((books (ρ (port v))).rows (d (port v))).arm (branch v) (field (port v) (ρ (port v)) (mode v) (branch v))).source (N,per)
local notation "C" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
local notation "reg" => Stock.census (Fin n)

open WilsonOriginalGeneralRosterFile (Fee Issued price)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

open WilsonOriginalGeneralRosterFile (IssuedForFlash)
def SoldForFlash (A:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val)) (f K u j request desired:ℕ)(box slit:ℝ):Prop:=
  ∀program:Program R (g) K,∃fk:f<K,∃file:Filed R (g) K,
    file.A=(fun N per i=>A N per (port i) (branch i)) ∧ file.station=slots ∧ file.target=target ∧
    (∀N per w pins age,age<K→file.row N per w pins age=WilsonMovingForkPrintedFile.row program N per w pins age) ∧
    (∀N per (_:K≤N) w pins,file.row N per w pins K=WilsonMovingForkMixedSeed.product R (g) (N:=N) pins w) ∧
    ∀N per (cut:K≤N)(turn:Grow R n box slit f per→Fin n→Motion),
      ∃panels:Grow R n box slit f per→Panel R (g) N per f K fk.le cut request power t (capital R D tuition),
        IssuedForFlash (F:=F) (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (u:=u) (j:=j)
          (desired:=desired) port mode branch file box slit turn panels

theorem originalForFlash {f K:ℕ}
    (campus:School F D T t d e books field M E tuition power target ρ f K)
    (pinned:Pinned F D T h t d e books field M tuition power target ρ f K):
    ∃A:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val),
    ∀{n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool){u j request desired:ℕ}{box slit:ℝ}
    (_fit:∀i,accuracy (fun i:Fin n=>(d (port i)).val) request i≤e (port i))(_fee:Fee (M∘port) (E∘port) request desired)
    (_jf:j≤f)
    (_apart:∀N per, K≤N→∀a:Grow R n box slit f per,
      Pairwise fun i k=>(R.family.path.levels.budget f).B^2<separation (a.val i) (a.val k))
    (_hears:∀N per (cut:K≤N)(fk:f≤K) (a:Grow R n box slit f per)
      (P:Panel R (fun i:Fin n=>(d (port i)).val) N per f K fk cut request power t (capital R D tuition)),P.slot=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ (port i))).rows (d (port i))) (branch i))→P.loc=a.val→
      ∀v,u≤v→v≤j→∀vf:v≤f, Reading R (fun i:Fin n=>(d (port i)).val) P vf),
    SoldForFlash F (books:=books) (field:=field) (ρ:=ρ) (M:=M) (E:=E) (tuition:=tuition) (power:=power)
      (target:=target) (t:=t) port mode branch A f K u j request desired box slit:=by
  classical
  obtain ⟨up,_,physical,_,registered⟩:=WilsonPhysicalMovingForkPinnedMaster.original F pinned
  obtain ⟨_,axes,_,offer⟩:=campus
  refine ⟨(fun N per i b=>if N=K then axes per i b else physical N per i b),?_⟩
  intro n port mode branch u j request desired box slit fit fee jf apart hears program
  obtain ⟨old,stations,aim,oldAxes,word⟩:=registered port branch program
  let matrix:=fun per i=>axes per (port i) (branch i)
  let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R (fun i:Fin n=>(d (port i)).val) old matrix
  refine ⟨up,file,?_,stations,aim,?_,?_,?_⟩
  · funext N per i
    change (if N=K then matrix per i else old.A N per i)=_
    rw [oldAxes]
  · intro N per w pins age below
    change dite (age=K) _ (fun _=>old.row N per w pins age)=_
    rw [dif_neg (Nat.ne_of_lt below),word]
  · intro N per cut w pins
    exact WilsonMeasuredPublicEntranceCutoffFile.original R (fun i:Fin n=>(d (port i)).val) old matrix cut per w pins
  intro N per cut turn
  obtain ⟨_,_,_,_,issued⟩:=offer N per cut
  have get(a:Grow R n box slit f per):=issued n port mode branch old stations request fit (turn a) a.val (fun i k hne=>apart N per cut a hne)
  choose panels entries using get
  have locate(a:Grow R n box slit f per): (panels a).loc=a.val:=(entries a).2.2.2.2.2.2.2.1
  have heard(a:Grow R n box slit f per):=hears N per cut up.le a (panels a) ((entries a).1.trans stations) (locate a)
  have bound(v:ℕ)(uv:u≤v)(vj:v≤j)(vk:v≤K)(s:(Stock.census (Fin n)).Mode)(a:Grow R n box slit f per):
      ‖WilsonMeasuredPublicEntranceCutoffHearing.difference R (fun i:Fin n=>(d (port i)).val) file up.le cut vk (fun i:Fin n=>(((books (ρ (port i))).rows (d (port i))).arm (branch i) (field (port i) (ρ (port i)) (mode i) (branch i))).source (N,per)) (turn a) a.val s‖≤
        price (R:=R) (fun i:Fin n=>(d (port i)).val) (M∘port) f desired s:=by
    obtain ⟨slot,axis,name,amount,_,_,phase,place,_,_,_,refs,cash⟩:=entries a
    have minCost(i:Fin n):1≤(panels a).M i:=by rw [amount];exact fee.1 i
    have paid:=WilsonMeasuredPublicEntranceCellWords.paid R (fun i:Fin n=>(d (port i)).val) (panels a) file slot axis (vj.trans jf)
      (heard a v uv vj (vj.trans jf)) minCost (E∘port) refs cash s desired (fee.2 s)
    rw [WilsonMeasuredPublicEntranceCutoffHearing.original,name,phase,place,amount] at paid
    exact paid
  refine ⟨panels,?_⟩
  constructor
  · exact fun a=>(entries a).1
  · exact fun a=>(entries a).2.1
  · exact fun a=>(entries a).2.2.1
  · exact fun a=>(entries a).2.2.2.1
  · exact locate
  · exact fun a=>(entries a).2.2.2.2.2.2.1
  · intro a i
    obtain ⟨_,_,_,amount,_,_,_,_,_,_,_,_,cash⟩:=entries a
    simpa only [amount,Function.comp_apply] using cash i
  · intro a
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,refs,_⟩:=entries a
    exact WilsonOriginalGeneralRosterDensity.original (panels a) refs
  · exact heard
  · exact bound

end YM.Integration.WilsonOriginalGeneralRosterUnionFile
end

/-! Flash lodgings: moving upper sizes and absolute gap prices, on the
genuine roster. Variants of WilsonOriginalGeneralRoster* (point version,
including the licensed scalar phase). -/
set_option autoImplicit false
set_option quotPrecheck false

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterUnionScreen
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Climb Maxwell Maxwell.Free Trace.Terrace GapsContact PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntranceMasterUpper (threshold)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Sold Fee)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker WilsonLimitConstruction PhysMS
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
local notation "C" => R.family
local notation "P" => R.family.path.levels

open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonMeasuredPublicEntranceScreen (Ground)
variable {n:ℕ}(port:Fin n→I)
local notation "g" => (fun i:Fin n=>(d (port i)).val)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

def ReadyForFlash (tuition:ℝ)(request reserve power t m j f:ℕ)(box slit:ℝ)(ρ:I→{s:ℝ//0<s ∧ s<δ}):Prop:=
  let K:=berth R reserve f
  j≤f ∧ (∀N per,K≤N→∀a:Grow R n box slit f per,
    Pairwise fun i k=>(R.family.path.levels.budget f).B^2<separation (a.val i) (a.val k)) ∧
  ∀(branch:Fin n→Bool) N per (cut:K≤N)(fk:f≤K)(a:Grow R n box slit f per)
    (A:Panel R (g) N per f K fk cut request power t (capital R D tuition)),
    A.slot=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ (port i))).rows (d (port i))) (branch i))→
    A.loc=a.val→∀v,m≤v→v≤j→∀vf:v≤f,Reading R (g) A vf

end YM.Integration.WilsonOriginalGeneralRosterUnionScreen
end

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeScreen
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Climb Maxwell Maxwell.Free Trace.Terrace GapsContact PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntranceMasterUpper (threshold)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Sold Fee)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker WilsonLimitConstruction PhysMS
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
local notation "C" => R.family
local notation "P" => R.family.path.levels

open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonMeasuredPublicEntranceScreen (Ground)
variable {n:ℕ}(port:Fin n→I)
local notation "g" => (fun i:Fin n=>(d (port i)).val)

open WilsonOriginalGeneralRosterUnionScreen (Ready)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

open WilsonOriginalGeneralRosterUnionScreen (ReadyForFlash)
universe u
theorem originalForFlash {simple:G.Simple}{axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {campaign:Campaign R}{W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (P))(lamp:WilsonReportLampForecast.Ready (P))
    (bliss:Bliss F l z H)(np:0<n){L₀ η:ℝ}(lp:0<L₀)(ep:0<η)(tuition:ℝ)(request reserve power h t:ℕ):
    ∀ᶠ m:ℕ in atTop,∀u:ℕ,m≤u→∀ᶠr in trail,
    ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    ∃j:ℕ,u≤j ∧ j+2≤f ∧ ReadyForFlash F books (d:=d) port tuition request reserve power t m j f (L₀*outer z h r) (η*r) ρ:=by
  classical
  letI:Nonempty (Fin n):=⟨⟨0,np⟩⟩
  have costs:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
  obtain ⟨_,faculty⟩:=WilsonMeasuredPublicEntranceMasterUpper.original R simple costs.2.1 costs.2.2.2
    costs.2.2.1 bank lamp costs.1 paid
  obtain ⟨apron,place⟩:=WilsonOriginalGeneralRosterHomePlacement.originalForFlash F simple bliss costs.2.1 d books (n:=n) lp ep h
  have size:Fintype.card (Fin n)≤n:=by simp
  let first:=threshold R simple costs.2.1 costs.2.2.2 costs.2.2.1 bank lamp costs.1
    (g) n apron request t reserve power (capital R D tuition) np size
  have pos:0≤capital R D tuition:=by unfold capital;positivity
  obtain ⟨ear,openEar⟩:=eventually_atTop.mp (open_late (C) simple 0)
  filter_upwards [faculty n D request,eventually_ge_atTop ear] with m classAt start
  intro u mu
  let floor:=max u first
  have stations:=WilsonAddressedMixedStationRange.original F simple bliss costs.2.1 D T h floor d books
  filter_upwards [place floor,stations] with r housed times
  intro ρ span near f
  obtain ⟨j,fj,height,support⟩:=housed ρ span near
  have uj:u≤j:=(le_max_left u first).trans fj
  have firstJ:first≤j:=(le_max_right u first).trans fj
  have jf:j≤f:=(Nat.le_add_right j 2).trans height
  let K:=berth R reserve f
  have fk:f≤K:=(WilsonInvariantActionPosition.arrival R reserve f).1.le
  refine ⟨j,uj,height,?_⟩
  refine ⟨jf,fun N per cut a=>(support N per (fk.trans cut) a).2,?_⟩
  intro branch N per cut road a A station loc v uv vj vf
  have mN:=mu.trans (uj.trans (jf.trans (road.trans cut)))
  obtain ⟨_,_,_,offer⟩:=classAt N mN
  have bill:=offer (Fin n) (g) np size (fun i=>Nat.le_of_lt_succ (d (port i)).isLt) apron request t reserve power
    (capital R D tuition) pos per
  have begin(i:Fin n):first≤A.slot i:=by
    rw [station]
    exact (le_max_right u first).trans ((times ρ span near).2 (port i) (branch i)).1
  have ground:WilsonMeasuredPublicEntranceScreen.Ground R N per j f apron A.loc:=by
    rw [loc]
    exact (support N per (road.trans cut) a).1
  exact bill j f K firstJ (mu.trans uj) height rfl road cut A begin (Or.inr ground) v uv vj
    (openEar v (start.trans uv) per) (openEar j (start.trans (mu.trans uj)) per)


end YM.Integration.WilsonOriginalGeneralRosterHomeScreen
end

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeUnion
open Function Filter Set Finset MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open Climb Maxwell Maxwell.Free Trace.Terrace GapsContact PhysicalNext.Repeat.Legato
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntranceMasterUpper (threshold)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Sold Fee)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker WilsonLimitConstruction PhysMS
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
local notation "C" => R.family
local notation "P" => R.family.path.levels

open WilsonOriginalGeneralRosterUnion (Row request need meets)

def RegisterForFlash (L₀ η:ℝ) (h t:ℕ)(d:I→Fin (D+1))
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val):Prop:=
  ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀(B:Type)[Fintype B](rows:B→Row I)(target:ℕ),
    let e:=need d E rows
    let pwr:=univ.sup e+1
    let reserve:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let tuition:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h reserve D
    ∀ᶠm:ℕ in atTop,∀u:ℕ,m≤u→∀ᶠr in trail,
      ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      let K:=berth R reserve f
      ∃A:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val),
      (∀mode:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>field i s mode) M E ρ f) ∧
      ∀w:B,∃j:ℕ,u≤j ∧ j+2≤f ∧ ∀mode branch:Fin (rows w).size→Bool,
        WilsonOriginalGeneralRosterUnionFile.SoldForFlash F (books:=books) (field:=field) (ρ:=ρ) (M:=M) (E:=E)
          (tuition:=tuition) (power:=power) (target:=target) (t:=t) (rows w).stock mode branch A
          f K m j (request E (rows w)) (rows w).desired (L₀*outer z h r) (η*r)

universe u
theorem originalForFlash {simple:G.Simple}{axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {campaign:Campaign R}{W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (P))(lamp:WilsonReportLampForecast.Ready (P))
    (bliss:Bliss F l z H)(prior:WilsonMeasuredPublicEntrancePanelSchool.Registered F D T h t d books field){L₀ η:ℝ}(lp:0<L₀)(ep:0<η):
    RegisterForFlash F books L₀ η h t d field:=by
  classical
  obtain ⟨M,E,one,store⟩:=WilsonMeasuredPublicEntranceAllCutoffs.original F prior
  refine ⟨M,E,one,?_⟩
  intro B _ rows target e pwr reserve tuition power
  have enough(i:I):e i+1≤2*pwr:=by
    have bound:e i≤univ.sup e:=le_sup (mem_univ i)
    dsimp only [pwr]
    omega
  have tickets:=store e pwr target enough
  have prepared:=eventually_all.mpr fun w:B=>WilsonOriginalGeneralRosterHomeScreen.originalForFlash F books
    (d:=d) (rows w).stock paid bank lamp bliss (rows w).positive lp ep tuition
    (request E (rows w)) reserve power h t
  filter_upwards [prepared] with m ready
  intro u mu
  filter_upwards [tickets,eventually_all.mpr fun w:B=>ready w u mu] with r sold allReady
  intro ρ span near f K
  obtain ⟨wages,pinned,_,campus⟩:=sold ρ span near
  obtain ⟨A,issue⟩:=WilsonOriginalGeneralRosterUnionFile.originalForFlash F campus pinned
  refine ⟨A,wages,?_⟩
  intro w
  obtain ⟨j,uj,room,all⟩:=allReady w ρ span near
  refine ⟨j,uj,room,?_⟩
  intro mode branch
  obtain ⟨jf,apart,hear⟩:=all
  apply issue (rows w).stock mode branch (meets d E rows w) _ jf apart (hear branch)
  exact ⟨fun i=>one ((rows w).stock i),fun s=>Nat.add_le_add_left
    (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) (rows w).desired⟩


end YM.Integration.WilsonOriginalGeneralRosterHomeUnion
end

/-! Flash lodgings: moving upper sizes and absolute gap prices, on the
genuine roster. Variants of WilsonOriginalGeneralRoster* (point version,
including the licensed scalar phase). -/
set_option autoImplicit false
set_option quotPrecheck false

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterResponse
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Climb Maxwell Maxwell.Free Trace.Terrace GapsContact
open OPE PhysMS MS MS.Land FVA2 FVA2.Register Next.Extract GapsContact.Seams GapsContact.Ascent
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy Panel)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Sold Issued)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG16 RG16.Literal RG05Readout RG05Readout.Address RG05Readout.Records Marker
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool){ρ:I→{s:ℝ//0<s ∧ s<δ}}
local notation "C" => R.family
local notation "reg" => Stock.census (Fin n)
local notation "g" => fun v:Fin n=>(d (port v)).val
local notation "names" N:max per:max => fun i:Fin n=>
  (((books (ρ (port i))).rows (d (port i))).arm (branch i) (field (port i) (ρ (port i)) (mode i) (branch i))).source (N,per)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

def PhaseForFlash (M:I→ℝ)(_E:I→ℕ)(u f desired:ℕ)(box slit:ℝ):Prop:=
  ∃uf:u≤f,∀N per (fine:f<N)(s:(reg).Mode)(mode weak:Fin n→Bool)(a:Grow R n box slit f per)(turn:Fin n→Motion),
    let Y:=fun i=>(((books (ρ (port i))).rows (d (port i))).arm (weak i)
      (field (port i) (ρ (port i)) (mode i) (weak i))).source (N,per)
    ‖WilsonOriginalGeneralRosterScalar.gap (R:=R) d port uf fine s Y turn a.val‖ ≤ rotation (R:=R) (g) (M∘port) f desired s

end YM.Integration.WilsonOriginalGeneralRosterResponse
end

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterUnionReturn
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Climb Maxwell Maxwell.Free Trace.Terrace GapsContact
open OPE PhysMS MS MS.Land FVA2 FVA2.Register Next.Extract GapsContact.Seams GapsContact.Ascent
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy Panel)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Issued)
open WilsonOriginalGeneralRosterUnionFile (Sold)
open WilsonOriginalGeneralRosterUnion (Row request need)
open WilsonOriginalGeneralRosterResponse (difference Phase)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG16 RG16.Literal RG05Readout RG05Readout.Address RG05Readout.Records Marker
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool){ρ:I→{s:ℝ//0<s ∧ s<δ}}
local notation "C" => R.family
local notation "reg" => Stock.census (Fin n)
local notation "g" => fun v:Fin n=>(d (port v)).val
local notation "names" N:max per:max => fun i:Fin n=>
  (((books (ρ (port i))).rows (d (port i))).arm (branch i) (field (port i) (ρ (port i)) (mode i) (branch i))).source (N,per)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

open WilsonOriginalGeneralRosterFile (IssuedForFlash)
open WilsonOriginalGeneralRosterUnionFile (SoldForFlash)
open WilsonOriginalGeneralRosterResponse (PhaseForFlash)
def ReturnedForFlash (axes:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val)) (M:I→ℝ)(E:I→ℕ)(tuition:ℝ)(power target t:ℕ)(f K m j u v request desired:ℕ)
    (box slit:ℝ):Prop:=
  ∀program:Program R (g) K,∃fk:f<K,∃file:Filed R (g) K,
    file.A=(fun N per i=>axes N per (port i) (branch i)) ∧
    file.station=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ (port i))).rows (d (port i))) (branch i)) ∧
    file.target=target ∧
    (∀N per w pins e,e<K→file.row N per w pins e=WilsonMovingForkPrintedFile.row program N per w pins e) ∧
    (∀N per (_:K≤N) w pins,file.row N per w pins K=WilsonMovingForkMixedSeed.product R (g) (N:=N) pins w) ∧
    ∀N per (kn:K≤N)(turn:Grow R n box slit f per→Fin n→Motion),
      ∃A:Grow R n box slit f per→Panel R (g) N per f K fk.le kn request power t (capital R D tuition),
      IssuedForFlash (F:=F) (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (u:=m) (j:=j) (desired:=desired)
        port mode branch file box slit turn A ∧
      ∀b:ℕ,b=u∨b=v→∀bk:b≤K,∀s:(reg).Mode,
      (∀a:Grow R n box slit f per,
        ‖difference (N:=N) file fk.le bk (names N per) (turn a) a.val s‖≤debit (R:=R) (g) (M∘port) f desired s)

omit [Fintype I] [Nonempty I] in
theorem assembleForFlash {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target f K m j u v request desired:ℕ}{box slit:ℝ}
    {axes:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val)}
    (one:∀i,1≤M i)(mu:m≤u)(uv:u≤v)(vj:v≤j)
    (first:PhaseForFlash F books field (ρ:=ρ) port M E u f desired box slit)
    (second:PhaseForFlash F books field (ρ:=ρ) port M E v f desired box slit)
    (sold:SoldForFlash F (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (tuition:=tuition) (power:=power)
      (target:=target) (t:=t) port mode branch axes f K m j request desired box slit):
    ReturnedForFlash F books field (ρ:=ρ) port mode branch axes M E tuition power target t f K m j u v request desired box slit:=by
  intro program
  obtain ⟨fk,file,matrix,station,aim,before,seed,rows⟩:=sold program
  refine ⟨fk,file,matrix,station,aim,before,seed,?_⟩
  intro N per kn turn
  obtain ⟨A,issued⟩:=rows N per kn turn
  refine ⟨A,issued,?_⟩
  intro b atEar bk s
  have bounds:m≤b ∧ b≤j:=atEar.elim (fun eq=>eq ▸ ⟨mu,uv.trans vj⟩) (fun eq=>eq ▸ ⟨mu.trans uv,vj⟩)
  have p:PhaseForFlash F books field (ρ:=ρ) port M E b f desired box slit:=atEar.elim (fun eq=>eq ▸ first) (fun eq=>eq ▸ second)
  obtain ⟨bf,free⟩:=p
  have cell (a:Grow R n box slit f per):‖difference (N:=N) file fk.le bk (names N per) (turn a) a.val s‖≤
      debit (R:=R) (g) (M∘port) f desired s:=
    WilsonOriginalGeneralRosterFare.receipt d port fk kn bf file (names N per) (turn a) a.val s (M∘port)
      (free N per (fk.trans_le kn) s mode branch a (turn a)) (issued.cell b bounds.1 bounds.2 bk s a)
  exact cell

end YM.Integration.WilsonOriginalGeneralRosterUnionReturn
end

noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterHomeReturn
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext.Repeat.Legato Climb Maxwell Maxwell.Free Trace.Terrace GapsContact
open OPE PhysMS MS MS.Land FVA2 FVA2.Register Next.Extract GapsContact.Seams GapsContact.Ascent
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonInvariantActionPosition (berth)
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonMeasuredPublicEntrancePanel (accuracy Panel)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalGeneralRosterFile (Issued)
open WilsonOriginalGeneralRosterUnionFile (Sold)
open WilsonOriginalGeneralRosterUnion (Row request need)
open WilsonOriginalGeneralRosterResponse (difference Phase)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMovingForkPrintedFile (Program)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonReceivedChronologicalFixedRoseVariation (cells signed)
open RG16 RG16.Literal RG05Readout RG05Readout.Address RG05Readout.Records Marker
open scoped Classical BigOperators Topology

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
    (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
    {I:Type}[Fintype I][Nonempty I]{D T h t:ℕ}{d:I→Fin (D+1)}{δ:ℝ}
    (books:(s:{s:ℝ//0<s ∧ s<δ})→Book F (l:=l) H z D T s.val)
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val)
    {n:ℕ}(port:Fin n→I)(mode branch:Fin n→Bool){ρ:I→{s:ℝ//0<s ∧ s<δ}}
local notation "C" => R.family
local notation "reg" => Stock.census (Fin n)
local notation "g" => fun v:Fin n=>(d (port v)).val
local notation "names" N:max per:max => fun i:Fin n=>
  (((books (ρ (port i))).rows (d (port i))).arm (branch i) (field (port i) (ρ (port i)) (mode i) (branch i))).source (N,per)

open WilsonOriginalGeneralRosterUnionReturn (Returned assemble)

open WilsonOriginalGeneralRosterHomePlacement (Grow)

open WilsonOriginalGeneralRosterFile (IssuedForFlash)
open WilsonOriginalGeneralRosterUnionReturn (ReturnedForFlash assembleForFlash)
open WilsonOriginalGeneralRosterResponse (PhaseForFlash)
def RegisterForFlash (L₀ η:ℝ) (h t:ℕ)(d:I→Fin (D+1))
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val):Prop:=
  ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀(B:Type)[Fintype B](rows:B→Row I)(target:ℕ),
    let e:=need d E rows
    let pwr:=univ.sup e+1
    let reserve:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let tuition:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h reserve D
    ∀ lo : ℕ, ∃ (base j₀ ear₀ j₁ ear₁ : ℕ), lo ≤ base ∧ base ≤ j₀ ∧ j₀ ≤ ear₀ ∧ ear₀ < ear₁ ∧ j₁ ≤ ear₁ ∧ Stop (C) 0 j₀ ear₀ ∧ Stop (C) 0 j₁ ear₁ ∧
    ∀ᶠr in trail,
      ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
      let f:=reporter F books ρ
      let K:=berth R reserve f
      ∃A:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val),
      (∀mode:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>field i s mode) M E ρ f) ∧
      ∀w:B,∃j:ℕ,ear₁≤j ∧ j+2≤f ∧ ∀mode branch:Fin (rows w).size→Bool,
        ReturnedForFlash F books field (ρ:=ρ) (rows w).stock mode branch A M E tuition power target t
          f K base j ear₀ ear₁ (request E (rows w)) (rows w).desired (L₀*outer z h r) (η*r)

theorem originalForFlash (fac:Facilities (C) order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit){L₀ η:ℝ}(lp:0<L₀)(ep:0<η)
    (grant:WilsonOriginalGeneralRosterHomeUnion.RegisterForFlash F books L₀ η h t d field):
    WilsonOriginalGeneralRosterHomeReturn.RegisterForFlash F books L₀ η h t d field:=by
  classical
  obtain ⟨M,E,one,issue⟩:=grant
  refine ⟨M,E,one,?_⟩
  intro B _ rows target e pwr reserve tuition power floor
  obtain ⟨m,store,fm⟩:=((issue B rows target).and (eventually_ge_atTop floor)).exists
  obtain ⟨J,u,mj,ju,stop⟩:=WilsonMovingForkElectedPhase.fixed fac m
  obtain ⟨J',v,old,jv,other⟩:=WilsonMovingForkElectedPhase.fixed fac (u+1)
  have uv:u<v:=old.trans jv
  have mv:=mj.trans (ju.trans uv.le)
  have intake (w:B)(b tag:ℕ)(licensed:Stop (C) 0 tag b):=WilsonOriginalGeneralRosterHomeScalar.originalForFlash F d books
    (rows w).stock (h:=h) fac bliss slow licensed lp ep (request E (rows w))
  refine ⟨m,J,u,J',v,fm,mj,ju,uv,jv,stop,other,?_⟩
  filter_upwards [store v mv,eventually_all.mpr (fun w:B=>intake w u J stop),
    eventually_all.mpr (fun w:B=>intake w v J' other)] with r provided early late
  intro ρ span near f K
  obtain ⟨A,charges,cohort⟩:=provided ρ span near
  refine ⟨A,charges,?_⟩
  intro w
  let row:=rows w
  let n:=row.size
  let port:=row.stock
  -- no change of test on the diagonal
  let desired:=row.desired
  obtain ⟨j,vj,height,seats⟩:=cohort w
  refine ⟨j,vj,height,?_⟩
  intro mode branch
  have installed(b:ℕ)(source:∃bf:b≤f,∀N per (fine:f<N)(s:(Stock.census (Fin n)).Mode)
      (weak:Fin n→Bool)(x:∀i,S.Field ((d (port i)).val))(a:Grow R n (L₀ * outer z h r) (η*r) f per)(turn:Fin n→Motion),
        let Y:=fun i=>(((books (ρ (port i))).rows (d (port i))).arm (weak i) (x i)).source (N,per)
        ‖WilsonOriginalGeneralRosterScalar.gap (R:=R) d port bf fine s Y turn a.val‖ ≤
          WilsonOriginalGeneralRosterScalar.directPrice F d books port ρ f (request E row) weak x s):
      PhaseForFlash F books field (ρ:=ρ) port M E b f desired (L₀*outer z h r) (η*r):=by
    obtain ⟨bf,funded⟩:=source
    refine ⟨bf,?_⟩
    intro N per fine s mode weak a motion
    let x:=fun i=>field (port i) (ρ (port i)) (mode i) (weak i)
    exact (funded N per fine s weak x a motion).trans (WilsonOriginalGeneralRosterFare.bill F d books port
      ρ f desired weak x s M E one (fun i=>(charges (mode i) (port i) (weak i)).2.2))
  exact assembleForFlash F books field port mode branch one (mj.trans ju) uv.le vj
    (installed u (early w ρ span near)) (installed v (late w ρ span near)) (seats mode branch)


end YM.Integration.WilsonOriginalGeneralRosterHomeReturn
end
