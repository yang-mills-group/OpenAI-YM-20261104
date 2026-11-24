import YM.Integration.WilsonOriginalGeneralRosterFile
import YM.Integration.WilsonOriginalGeneralRosterPlacement
import YM.Integration.WilsonPhysicalMovingForkCutEars
import YM.Integration.WilsonMeasuredPublicEntranceAllCutoffs

/-! The original paid course issues upper marked-field readings for any finite menu.
All request powers are fixed before the compact, the optical dates, the programme
and both regulators. A single collar and a single earlier physical date cover all
homogeneous/heterogeneous choices, motions, cell positions and deletion faces. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterSale
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

def Register (h t:ℕ)(d:I→Fin (D+1))
    (field:(i:I)→{s:ℝ//0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val):Prop:=
  ∃M:I→ℝ,∃E:I→ℕ,(∀i,1≤M i) ∧ ∀n:ℕ,0<n→∀(port:Fin n→I)(desired target:ℕ),
    let request:=desired+∑v,E (port v)
    let g:=fun v=>(d (port v)).val
    let pwr:=univ.sup (accuracy g request)+1
    let reserve:=depth ((2*pwr+∑i,E i)+1) (width T h) D
    let tuition:=max 1 (4*∑i,M i)
    let power:=(∑i,E i)+WilsonAddressedMixedRawTrial.power T h reserve D
    ∀φ:Test n,∀ᶠm:ℕ in atTop,∀u:ℕ,m≤u→∀ᶠr in trail,
    ∀ρ:I→{s:ℝ//0<s ∧ s<δ},(∀i,r≤(ρ i).val ∧ (ρ i).val≤outer z h r)→(∃i,(ρ i).val=r)→
    let f:=reporter F books ρ
    let K:=berth R reserve f
    ∃j:ℕ,u≤j ∧ j+2≤f ∧
      (∀mode:Bool,WilsonReflectedMixedLocatedSchool.Paid F D T d books (fun i s=>field i s mode) M E ρ f) ∧
      ∀mode branch:Fin n→Bool,
      Sold F (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (tuition:=tuition) (power:=power)
        (target:=target) (t:=t) port mode branch f K m j request desired φ r

universe u
theorem original {simple:G.Simple}{axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {campaign:Campaign R}{W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (P))(lamp:WilsonReportLampForecast.Ready (P))
    (bliss:Bliss F l z H)
    (prior:WilsonMeasuredPublicEntrancePanelSchool.Registered F D T h t d books field):
    Register F books h t d field:=by
  classical
  obtain ⟨M,E,one,store⟩:=WilsonMeasuredPublicEntranceAllCutoffs.original F prior
  refine ⟨M,E,one,?_⟩
  intro n np port desired target request g pwr reserve tuition power
  let e:=fun _:I=>univ.sup (accuracy g request)
  have fits(i:Fin n):accuracy g request i≤e (port i):=le_sup (mem_univ i)
  have enough(i:I):e i+1≤2*pwr:=by dsimp [e,pwr];omega
  have tickets:=store e pwr target enough
  have fee:Fee (M∘port) (E∘port) request desired:=by
    refine ⟨fun i=>one (port i),fun s=>Nat.add_le_add_left ?_ desired⟩
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  intro φ
  letI:Nonempty (Fin n):=⟨⟨0,np⟩⟩
  have costs:=WilsonOriginalPhysicalFirstEntryOwnerFinance.attached paid
  obtain ⟨_,faculty⟩:=WilsonMeasuredPublicEntranceMasterUpper.original R simple costs.2.1 costs.2.2.2
    costs.2.2.1 bank lamp costs.1 paid
  obtain ⟨apron,place⟩:=WilsonOriginalGeneralRosterPlacement.original F simple bliss costs.2.1 d books φ h
  have size:Fintype.card (Fin n)≤n:=by simp
  let first:=threshold R simple costs.2.1 costs.2.2.2 costs.2.2.1 bank lamp costs.1
    g n apron request t reserve power (capital R D tuition) np size
  have pos:0≤capital R D tuition:=by unfold capital;positivity
  obtain ⟨ear,openEar⟩:=eventually_atTop.mp (open_late (C) simple 0)
  filter_upwards [faculty n D request,eventually_ge_atTop ear] with m classAt start
  intro u mu
  let floor:=max u first
  have stations:=WilsonAddressedMixedStationRange.original F simple bliss costs.2.1 D T h floor d books
  filter_upwards [place floor,stations,tickets] with r housed times filed
  intro ρ span near f K
  obtain ⟨j,fj,height,support⟩:=housed ρ span near
  have uj:u≤j:=(le_max_left u first).trans fj
  have firstJ:first≤j:=(le_max_right u first).trans fj
  have jf:j≤f:=(Nat.le_add_right j 2).trans height
  have joined:=filed ρ span near
  obtain ⟨wages,pinned,_,campus⟩:=joined
  have fk:=pinned.choose
  refine ⟨j,uj,height,wages,?_⟩
  intro mode branch
  refine WilsonOriginalGeneralRosterFile.original F port mode branch campus pinned fits fee jf
    (fun N per cut a=>(support N per (fk.le.trans cut) a).2) ?_
  intro N per cut road a A station loc v uv vj vf
  have mN:=mu.trans (uj.trans (jf.trans (road.trans cut)))
  obtain ⟨_,_,_,offer⟩:=classAt N mN
  have bill:=offer (Fin n) g np size (fun i=>Nat.le_of_lt_succ (d (port i)).isLt) apron request t reserve power
    (capital R D tuition) pos per
  have begin(i:Fin n):first≤A.slot i:=by
    rw [station]
    exact (le_max_right u first).trans ((times ρ span near).2 (port i) (branch i)).1
  have ground:WilsonMeasuredPublicEntranceScreen.Ground R N per j f apron A.loc:=by
    rw [loc]
    exact (support N per (road.trans cut) a).1
  exact bill j f K firstJ (mu.trans uj) height rfl road cut A begin (Or.inr ground) v uv vj
    (openEar v (start.trans uv) per) (openEar j (start.trans (mu.trans uj)) per)

end YM.Integration.WilsonOriginalGeneralRosterSale
end
