import YM.Integration.WilsonOriginalGeneralRosterUnion
import YM.Integration.WilsonOriginalGeneralRosterHomeScreen

/-! All rows of one finite experiment share a single planted cutoff and one
matrix bank. A repeated source stock has the same axis in every row,
including at the cutoff itself. -/
set_option autoImplicit false
set_option quotPrecheck false
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

def Register (h t:ℕ)(d:I→Fin (D+1))
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
      ∀w:B,∃j:ℕ,u≤j ∧ j+2≤f ∧ ∀ scale : ℝ, r ≤ scale → scale ≤ outer z h r → ∀mode branch:Fin (rows w).size→Bool,
        WilsonOriginalGeneralRosterUnionFile.Sold F (books:=books) (field:=field) (ρ:=ρ) (M:=M) (E:=E)
          (tuition:=tuition) (power:=power) (target:=target) (t:=t) (rows w).stock mode branch A
          f K m j (request E (rows w)) (rows w).desired (rows w).test scale

universe u
theorem original {simple:G.Simple}{axis:Axis}{ε:ℝ}{σ:WilsonOriginalAllOrderCourse.Schedule G}
    {campaign:Campaign R}{W:Campaign.Pillars R campaign}
    (paid:WilsonOriginalAllOrderCourse.Paid.{u} axis simple ε σ R campaign W)
    (bank:WilsonThermometerClusterProjectionBudget.Ready (P))(lamp:WilsonReportLampForecast.Ready (P))
    (bliss:Bliss F l z H)(prior:WilsonMeasuredPublicEntrancePanelSchool.Registered F D T h t d books field):
    Register F books h t d field:=by
  classical
  obtain ⟨M,E,one,store⟩:=WilsonMeasuredPublicEntranceAllCutoffs.original F prior
  refine ⟨M,E,one,?_⟩
  intro B _ rows target e pwr reserve tuition power
  have enough(i:I):e i+1≤2*pwr:=by
    have bound:e i≤univ.sup e:=le_sup (mem_univ i)
    dsimp only [pwr]
    omega
  have tickets:=store e pwr target enough
  have prepared:=eventually_all.mpr fun w:B=>WilsonOriginalGeneralRosterHomeScreen.original F books
    (d:=d) (rows w).stock paid bank lamp bliss (rows w).positive (rows w).test tuition
    (request E (rows w)) reserve power h t
  filter_upwards [prepared] with m ready
  intro u mu
  filter_upwards [tickets,eventually_all.mpr fun w:B=>ready w u mu] with r sold allReady
  intro ρ span near f K
  obtain ⟨wages,pinned,_,campus⟩:=sold ρ span near
  obtain ⟨A,issue⟩:=WilsonOriginalGeneralRosterUnionFile.original F campus pinned
  refine ⟨A,wages,?_⟩
  intro w
  obtain ⟨j,uj,room,all⟩:=allReady w ρ span near
  refine ⟨j,uj,room,?_⟩
  intro scale lower upper mode branch
  obtain ⟨jf,apart,hear⟩:=all scale lower upper
  apply issue (rows w).stock mode branch (meets d E rows w) _ jf apart (hear branch)
  exact ⟨fun i=>one ((rows w).stock i),fun s=>Nat.add_le_add_left
    (Finset.sum_le_sum_of_subset (Finset.subset_univ _)) (rows w).desired⟩

end YM.Integration.WilsonOriginalGeneralRosterHomeUnion
end
