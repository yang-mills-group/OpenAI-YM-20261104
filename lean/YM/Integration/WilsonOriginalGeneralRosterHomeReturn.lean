import YM.Integration.WilsonOriginalGeneralRosterUnionReturn
import YM.Integration.WilsonOriginalGeneralRosterHomeUnion
import YM.Integration.WilsonOriginalGeneralRosterHomeScalar

/-! The full ordinary Wilson expectation on a bank of row-dependent tests and
arities, heard at two common earlier stops on the same filed stocks. -/
set_option autoImplicit false
set_option quotPrecheck false
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

def Register (h t:ℕ)(d:I→Fin (D+1))
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
      ∀w:B,∃j:ℕ,ear₁≤j ∧ j+2≤f ∧ ∀ scale : ℝ, r ≤ scale → scale ≤ outer z h r → ∀mode branch:Fin (rows w).size→Bool,
        Returned F books field (ρ:=ρ) (rows w).stock mode branch A M E tuition power target t
          f K base j ear₀ ear₁ (request E (rows w)) (rows w).desired (rows w).test scale

theorem original (fac:Facilities (C) order S)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (grant:WilsonOriginalGeneralRosterHomeUnion.Register F books h t d field):
    WilsonOriginalGeneralRosterHomeReturn.Register F books h t d field:=by
  classical
  obtain ⟨M,E,one,issue⟩:=grant
  refine ⟨M,E,one,?_⟩
  intro B _ rows target e pwr reserve tuition power floor
  obtain ⟨m,store,fm⟩:=((issue B rows target).and (eventually_ge_atTop floor)).exists
  obtain ⟨J,u,mj,ju,stop⟩:=WilsonMovingForkElectedPhase.fixed fac m
  obtain ⟨J',v,old,jv,other⟩:=WilsonMovingForkElectedPhase.fixed fac (u+1)
  have uv:u<v:=old.trans jv
  have mv:=mj.trans (ju.trans uv.le)
  have intake (w:B)(b tag:ℕ)(licensed:Stop (C) 0 tag b):=WilsonOriginalGeneralRosterHomeScalar.original F d books
    (rows w).stock (h:=h) fac bliss slow licensed (rows w).test (request E (rows w))
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
  let φ:=row.test
  let desired:=row.desired
  obtain ⟨j,vj,height,seats⟩:=cohort w
  refine ⟨j,vj,height,?_⟩
  intro scale lower upper mode branch
  have installed(b:ℕ)(source:∃bf:b≤f,∀N per (fine:f<N)(s:(Stock.census (Fin n)).Mode)
      (weak:Fin n→Bool)(x:∀i,S.Field ((d (port i)).val))(a:cells R φ scale (f,per))(turn:Fin n→Motion),
        let Y:=fun i=>(((books (ρ (port i))).rows (d (port i))).arm (weak i) (x i)).source (N,per)
        ‖WilsonOriginalGeneralRosterScalar.gap (R:=R) d port bf fine s Y turn a.val‖ ≤
          WilsonOriginalGeneralRosterScalar.directPrice F d books port ρ f (request E row) weak x s):
      Phase F books field (ρ:=ρ) port M E b f desired φ scale:=by
    obtain ⟨bf,funded⟩:=source
    refine ⟨bf,?_⟩
    intro N per fine s mode weak a motion
    let x:=fun i=>field (port i) (ρ (port i)) (mode i) (weak i)
    exact (funded N per fine s weak x a motion).trans (WilsonOriginalGeneralRosterFare.bill F d books port
      ρ f desired weak x s M E one (fun i=>(charges (mode i) (port i) (weak i)).2.2))
  exact assemble F books field port mode branch one (mj.trans ju) uv.le vj
    (installed u (early w ρ span near scale lower upper)) (installed v (late w ρ span near scale lower upper)) (seats scale lower upper mode branch)

end YM.Integration.WilsonOriginalGeneralRosterHomeReturn
end
