import YM.Integration.WilsonOriginalGeneralRosterUnionReturn
import YM.Integration.WilsonOriginalGeneralRosterFirstJoin

/-! The signed measured source before its first joins. Disjoint occupied
blocks use their physical means, their true older covariance, and each
intervening original join. The four-component instance splits 01 and 23. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalGeneralRosterJoinedRead
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

open Function Finset MeasureTheory Lattice RG Wilson Source Labels OPE.Therm
open PhysicalNext.Repeat.Legato Extra.Histories Motion Marker
open WilsonOriginalGeneralRosterFirstJoin (mark)
open WilsonOriginalCovarianceDatedPassage (level joint)
open WilsonOriginalGeneralRosterUnionReturn (Returned)
local notation "μ" N:max per:max => scene (C).path N per N

def Joined {f N per:ℕ}(φ:Test n)(r:ℝ)(turn:cells R φ r (f,per)→Fin n→Motion)
    (all left right:Finset (Fin n))(age:ℕ):Prop:=
  let fields:=fun (a:cells R φ r (f,per)) (s:Finset (Fin n))=>physical R (g) (N:=N) (names N per) (turn a) a.val (mark s)
  signed R φ r (f,per) (fun a=>∫U,fields a all U ∂(μ N per))=
    signed R φ r (f,per) (fun a=>(∫U,fields a left U ∂(μ N per))*(∫U,fields a right U ∂(μ N per))+
      level R N (fields a left) (fields a right) age+
        ∑w∈range (N-age),joint R N (fields a left) (fields a right) (age+w))

omit [Fintype I] [Nonempty I] in
theorem filed {N per f K base top req want power t:ℕ}{fk:f≤K}{kn:K≤N}{M:I→ℝ}{E:I→ℕ}{tuition:ℝ}
    (file:Filed R (g) K){φ:Test n}{r:ℝ}(turn:cells R φ r (f,per)→Fin n→Motion)
    (panels:cells R φ r (f,per)→Panel R (g) N per f K fk kn req power t (capital R D tuition))
    (deed:Issued (F:=F) (books:=books) (field:=field) (M:=M) (E:=E) (ρ:=ρ) (u:=base) (j:=top) (desired:=want)
      port mode branch file φ r turn panels)
    (left right:Finset (Fin n))(disj:Disjoint left right){age:ℕ}(old:age≤N):
    Joined F books field port mode branch (ρ:=ρ) (N:=N) φ r turn (left∪right) left right age:=by
  unfold Joined
  apply congrArg (signed R φ r (f,per))
  funext a
  have law:=WilsonOriginalGeneralRosterFirstJoin.original R (panels a) left right disj old
  rw [deed.namesEq a,deed.motion a,deed.location a] at law
  exact law

omit [Fintype I] [Nonempty I] in
theorem original {axes:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val)}
    {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target f K base top u v req want:ℕ}{φ:Test n}{r:ℝ}
    (received:Returned F books field (ρ:=ρ) port mode branch axes M E tuition power target t f K base top u v req want φ r)
    (program:Program R (g) K)(N per:ℕ)(kn:K≤N)(turn:cells R φ r (f,per)→Fin n→Motion)
    (left right:Finset (Fin n))(disj:Disjoint left right){age:ℕ}(old:age≤N):
    Joined F books field port mode branch (ρ:=ρ) (N:=N) φ r turn (left∪right) left right age:=by
  obtain ⟨_,file,_,_,_,_,_,campus⟩:=received program
  obtain ⟨panels,deed,_⟩:=campus N per kn turn
  exact filed F books field port mode branch (ρ:=ρ) file turn panels deed left right disj old

omit [Fintype I] [Nonempty I] in
theorem four (four:Fin 4→I)(orient arm:Fin 4→Bool)
    {axes:∀_N _per:ℕ,(i:I)→Bool→((C).label (d i).val≃ₗ[ℂ](C).label (d i).val)}
    {M:I→ℝ}{E:I→ℕ}{tuition:ℝ}{power target f K base top u v req want:ℕ}{φ:Test 4}{r:ℝ}
    (received:Returned F books field (ρ:=ρ) four orient arm axes M E tuition power target t f K base top u v req want φ r)
    (program:Program R (fun i=>(d (four i)).val) K)(N per:ℕ)(kn:K≤N)(turn:cells R φ r (f,per)→Fin 4→Motion)
    {age:ℕ}(old:age≤N):
    Joined F books field four orient arm (ρ:=ρ) (N:=N) φ r turn Finset.univ {0,1} {2,3} age:=by
  have split:({0,1}:Finset (Fin 4))∪{2,3}=Finset.univ:=by decide
  simpa only [split] using original F books field four orient arm received program N per kn turn {0,1} {2,3} (by decide) old

end YM.Integration.WilsonOriginalGeneralRosterJoinedRead
end
