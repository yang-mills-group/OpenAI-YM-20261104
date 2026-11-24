import YM.Integration.WilsonPhysicalLicensedFaces

/-! Appoint every public home before choosing the subset and its geometry.
The age of the common reporter may exceed the reporter of the selected subset. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalLicensedSelection
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceCellWords (physical)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{z:Trace.Terrace.Arch R.family}
  {lo wid teach}(L:Package R.family wid lo teach)
local notation "C₀" => R.family
local notation "a_" => R.family.S.a
local notation "β" => (C₀).path.levels.clock.hatBeta

open WilsonPhysicalLicensedFaces (measured)

include L in
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){J u:ℕ}
    (stop:Stop C₀ 0 J u){D T n:ℕ}(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{y:ℝ //0<y ∧ y<δ})→Book F (l:=l) H z D T s.val)(window q:ℕ):
    ∃gate:ℕ,∀ρ,∀f:ℕ,(∀i b,station F ((books (ρ i)).rows (d i)) b≤f) →
      ∀c:ℕ,gate≤c → u+2≤c → c+2≤f → a_ c/a_ f≤(β f)^window →
      ∀s:(Stock.census (Fin n)).Mode,s.val.Nonempty →measured F d books ρ q u f c s:=by
  classical
  let Sale (f:ℕ)(s:(Stock.census (Fin n)).Mode):Prop:=
    s.val.Nonempty →∀ρ,(∀i b,station F ((books (ρ i)).rows (d i)) b≤f) →∀c:ℕ,u+2≤c → c+2≤f →
      a_ c/a_ f≤(β f)^window →measured F d books ρ q u f c s
  have each (s:(Stock.census (Fin n)).Mode):∀ᶠf:ℕ in atTop,Sale f s:=by
    by_cases occupied:s.val.Nonempty
    · letI:Nonempty ↥s.val:=⟨⟨occupied.choose,occupied.choose_spec⟩⟩
      filter_upwards [WilsonPhysicalDisplayedCapture.original F L simple slow stop
        (fun i:↥s.val=>(d i).val) window q] with f paid
      intro _ ρ arrived c uc cf room N per deep o inside apart weak v turn uf
      have cost:=paid c uc cf room N per deep (fun i=>o i.val) (fun i=>inside i.val i.2) apart
        (fun i=> (books (ρ i.val)).rows (d i.val)) (fun i=>(books (ρ i.val)).checked)
        (fun i=>weak i.val) (fun i=>v i.val)
        (fun i=>arrived i.val (weak i.val))
        (fun i=>turn i.val) uf
      dsimp only at cost
      rw [←WilsonMeasuredPublicEntranceProperPhase.word_at R (fun i=>(d i).val) deep.le s o
        (fun i=>(((books (ρ i)).rows (d i)).arm (weak i) (v i)).source (N,per)) turn,
        WilsonMeasuredPublicEntranceProperPhase.actual] at cost
      exact cost
    · exact Eventually.of_forall fun _ h=>False.elim (occupied h)
  obtain ⟨gate,all⟩:=eventually_atTop.mp (eventually_all.mpr each)
  refine ⟨gate,?_⟩
  intro ρ f arrived c gc uc cf room s occupied
  exact all _ (gc.trans (by omega)) s occupied ρ arrived c uc cf room

include L in
theorem selected {I:Type}[Fintype I](simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){J u:ℕ}
    (stop:Stop C₀ 0 J u){D T n:ℕ}(d:I→Fin (D+1))(sel:Fin n→I){δ:ℝ}
    (books:(s:{y:ℝ //0<y ∧ y<δ})→Book F (l:=l) H z D T s.val)(window q:ℕ):
    ∃gate:ℕ,∀ρ,let f:=reporter F books ρ
      ∀c:ℕ,gate≤c → u+2≤c → c+2≤f → a_ c/a_ f≤(β f)^window →
      ∀s:(Stock.census (Fin n)).Mode,s.val.Nonempty →
        measured F (fun i=>d (sel i)) books (fun i=>ρ (sel i)) q u f c s:=by
  obtain ⟨gate,pay⟩:=original F L simple slow stop (fun i=>d (sel i)) books window q
  exact ⟨gate,fun ρ=>pay (fun i=>ρ (sel i)) (reporter F books ρ)
    (fun i b=>WilsonMovingForkOpticalBook.station_le F books ρ (sel i) (d (sel i)) b)⟩

end YM.Integration.WilsonPhysicalLicensedSelection
end
