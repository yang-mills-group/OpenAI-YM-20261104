import YM.Integration.WilsonPhysicalDisplayedCapture
import YM.Integration.WilsonMeasuredPublicEntranceProperPhase

/-! One cutoff gate buys the Gibbs to fixed-flat comparison of every occupied
face of the original selected source family, with its actually filed rotations. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalLicensedFaces
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

def measured {D T n:ℕ}(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{y:ℝ //0<y ∧ y<δ})→Book F (l:=l) H z D T s.val)
    (ρ:Fin n→{y:ℝ //0<y ∧ y<δ})(q u f c:ℕ)(s:(Stock.census (Fin n)).Mode):Prop:=
  ∀N per:ℕ,∀deep:f<N,∀o:Fin n→ Cover,(∀i∈s.val,8*‖(C₀).S.gridPoint f (o i)‖≤a_ (c+1)) →
  (Pairwise fun i k:↥s.val=>2*a_ f*(((C₀).path.levels.budget f).B:ℝ)^2≤
    ‖(C₀).S.gridPoint f (o i.val)-(C₀).S.gridPoint f (o k.val)‖) →
  ∀weak:Fin n→Bool,∀v:∀i,S.Field (d i).val,∀turn:Fin n→Motion,∀uf:u≤f,
    let Y(i:Fin n):=(((books (ρ i)).rows (d i)).arm (weak i) (v i)).source (N,per)
    let raw:=physical R (fun i=>(d i).val) (N:=N) Y turn (fun i=>wrap ((C₀).side f per) (o i)) s
    ‖(C₀).omega N per raw-actualTransport (C₀) (N:=N) raw (uf.trans deep.le) 1‖ ≤
      (∏i:↥s.val, Motion.orbitCost ((C₀).labels.level (d i).val)*
        charge F ((books (ρ i)).rows (d i)) f (weak i) (v i))*((β f)^q)⁻¹

include L in
theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){J u:ℕ}
    (stop:Stop C₀ 0 J u){D T n:ℕ}(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{y:ℝ //0<y ∧ y<δ})→Book F (l:=l) H z D T s.val)(window q:ℕ):
    ∃gate:ℕ,∀ρ,let f:=reporter F books ρ
      ∀c:ℕ,gate≤c → u+2≤c → c+2≤f → a_ c/a_ f≤(β f)^window →
      ∀s:(Stock.census (Fin n)).Mode,s.val.Nonempty →measured F d books ρ q u f c s:=by
  classical
  let Sale (f:ℕ)(s:(Stock.census (Fin n)).Mode):Prop:=
    s.val.Nonempty →∀ρ,reporter F books ρ=f →∀c:ℕ,u+2≤c → c+2≤f →
      a_ c/a_ f≤(β f)^window →measured F d books ρ q u f c s
  have each (s:(Stock.census (Fin n)).Mode):∀ᶠf:ℕ in atTop,Sale f s:=by
    by_cases occupied:s.val.Nonempty
    · letI:Nonempty ↥s.val:=⟨⟨occupied.choose,occupied.choose_spec⟩⟩
      filter_upwards [WilsonPhysicalDisplayedCapture.original F L simple slow stop
        (fun i:↥s.val=>(d i).val) window q] with f paid
      intro _ ρ tied c uc cf room N per deep o inside apart weak v turn uf
      have cost:=paid c uc cf room N per deep (fun i=>o i.val) (fun i=>inside i.val i.2) apart
        (fun i=> (books (ρ i.val)).rows (d i.val)) (fun i=>(books (ρ i.val)).checked)
        (fun i=>weak i.val) (fun i=>v i.val)
        (fun i=>tied ▸ WilsonMovingForkOpticalBook.station_le F books ρ i.val (d i.val) (weak i.val))
        (fun i=>turn i.val) uf
      dsimp only at cost
      rw [←WilsonMeasuredPublicEntranceProperPhase.word_at R (fun i=>(d i).val) deep.le s o
        (fun i=>(((books (ρ i)).rows (d i)).arm (weak i) (v i)).source (N,per)) turn,
        WilsonMeasuredPublicEntranceProperPhase.actual] at cost
      exact cost
    · exact Eventually.of_forall fun _ h=>False.elim (occupied h)
  obtain ⟨gate,all⟩:=eventually_atTop.mp (eventually_all.mpr each)
  refine ⟨gate,?_⟩
  intro ρ
  dsimp only
  intro c gc uc cf room s occupied
  exact all _ (gc.trans (by omega)) s occupied ρ rfl c uc cf room

end YM.Integration.WilsonPhysicalLicensedFaces
end
