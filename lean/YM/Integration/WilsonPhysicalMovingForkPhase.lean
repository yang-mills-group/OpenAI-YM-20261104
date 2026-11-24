import YM.Integration.WilsonPhysicalDisplayedCapture
import YM.Integration.WilsonMovingForkShiftedSite
import YM.Integration.WilsonMovingForkCommonTranslation
import YM.Integration.WilsonMovingForkOpticalBook

/-! The unconditional moving-fork row may be shifted once, then heard at its licensed original flat. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalMovingForkPhase
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace
open GapsContact GapsContact.Seams GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)
open scoped Classical Topology BigOperators
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta


open WilsonMovingForkShiftedSite (Reached)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMovingForkOpticalBook (reporter)
include L in
theorem original {z:Trace.Terrace.Arch R.family}{D T:ℕ}{δ:ℝ}
    (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){J u:ℕ}(stop:Stop C 0 J u)
    (d:I→Fin (D+1)){n:ℕ}[Nonempty (Fin n)](sel:Fin n→I)
    (books:(r:{r:ℝ //0<r ∧ r<δ})→Book F (l:=l) H z D T r.val)(B q:ℕ):
    ∃gate:ℕ,∀ρ,let f:=reporter F books ρ
      ∀v c K:ℕ,gate≤c → u+2≤c → c+2≤f → a c/a f≤(β f)^B →
      ∀(fk:f≤K)(uv:u≤v)(vc:v≤c)(ck:c≤K),∀(site:Fin n→ Lattice.Cover)(translation:Lattice.Cover),
      let offered:=fun i=>site i+translation
      (∀i,8*‖(C).S.gridPoint f (offered i)‖≤a (c+1)) →
      (Pairwise fun i k=>2*a f*(((P).budget f).B:ℝ)^2≤‖(C).S.gridPoint f (offered i)-(C).S.gridPoint f (offered k)‖) →
      ∀weak:Fin n→Bool,∀x:∀i,S.Field (d (sel i)).val,
      let rows:=fun i=>(books (ρ (sel i))).rows (d (sel i))
      let arms:=fun i=>(rows i).arm (weak i) (x i)
      Reached arms fk uv vc ck site offered
        ((∏i,Motion.orbitCost ((C).labels.level (d (sel i)).val)*charge F (rows i) f (weak i) (x i))*((β f)^q)⁻¹):=by
  classical
  obtain ⟨gate,paid⟩:=eventually_atTop.mp (WilsonPhysicalDisplayedCapture.original F L simple slow stop
    (fun i=>(d (sel i)).val) B q)
  refine ⟨gate,?_⟩
  intro ρ f v c K gc uc cf ratio fk uv vc ck site translation offered inside apart weak x rows arms N per top
  let g:=fun i=>(d (sel i)).val
  let Y:=fun i=>(arms i).source (N,per)
  have cut:f≤N:=fk.trans top.le
  have pay:=paid f (gc.trans (by omega)) c uc cf ratio N per (fk.trans_lt top) offered inside apart
    rows (fun i=>(books (ρ (sel i))).checked) weak x
    (fun i=>WilsonMovingForkOpticalBook.station_le F books ρ (sel i) (d (sel i)) (weak i))
    (fun _=>(1,false)) (show u≤f by omega)
  dsimp only at pay
  have idle:(fun i=>displayed R (g i) (Y i) (1,false))=Y:=by
    funext i
    simp [displayed,show (1:Signed).ortho=1 from map_one Signed.inclusionO]
  change ‖gap R N per u _ (word R g f N per cut offered (fun i=>displayed R (g i) (Y i) (1,false)))‖≤_ at pay
  rw [idle] at pay
  change ‖(C).omega N per (word R g f N per cut site Y)-
    WilsonThermometerUnitFilingCoarse.reading R (N:=N) (credit (C) N per 0 (word R g f N per cut offered Y) u
      (uv.trans (vc.trans (ck.trans top.le)))) u le_rfl‖≤_
  rw [←WilsonMovingForkCommonTranslation.original R g cut site Y translation]
  exact pay

end YM.Integration.WilsonPhysicalMovingForkPhase
end
