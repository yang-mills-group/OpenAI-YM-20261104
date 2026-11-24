import YM.Integration.WilsonPhysicalLicensedSelection
import YM.Integration.WilsonMeasuredPublicEntranceShiftedSites

/-! The original cell integral uses one common torus lift of every translated
proper face and its complete rotation before taking the signed expectation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalShiftedFacePhase
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

local notation "C₀" => R.family
local notation "a_" => R.family.S.a
local notation "β" => (C₀).path.levels.clock.hatBeta

open WilsonAddressedPhysicalCells WilsonPhysicalLicensedFaces
open PertExtension PertExtension.LatticePT
theorem original {D T n k:ℕ}(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{y:ℝ //0<y ∧ y<δ})→Book F (l:=l) H z D T s.val)
    (ρ:Fin n→{y:ℝ //0<y ∧ y<δ}){q u f c:ℕ}(s:(Stock.census (Fin n)).Mode)
    (cash:measured F d books ρ q u f c s)(φ:Test k)(scale:ℝ)
    (pick:Fin n→Fin k)(origin:Fin n→ Cover){width sep scope radius:ℝ}
    (support:∀x:Points k,φ x≠0→
      let center:=fun i=>(C₀).S.gridPoint f (origin i)+scale • x (pick i)
      (∀i,‖center i‖≤width*scope) ∧ Pairwise fun i j=>sep*radius≤‖center i-center j‖)
    (hmesh:4*(k:ℝ)*a_ f≤ scope)(distance:4*(k:ℝ)*a_ f≤(sep/4)*radius)
    (wall:8*((width+1)*scope)≤a_ (c+1))
    (aperture:2*a_ f*(((C₀).path.levels.budget f).B:ℝ)^2≤(sep/2)*radius)
    {N per:ℕ}(deep:f<N)(uf:u≤f)(weak:Fin n→Bool)(v:∀i,S.Field (d i).val)
    (turn:Sites ((C₀).side f per) k→Fin n→Motion)
    (cell:Sites ((C₀).side f per) k)(hit:mass φ (a_ f) scale ((C₀).side f per) cell≠0):
    let Y(i:Fin n):=(((books (ρ i)).rows (d i)).arm (weak i) (v i)).source (N,per)
    let raw:=physical R (fun i=>(d i).val) (N:=N) Y (turn cell)
      (fun i=>wrap ((C₀).side f per) (origin i)+cell (pick i)) s
    ‖(C₀).omega N per raw-actualTransport (C₀) (N:=N) raw (uf.trans deep.le) 1‖ ≤
      (∏i:↥s.val,Motion.orbitCost ((C₀).labels.level (d i).val)*
        charge F ((books (ρ i)).rows (d i)) f (weak i) (v i))*((β f)^q)⁻¹:=by
  classical
  obtain ⟨site,whereAt,fits⟩:=WilsonMeasuredPublicEntranceShiftedSites.original R φ (per:=per) scale pick origin support hmesh distance
  obtain ⟨inside,apart⟩:=fits cell hit
  have native:=cash N per deep (site cell) (fun i _=>(mul_le_mul_of_nonneg_left (inside i) (by norm_num : 0≤(8:ℝ))).trans wall)
    (fun {i j:↥s.val} ne=>aperture.trans (apart (fun h=>ne (Subtype.ext h)))) weak v (turn cell) uf
  have pos:(fun i=>wrap ((C₀).side f per) (site cell i))=(fun i=>wrap ((C₀).side f per) (origin i)+cell (pick i)):=whereAt cell
  dsimp only at native ⊢
  simpa only [pos] using native

end YM.Integration.WilsonPhysicalShiftedFacePhase
end
