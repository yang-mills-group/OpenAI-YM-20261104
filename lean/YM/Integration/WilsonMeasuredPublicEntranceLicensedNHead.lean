import YM.Integration.WilsonPhysicalShiftedLicensedHead
import YM.Integration.WilsonMeasuredPublicEntranceGibbsProfile
import YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing
import YM.Integration.WilsonPhysicalLicensedMaster
import YM.Integration.WilsonMeasuredPublicEntranceProfileMesh

/-! Transfer all the actual occupied cells of a fixed joint test under one
optical bed, for heterogeneous public homes and their single preselected roster. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceLicensedNHead
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

variable {lo wid teach}(L:Package R.family wid lo teach)
local notation "C₀" => R.family
local notation "a_" => R.family.S.a
local notation "β" => (C₀).path.levels.clock.hatBeta

open WilsonAddressedPhysicalCells WilsonPhysicalLicensedFaces
open PertExtension PertExtension.LatticePT
open WilsonThermometerUnitFilingFourPoolClock (outer)
open WilsonPositionProgramReporterBand (Band)
open Pert.Asymptotics PhysMS

open WilsonMeasuredPublicEntranceProfileRegistry (Billed)
open WilsonPhysicalShiftedLicensedHead (receipt)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted difference)
variable {D T n k:ℕ}(d:Fin n→Fin (D+1)){δ:ℝ}
    (books:(s:{y:ℝ //0<y ∧ y<δ})→Book F (l:=l) H z D T s.val)
    (ρ:Fin n→{y:ℝ //0<y ∧ y<δ}){q u f:ℕ}(s:(Stock.census (Fin n)).Mode){width sep r scope:ℝ}

theorem original {J:Type}[Fintype J](paid:receipt (k:=k) F d books ρ q u f s width sep r scope)
    (φ:Test k)(scale:ℝ)(pick:Fin n→Fin k)(origin:Fin n→ Cover)
    (layout:∀x:Points k,φ x≠0→let center:=fun i=>(C₀).S.gridPoint f (origin i)+scale • x (pick i)
      (∀i,‖center i‖≤width*scope) ∧ Pairwise fun i j=>sep*r≤‖center i-center j‖)
    {N per K:ℕ}(deep:f<N)(uf:u≤f)(fk:f≤K)(live:K≤N)(weak:J→Fin n→Bool)(v:J→∀i,S.Field (d i).val)
    (turn:J→Sites ((C₀).side f per) k→Fin n→Motion)(amp:J→ℂ)
    (file:J→Filed R (fun i=>(d i).val) K)(rate:ℝ):
    let Y:=fun b i=>(((books (ρ i)).rows (d i)).arm (weak b i) (v b i)).source (N,per)
    let loc:=fun (c:Sites ((C₀).side f per) k) i=>wrap ((C₀).side f per) (origin i)+c (pick i)
    let raw:=fun b c=>physical R (fun i=>(d i).val) (N:=N) (Y b) (turn b c) (loc c) s
    let posted:=fun b c=>submitted R (fun i=>(d i).val) (N:=N) (file b) fk (Y b) (turn b c) (loc c) s
    let next:=fun b c=>actualTransport (C₀) (N:=N) (posted b c) (uf.trans fk) 1
    let bill:=fun b=>(∏i:↥s.val,Motion.orbitCost ((C₀).labels.level (d i).val)*
      charge F ((books (ρ i)).rows (d i)) f (weak b i) (v b i))*((β f)^q)⁻¹
    Billed φ (a_ f) scale ((C₀).side f per) (fun c=>∑b,amp b*
      difference R (fun i=>(d i).val) (file b) fk live (uf.trans fk) (Y b) (turn b c) (loc c) s) rate →
    Billed φ (a_ f) scale ((C₀).side f per) (fun c=>∑b,amp b*((C₀).omega N per (raw b c)-next b c))
      ((∑b,‖amp b‖*bill b)+rate):=by
  classical
  intro Y loc raw posted next bill earned
  let earlier:=fun b c=>actualTransport (C₀) (N:=N) (raw b c) (uf.trans deep.le) 1
  have paidField(b c):difference R (fun i=>(d i).val) (file b) fk live (uf.trans fk) (Y b) (turn b c) (loc c) s=
      earlier b c-next b c:=WilsonMeasuredPublicEntranceCutoffHearing.original R (fun i=>(d i).val) (file b) fk live
        (uf.trans fk) (Y b) (turn b c) (loc c) s
  have cut:Billed φ (a_ f) scale ((C₀).side f per) (fun c=>∑b,amp b*(earlier b c-next b c)) rate:=by
    simpa only [paidField] using earned
  let gap:=fun b c=>(C₀).omega N per (raw b c)-earlier b c
  have phase(b):Billed φ (a_ f) scale ((C₀).side f per) (gap b) (bill b):=by
    refine ⟨WilsonSeparatedPrefixCellProfile.tested _ _ _ _ ((C₀).S.a_pos f) _,?_⟩
    apply WilsonSeparatedPrefixCellProfile.priced _ _ _ _ ((C₀).S.a_pos f) _ (bill b)
    · apply mul_nonneg (Finset.prod_nonneg _) (inv_nonneg.mpr (pow_nonneg (zero_lt_one.trans (R.alloy.B.a.fits.delayed f)).le q))
      intro i _
      exact mul_nonneg (zero_le_one.trans (Motion.orbitCost_one_le _)) (zero_le_one.trans (le_max_left _ _))
    · exact paid φ scale pick origin layout N per deep uf (weak b) (v b) (turn b)
  have fee:=WilsonMeasuredPublicEntranceJointBilled.original φ (a_ f) scale ((C₀).side f per) ((C₀).S.a_pos f) amp gap bill phase
  have joined:=WilsonMeasuredPublicEntranceGibbsProfile.add φ (a_ f) scale ((C₀).S.a_pos f) _ _ fee cut
  have combine(c):(∑b,amp b*gap b c)+(∑b,amp b*(earlier b c-next b c))=∑b,amp b*((C₀).omega N per (raw b c)-next b c):=by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _=>by dsimp [gap];ring
  simpa only [combine] using joined

end YM.Integration.WilsonMeasuredPublicEntranceLicensedNHead
end
