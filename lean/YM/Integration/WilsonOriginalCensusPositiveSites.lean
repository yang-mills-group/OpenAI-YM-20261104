import YM.Integration.WilsonOriginalCensusPhysicalUnits
import YM.Integration.WilsonOriginalCensusFaceSites

/-! One positive-grade census for all faces of a given physical roster, fixed before the original regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPositiveSites
open Function Finset Lattice Wilson RG Source Extraction Table Spec Marker QuadraticLocal
open Extra.Trajectories FVA1 RG05Readout.Records Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open OriginalForcedAddresses Push.GridApprox.Nil ActualRunUnmaskedPartners Kiosk
open WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonPositionThermometerDepositedFaces (leg pages)
open scoped Classical BigOperators
variable {I:Type}[DecidableEq I][Fintype I](k:I→ℕ)

abbrev Group:=Fin (Fintype.card {l:I // 0 < k l})

def pick:Group k ≃ {l:I // 0 < k l}:=(Fintype.equivFin _).symm

def names:Group k ↪ I:=(pick k).toEmbedding.trans (Embedding.subtype _)

omit [DecidableEq I] in
theorem positive (j:Group k):0 < k (names k j):=(pick k j).property

omit [DecidableEq I] in
theorem deep (s:Hot (Stock.census (Group k))):0 < mass (fun j=>k (names k j)) s.val.val:=by
  obtain ⟨i,has⟩:=s.property
  exact lt_of_lt_of_le (positive k i) (Finset.single_le_sum (s:=s.val.val) (f:=fun j=>k (names k j))
    (fun _ _=>Nat.zero_le _) has)

def part (s:(Replicum.Bud I).Mode):(Replicum.Bud (Group k)).Mode:=
  ⟨univ.filter (fun j=>names k j∈s.val),mem_univ _⟩

theorem mapped (s:(Replicum.Bud I).Mode):
    (part k s).val.map (names k)=s.val.filter (fun l=>k l≠0):=by
  classical
  ext l
  constructor
  · intro member
    obtain ⟨i,inside,rfl⟩:=mem_map.mp member
    exact mem_filter.mpr ⟨(mem_filter.mp inside).2,(positive k i).ne'⟩
  · intro member
    obtain ⟨inside,nonzero⟩:=mem_filter.mp member
    let i: {j:I // 0 < k j}:=⟨l,Nat.pos_of_ne_zero nonzero⟩
    let j:Group k:=(pick k).symm i
    have located:names k j=l:=congrArg Subtype.val ((pick k).apply_symm_apply i)
    exact mem_map.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,located ▸ inside⟩,located⟩

def sites {side:Side}(o:Positions I side):Positions (Group k) side:=
  ⟨fun j=>o.origin (names k j),fun j=>o.stub (names k j),fun j=>o.mem (names k j)⟩

variable {G:Gauge}(R:Run G)(simple:G.Simple){D N per:ℕ}
  (V:Vane R.family D)(grade:I→Fin (D+1))
  (v:∀l,(Bel R.family.book).Field (grade l))(o:Positions I (R.family.side N per))
local notation "d" => (fun l=>(grade l).val)
local notation "a" => names (d)
local notation "subgrade" => (fun j:Group (d)=>grade ((a) j))
local notation "subsource" => (fun j:Group (d)=>v ((a) j))
local notation "home" => sites (d) o

include simple in
theorem original (ref:∀l,R.family.ref (grade l) ≤ N){j:ℕ}(live:j ≤ N)(s:(Replicum.Bud I).Mode)
    (U:Config G (R.family.side j per)):
    (gust R.family.path N per N (pages R simple N per V grade v o) j live U).part s =
      (∏l∈s.val.filter (fun l=>(grade l).val=0),(V.wheel.atCut (N,per) (grade l) (v l)) 0)*
      (gust R.family.path N per N (pages R simple N per V (subgrade) (subsource) (home)) j live U).part (part (d) s):=by
  rw [WilsonOriginalCensusPhysicalUnits.original R simple V grade v o ref live s U]
  congr 1
  rw [WilsonPositionThermometerDepositedFaces.deposited R simple N per V grade v o ref live,
    WilsonPositionThermometerDepositedFaces.deposited R simple N per V (subgrade) (subsource) (home)
      (fun l=>ref ((a) l)) live]
  congr 2
  funext Z
  change (∏l∈s.val.filter (fun l=>(grade l).val≠0),leg R N per V grade v o l Z)=
    ∏i∈(part (d) s).val,leg R N per V grade v o ((a) i) Z
  rw [←mapped (d) s,prod_map]

end YM.Integration.WilsonOriginalCensusPositiveSites
end
