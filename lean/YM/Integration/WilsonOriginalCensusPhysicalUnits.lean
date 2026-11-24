import YM.Integration.WilsonPositionThermometerDepositedFaces
import YM.Integration.WilsonThermometerUnitFilingReflected

/-! Exact removal of all genuinely grade-zero original fields from any finite Wilson face. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalCensusPhysicalUnits
open Extra.Trajectories FVA1 RG05Readout.Records
open Set Function Filter Finset MeasureTheory Lattice Wilson RG Source Extraction Table Spec Marker
open Climb Trace.Pilot Next.Rank Next.UVStress PhysicalNext.Repeat.Legato
open MergeProof MergeProof.Accent MergeProof.East MergeProof.Replicums
open OriginalForcedAddresses Push.GridApprox.Nil ActualRunUnmaskedPartners WilsonPositionThermometerGradedBirth
open scoped Topology Classical BigOperators
open WilsonPositionThermometerDepositedFaces (pages leg)
open RG12
variable {G:Gauge}(R:Run G)(simple:G.Simple){N per:ℕ}

include simple in
theorem scalar (d:ℕ)(zero:d=0)(ref:R.family.ref d ≤ N)(field:R.family.label d)
    (site:Site (R.family.side N per))(U:Config G (R.family.side N per)):
    R.family.O N per field site U=field 0:=by
  subst d
  obtain ⟨c,eq⟩:=RG12.unit_spans simple R.family 0 (R.family.ref 0) (by decide) field
  rw [eq,(R.family.linearO N per 0 site).map_smul]
  have one:=R.family.constant R.makes 0 (p:=per) ref site
  change R.family.O N per (unitVec (R.family.labels.level 0) R.family.path (R.family.ref 0)) site=1 at one
  rw [one]
  simp [unitVec,Labels.Frame.e0]

theorem transported (f:Config G (R.family.side N per)→ℂ)(c:ℂ){i:ℕ}(live:i ≤ N)
    (U:Config G (R.family.side i per)):
    actualTransport R.family (N:=N) (fun Z=>c*f Z) live U=c*actualTransport R.family (N:=N) f live U:=by
  induction live using Nat.decreasingInduction with
  | self => rw [actualTransport_base R.family R.makes le_rfl,actualTransport_base R.family R.makes le_rfl]
  | of_succ l hl ih =>
    rw [actualTransport_step R.family R.makes le_rfl _ hl,actualTransport_step R.family R.makes le_rfl _ hl,
      show actualTransport R.family (N:=N) (fun Z=>c*f Z) hl=(fun W=>c*actualTransport R.family (N:=N) f hl W) from funext ih]
    exact actualAverage_complex_mul R.family _ c U

variable {I:Type}[DecidableEq I][Fintype I]{D:ℕ}(V:Vane R.family D)(j:I→Fin (D+1))
    (v:∀l,(Bel R.family.book).Field (j l))(o:Positions I (R.family.side N per))
local notation "J" => Replicum.Bud I
local notation "coef" => fun l:I=>(V.wheel.atCut (N,per) (j l) (v l)) 0
local notation "F" => leg R N per V j v o
local notation "book" => pages R simple N per V j v o

def active (s:(J).Mode):(J).Mode:=⟨s.val.filter (fun l=>(j l).val≠0),mem_univ _⟩

include simple in
theorem roster (ref:∀l,R.family.ref (j l) ≤ N)(s:(J).Mode)(U:Config G (R.family.side N per)):
    (∏l∈s.val,(F) l U)=(∏l∈s.val.filter (fun l=>(j l).val=0),(coef) l)*
      ∏l∈(active j s).val,(F) l U:=by
  rw [←prod_filter_mul_prod_filter_not s.val (fun l=>(j l).val=0) (fun l=>(F) l U)]
  apply congrArg (fun a:ℂ=>a*∏l∈(active j s).val,(F) l U)
  exact prod_congr rfl fun l hit=>scalar R simple _ (mem_filter.1 hit).2 (ref l) _ _ _

include simple in
theorem original (ref:∀l,R.family.ref (j l) ≤ N){i:ℕ}(live:i ≤ N)(s:(J).Mode)
    (U:Config G (R.family.side i per)):
    (gust R.family.path N per N (book) i live U).part s=
      (∏l∈s.val.filter (fun l=>(j l).val=0),(coef) l)*
        (gust R.family.path N per N (book) i live U).part (active j s):=by
  let c:=∏l∈s.val.filter (fun l=>(j l).val=0),(coef) l
  let f:=fun Y=>∏l∈(active j s).val,(F) l Y
  have peeled:(fun Y=>∏l∈s.val,(F) l Y)=fun Y=>c*f Y:=funext (roster R simple V j v o ref s)
  rw [WilsonPositionThermometerDepositedFaces.deposited R simple N per V j v o ref live s,
    WilsonPositionThermometerDepositedFaces.deposited R simple N per V j v o ref live (active j s)]
  change _ • actualTransport R.family (N:=N) (fun Y=>∏l∈s.val,(F) l Y) live U=
    c*(_ • actualTransport R.family (N:=N) f live U)
  rw [peeled,transported R f c live U,Complex.real_smul,Complex.real_smul]
  ring

end YM.Integration.WilsonOriginalCensusPhysicalUnits
end
