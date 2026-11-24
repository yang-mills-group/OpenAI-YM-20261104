import YM.Integration.WilsonPhysicalStationThermalPair
import YM.Integration.WilsonReporterWeightedOrdinary

/-! At each original cutoff, apply the thermal inverse independently
to the raw coordinate and to the section of the physical detector.
The observed and reference scalars use the same two named sites. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalVotes
open Function Filter Finset Lattice RG Wilson Cells Labels Source Next.Rank Next.Rank.East Next.Rank.Price
open MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open Further.CorrectedLift (ladder)
open WilsonPhysicalStationThermalPair (raw cell)
open Next.Rank Perch Atlas Edition Station PhysicalNext.InteractingRank Market
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D:ℕ}(A:Vane R.family D)(d:Fin (D+1)){N p:ℕ}
    (checked:A.checked f H D)(top:A.k<N)

def votes (x:R.family.label d)(z:(Bel R.family.book).Field d):Fin 2→R.family.label d:=
  ![x,ladder R.family d z]

def offered (x:R.family.label d)(z:(Bel R.family.book).Field d):Fin 2→R.family.label d:=
  ![raw R A d (p:=p) checked top x,A.wheel.atCut (N,p) d z]

theorem solves (x:R.family.label d)(z:(Bel R.family.book).Field d)(i:Fin 2):
    Price.Solves R.family (mag R.family.path.levels A.b A.k) d A.k N p (A.R N p d)
      (votes R d x z i) (offered R A d (p:=p) checked top x z i):=by
  fin_cases i
  · exact WilsonPhysicalStationThermalPair.solves R A d checked top _
  · have paid:=WilsonPhysicalStationThermalPair.solves R A d (p:=p) checked top (ladder R.family d z)
    rw [WilsonPhysicalStationThermalPair.lifted] at paid
    exact paid

theorem physical (j:ℕ)(o:Fin 2 → Cover)(x:R.family.label d)(z:(Bel R.family.book).Field d):
    R.family.numeric N p (q_asked (C:=R.family) (d:=fun _:Fin 2=>d.val) (offered R A d (p:=p) checked top x z))
      (fun i=>location R.family.S j N p (o i))=cell R A d (p:=p) checked top j o x z:=rfl

theorem reference (x:R.family.label d)(z:(Bel R.family.book).Field d)(y:Points 2):
    (standard R.family).useAt (standard R.family) y (jointX (d0:=fun _:Fin 2=>d.val) (votes R d x z))=
    (standard R.family).classMoment (standard R.family) (fun _:Fin 2=>d.val) y
      ![(standard R.family).project d x,z]:=by
  let table:=(standard R.family).classMoment (standard R.family) (fun _:Fin 2=>d.val) y
  have eq:(fun i:Fin 2=>(standard R.family).project d (votes R d x z i))=
      (![(standard R.family).project d x,z]:Fin 2→(standard R.family).Field d):=by
    funext i
    fin_cases i
    · rfl
    · exact Further.CorrectedLift.ladder_reads (C:=R.family) z
  exact congrArg (fun w=>table w) eq

end YM.Integration.WilsonPhysicalStationThermalVotes
end
