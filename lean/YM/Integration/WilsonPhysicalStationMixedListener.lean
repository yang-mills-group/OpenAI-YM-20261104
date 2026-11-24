import YM.Integration.WilsonPhysicalStationMixedWickPair
/-! The heterogeneous finite Wilson measurement as a linear function on the genuine left column. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedListener
open Function Filter Finset Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress
open MergeProof.East PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open Next.Rank.Edition (q_asked)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationMixedWickPair (cell)
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){h r:ℕ}
def pins (u:R.family.label h)(v:R.family.label r):R.family.book.Vector (grades h r):=
  Fin.cons (α:=fun i=>R.family.label (grades h r i)) u (fun _=>v)
def value (N p j:ℕ)(o:Fin 2 → Lattice.Cover)(u:R.family.label h)(v:R.family.label r):ℂ:=
  R.family.numeric N p (q_asked (C:=R.family) (d:=grades h r) (pins R u v))
    (fun i=>location R.family.S j N p (o i))
def port (h:ℕ)(N p j:ℕ)(o:Fin 2 → Lattice.Cover)(v:R.family.label r):R.family.label h→ₗ[ℂ]ℂ:=
  (R.family.ensemble (N:=N) (p:=p) (grades h r)
    (fun i=>location R.family.S j N p (o i))).toLinearMap (pins R (0:R.family.label h) v) 0

theorem actual (N p j:ℕ)(o:Fin 2 → Lattice.Cover)(u:R.family.label h)(v:R.family.label r):
    port R h N p j o v u=value R N p j o u v:=by
  let M:=R.family.ensemble (N:=N) (p:=p) (grades h r) (fun i=>location R.family.S j N p (o i))
  change M (Function.update (pins R (0:R.family.label h) v) 0 u)=M (pins R u v)
  congr 1
  funext i
  fin_cases i <;> simp [Function.update,pins]

variable {f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}{D N p:ℕ}(A:Vane R.family D)
    (d e:Fin (D+1))(ca:A.checked f H D)(top:A.k<N)(j:ℕ)(o:Fin 2 → Lattice.Cover)(z:(standard R.family).Field e)
theorem seated (u:R.family.label d):
    port R d N p j o (A.wheel.atCut (N,p) e z) (raw R A d (p:=p) ca top u)=
      cell R A d e (p:=p) ca top j o u z:=actual R N p j o _ _
end YM.Integration.WilsonPhysicalStationMixedListener
end
