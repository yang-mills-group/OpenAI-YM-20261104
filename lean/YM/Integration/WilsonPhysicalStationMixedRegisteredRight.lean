import YM.Integration.WilsonPhysicalStationMixedBilledPort
/-! Right linear reads keep the complete deposited left field and the actual original two-site prior. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedRegisteredRight
open Function Filter Finset Lattice RG Wilson Labels Source Cells Extraction Table Climb Trace Trace.Pilot Next.UVStress
open MergeProof.East PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open Next.Rank.Edition (q_asked)
open WilsonOriginalBlissMixedGram (grades)
open WilsonPhysicalStationThermalPair (raw)
open WilsonPhysicalStationMixedWickPair (cell)
open scoped BigOperators Classical
open WilsonPhysicalStationMixedListener (pins value)
open WilsonPhysicalStationMixedWickTest (fields reference)
open WilsonPhysicalStationMixedBilledPort (base)
variable {G:Gauge}(R:Run G){h r:ℕ}

def wire (r N p j:ℕ)(o:Fin 2 → Lattice.Cover)(Y:R.family.label h):R.family.label r→ₗ[ℂ]ℂ:=
  (R.family.ensemble (N:=N) (p:=p) (grades h r) (fun i=>location R.family.S j N p (o i))).toLinearMap
    (pins R Y (0:R.family.label r)) 1
theorem actual (N p j:ℕ)(o:Fin 2 → Lattice.Cover)(Y:R.family.label h)(z:R.family.label r):
    wire R r N p j o Y z=WilsonPhysicalStationMixedListener.value R N p j o Y z:=by
  let M:=R.family.ensemble (N:=N) (p:=p) (grades h r) (fun i=>location R.family.S j N p (o i))
  change M (Function.update (pins R Y (0:R.family.label r)) 1 z)=M (pins R Y z)
  congr 1
  funext i
  fin_cases i <;> simp [Function.update,pins]

def registered {D:ℕ}(A:Vane R.family D)(dr:Fin (D+1))(N p j:ℕ)(o:Fin 2 → Lattice.Cover)(Y:R.family.label h):
    (standard R.family).Field dr→ₗ[ℂ]ℂ:=(wire R dr N p j o Y).comp (A.wheel.atCut (N,p) dr).toLinearMap
theorem reading {D:ℕ}(A:Vane R.family D)(dr:Fin (D+1))(N p j:ℕ)(o:Fin 2 → Lattice.Cover)(Y:R.family.label h)
    (z:(standard R.family).Field dr):
    registered R A dr N p j o Y z=WilsonPhysicalStationMixedListener.value R N p j o Y (A.wheel.atCut (N,p) dr z):=
  actual R N p j o Y _

def free (h r:ℕ)(x:Points 2)(a:(R.family.labels.level h).Index):(standard R.family).Field r→ₗ[ℂ]ℂ:=
  ((standard R.family).classMoment (standard R.family) (grades h r) x).toLinearMap
    (fields R.family (l:=h) (Pi.single a 1) (0:(standard R.family).Field r)) 1

theorem standing (x:Points 2)(a:(R.family.labels.level h).Index)(z:(standard R.family).Field r):
    free R h r x a z=base R h z x a:=by
  let M:=(standard R.family).classMoment (standard R.family) (grades h r) x
  let b:R.family.label h:=Pi.single a 1
  change M (Function.update (fields R.family b (0:(standard R.family).Field r)) 1 z)=M (fields R.family b z)
  congr 1
  funext i
  fin_cases i <;> simp [Function.update,fields]

end YM.Integration.WilsonPhysicalStationMixedRegisteredRight
end
