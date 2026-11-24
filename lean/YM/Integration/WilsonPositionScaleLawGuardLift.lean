import YM.Integration.WilsonPositionScaleLawDressedGear
import YM.Integration.WilsonPositionScaleLawDressedTransport

/-! Publish the genuine guarded scale identity in the actual normed original
field space, including the original engineering dilations on both sides. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawGuardLift
open Function Filter Set Spec Table Extraction OPE OPE.Orbits Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize XSpace.Structure1 XSpace.Cirrus PhysicalNext.Repeat.Legato
open MS MS.Land MS.Fleet MS.Book.Program FVA2 FVA2.Register FVA2.Scale FVA2.Arrival PowerSeries
open WilsonPositionScaleLawHome (Ratio)
open WilsonPositionScaleLawGrade (lift reads)
open WilsonPositionScaleLawDressedGear (engine)
open WilsonPositionScaleLawIndependent (time)
open WilsonPositionScaleLawDressedTransport (adjust guard)
open scoped Topology Classical BigOperators
variable {G:Gauge}(C:Family G){d:ℕ}
set_option quotPrecheck false
local notation "E"=> (Bel C.book).Field

def act (d:ℕ):FieldEnd G d→ₐ[ℂ](E d→L[ℂ]E d) where
  toFun:=lift C
  map_zero':=by ext v;apply (fields C.labels d).injective;rw [reads];simp
  map_one':=by ext v;apply (fields C.labels d).injective;rw [reads];rfl
  map_add' a b:=by ext v;apply (fields C.labels d).injective;rw [reads];change _=fields C.labels d (lift C a v+lift C b v);rw [map_add,reads,reads];rfl
  map_mul' a b:=by ext v;apply (fields C.labels d).injective;rw [reads];change _=fields C.labels d (lift C a (lift C b v));rw [reads,reads];rfl
  commutes' z:=by ext v;apply (fields C.labels d).injective;rw [reads];change z • fields C.labels d v=fields C.labels d (z • v);rw [map_smul]

def pack (a:Guard G d):PowerSeries (E d→L[ℂ]E d):=PowerSeries.map (act C d).toRingHom a

theorem coefficient (a:Guard G d)(k:ℕ):coeff k (pack C a)=lift C (coeff k a):=by
  rw [pack,PowerSeries.coeff_map];rfl

theorem gear (t:Ratio):engine C d t=act C d (Level.Dial d (WilsonPositionScaleLawIndependent.time t)):=by
  ext v;apply (fields C.labels d).injective
  change fields C.labels d (Pert.Scale.gear C.labels d t.val v)=fields C.labels d (lift C _ v)
  rw [reads];exact WilsonPositionScaleLawUnits.original C.labels d t v

theorem transfer (t:Ratio)(A:FieldEnd G d):
    act C d A*engine C d t=engine C d t*act C d (Level.turner (WilsonPositionScaleLawIndependent.time t) A):=by
  rw [gear,←map_mul,←map_mul]
  exact congrArg (act C d) (Level.transfer (WilsonPositionScaleLawIndependent.time t) A)

variable (Z:WilsonPrescription G){hG:G.Simple}
    (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G)))
    {σ:Prescription (Press.portDeck G)}{b:Bool}(H:Main.Match Z hG M σ b)(ν:ℝ)

include H in
theorem original (t:Ratio)(d:ℕ):
    pack C (convertT (WilsonPositionScaleLawIndependent.time t) (adjust Z d))*pack C (WilsonPositionScaleLawDressedTransport.guard Z M ν (WilsonPositionScaleLawIndependent.time t) d)=
    pack C (GroupS.gaugeB Z.criterion M ν (WilsonPositionScaleLawIndependent.time t) d)*
      pack C (Reg.Point.stepV (GroupS.ψ Z.criterion M ν (WilsonPositionScaleLawIndependent.time t)) (adjust Z d)):=by
  have e:=congrArg (PowerSeries.map (act C d).toRingHom) (WilsonPositionScaleLawDressedTransport.published Z M H ν (WilsonPositionScaleLawIndependent.time t) d)
  simpa only [pack,map_mul] using e

end YM.Integration.WilsonPositionScaleLawGuardLift
