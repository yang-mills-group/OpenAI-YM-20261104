import YM.Integration.WilsonOlderFreshConnectedEarning
import YM.Integration.WilsonMeasuredPointBareSlate
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedLamp
open Function Filter Finset MeasureTheory Lattice RG Precision Wilson Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology

open QuadraticLocal QuadraticLocal.Sunrise QuadraticLocal.Sunrise.Aviary QuadraticLocal.Poetry AllOrder AllOrder.Ink
open WilsonMeasuredPointBareSlate
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer.Rolls
variable {G:Gauge}{I:Type}{D:I → ℕ}{J:Finset I}{r:ℕ}

def lamp (P:Comet G (Pen D J) r)(v:Case D)(i:Stationary.Ink G r):Lantern G Unit:=
  ⟨r,scaled (touch v J (P.wage i)) (sprigB P i),[(0,())]⟩

theorem lawful (P:Comet G (Pen D J) r)(v:Case D)(i:Stationary.Ink G r):
    (lamp P v i).atom.Invariant:=
  WilsonMeasuredPointBareSlate.lawful (touch v J (P.wage i)) _ (sprigB_t P i)

theorem aperture (P:Comet G (Pen D J) r)(v:Case D)(i:Stationary.Ink G r){j l:ℕ}
    (h:r ≤ l+j):(lamp P v i).Bears {()} () (j+l+2):=by
  constructor
  · change r+1 ≤ j+l+2
    omega
  · intro x
    cases x
    simp [lamp,swallow,Focus.tally,Focus.calls]
  · simp [lamp]

theorem value (P:Comet G (Pen D J) r)(v:Case D)(i:Stationary.Ink G r)
    {n:Side}(U:Config G n)(o:Site n):
    (lamp P v i).atom.unmasked U o=touch v J (P.wage i)*(sprigB P i).unmasked U o:=
  WilsonMeasuredPointBareSlate.poly _ _ _

private theorem scaled_magnitude (c:ℝ)(p:Atom G r):(scaled c p).magnitude=|c| *p.magnitude:=by
  unfold Atom.magnitude
  change ∑b,|c*p.coeff b|=|c| *∑b,|p.coeff b|
  simp only [abs_mul,Finset.mul_sum]

theorem fee (P:Comet G (Pen D J) r)(v:Case D)(i:Stationary.Ink G r)(w:ℝ):
    (lamp P v i).money w=|touch v J (P.wage i)| *(sprigB P i).budget w:=by
  have len:(lamp P v i).length=(sprigB P i).length:=by
    change AllOrder.Ink.meter [(0,())]+(sprigB P i).length=_
    simp [AllOrder.Ink.meter,Laurent.size]
  change (scaled (touch v J (P.wage i)) (sprigB P i)).magnitude*Real.exp (w*(lamp P v i).length)=_
  rw [scaled_magnitude,len]
  unfold Atom.budget
  ring

theorem paid [Fintype I] (P:Comet G (Pen D J) r)(v:Case D)(μ:Stationary.Ink G r → Measure (Sky D))
    (born:Barn P μ)(w:ℝ):
    ∑i,(lamp P v i).money w ≤ (∏i∈J,‖v i‖)*lease P μ w:=by
  simp only [fee,lease,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have h:= (P.wage i).le_opNorm (seaMark v J)
  have small: ‖seaMark v J‖ ≤ ∏j∈J,‖v j‖:=folio_norm v
  have cost:|touch v J (P.wage i)| ≤ (∏j∈J,‖v j‖)*(μ i).real Set.univ:=by
    rw [(born i).2.2.1,mul_comm]
    exact h.trans (mul_le_mul_of_nonneg_left small (norm_nonneg _))
  rw [←mul_assoc]
  apply mul_le_mul_of_nonneg_right cost
  unfold Atom.budget Atom.magnitude
  positivity

end YM.Integration.WilsonOlderFreshConnectedLamp
end
