import YM.Integration.WilsonPhysicalStationTableJump
import YM.MergeProof.West.Latte
import YM.Next.RANK.ParticleGate

/-! Both original marked fields on a single thermal table. A raw coordinate
may be a free equation direction. Only the reflected detector is lifted
from the physical quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPhysicalStationThermalPair
open Function Filter Finset Lattice RG Wilson Cells Labels Source Next.Rank Next.Rank.East Next.Rank.Price
open MeasureTheory Extraction Table Climb Trace Trace.Pilot Next.UVStress MergeProof.East
open PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonPhysicalStationTableJump (table pair)
open Further.CorrectedLift (ladder)
open Atlas (Heating Heater wood)
open Next.Rank.Normal (exchange)
open scoped Classical Topology BigOperators
variable {G:Gauge}(R:Run G){f:Extraction.Order}{H:(Bel R.family.book).Hierarchy}
    {D:ℕ}(A:Vane R.family D)(d:Fin (D+1)){N p:ℕ}
    (checked:A.checked f H D)(top:A.k<N)
include checked top

def raw (x:R.family.label d):R.family.label d:=
  (table R A d (p:=p) checked top).symm ((R.family.labels.level d).scaled
    (shrink R.family A.k N p)⁻¹ (weightTag R.family d (Station.mag R.family.path.levels A.b A.k) x))

theorem solves (x:R.family.label d):Solves R.family (Station.mag R.family.path.levels A.b A.k) d
    A.k N p (A.R N p d) x (raw R A d (p:=p) checked top x):=by
  let F:=R.family.labels.level d
  let a:=shrink R.family A.k N p
  let v:=weightTag R.family d (Station.mag R.family.path.levels A.b A.k) x
  change F.scaled a ((table R A d (p:=p) checked top) ((table R A d (p:=p) checked top).symm (F.scaled a⁻¹ v)))=v
  rw [LinearEquiv.apply_symm_apply]
  exact F.scaled_inv (shrink_pos R.family R.makes top.le p).ne' v

theorem lifted (z:(Bel R.family.book).Field d):
    raw R A d (p:=p) checked top (ladder R.family d z)=A.wheel.atCut (N,p) d z:=
  (WilsonPhysicalStationTableJump.stamped R A d z checked top).symm

def cell (j:ℕ)(o:Fin 2 → Cover)(x:R.family.label d)(z:(Bel R.family.book).Field d):ℂ:=
  pair R d N p j o (raw R A d (p:=p) checked top x) (A.wheel.atCut (N,p) d z)

theorem honest (j:ℕ)(o:Fin 2 → Cover)(y z:(Bel R.family.book).Field d):
    cell R A d (p:=p) checked top j o (ladder R.family d y) z=
      pair R d N p j o (A.wheel.atCut (N,p) d y) (A.wheel.atCut (N,p) d z):=by
  unfold cell
  rw [lifted]

/-- On a heating receipt issued on this very table, the posted polynomial
trims to the full prescribed raw row at its own radius. -/
theorem trimmed (x:R.family.label d){degree cap:ℕ}(leCap:d.val≤cap)
    (M:Heater R.family A.k d)(ink:Heating R.family A.k N p d degree M (A.R N p d)):
    Rise.trim (exchange (Beamer.features cap (Subtype.val : Atlas.trimV (wood R.family.path.levels A.k) G→_)
      (Station.mag R.family.path.levels A.b A.k)) (M (raw R A d (p:=p) checked top x)))
        Configuration.bear d= MvPolynomial.rename Sum.inl (Configuration.thawKey (Labels.raiseLabel G leCap ((R.family.labels.level d).coords.symm x))):=by
  exact Perch.alignedX leCap _ _ (Station.mag_pos ..) (solves R A d checked top x) _ (ink.test _)

end YM.Integration.WilsonPhysicalStationThermalPair
end
