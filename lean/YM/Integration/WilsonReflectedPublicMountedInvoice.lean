import YM.Integration.WilsonReflectedPublicPrimaryFare
import YM.Integration.WilsonReflectedPublicRotationFare
/-! Uniform funded native receipts at both incident roots of an actual
reflected public conditional. Each admitted normalized cutoff vector retains
its own group-field value, primary and compulsory hard inventory. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicMountedInvoice
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Trace.Physical.Germ
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open scoped Topology BigOperators Classical
open WilsonAddressedAlignedColumn
variable {G:Gauge}(R:Run G)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
local notation "C₀" => R.family
local notation "B₀" => WilsonThermometerOffsetLedger.cash R

def wage (f:ℕ):ℝ:=1+Real.log (2+Real.log (R.alloy.B.a.clock.hatBeta f))

include simple shop in
theorem original (d:ℕ):∀ᶠ f in atTop,∀{N p} (hf:f≤N)
    {V:Sight C₀ d p}{r:Emblems C₀ d} (home:Opened C₀ d f p)
    (_enrolled:Enrolled R.makes R.doors B₀ f N p d (digits R N p 0) V r)
    (y:(C₀).label d) (s:Motion) (c:Site ((C₀).side f p)),
    let P:=(C₀).path.rep N p f
    let x:=reduce (offer R y home hf)
    let field:=marked R (N:=N) 0 s c V r x f
    ∃q:Coefficient ((C₀).labels.level d) ((C₀).side f p),
      q.Format c (C₀).params P ∧
      ((C₀).labels.level d).coeffSize q.x≤orbitCost ((C₀).labels.level d)*(1+wage R f) ∧
      q.remBound c P (kappa (C₀).path f) (wage R f) ∧
      field.2.1=q.exponentialEntry c ((C₀).localSection d) P ∧
      profile P.activities field.2.2=profile P.activities q.forced ∧
      q.density c ((C₀).localSection d) P=field.1 :=by
  filter_upwards [WilsonReflectedPublicRotationFare.original R simple shop d,
    WilsonThermometerOffsetLedger.original R simple shop d] with f rot native
  intro N p hf V r home enrolled y s c P x field
  have pos:0≤B₀ d f:=zero_le_one.trans native.2.1
  have norm:size x≤1:=small _
  obtain ⟨q,fmt,head,_,wallet,bright,forced,total⟩:=
    WilsonReflectedPublicPrimaryFare.original R 0 s c hf home x enrolled
  rw [WilsonReflectedPublicOpticalJoint.location R hf s c] at fmt wallet bright total
  refine ⟨q,fmt,head.trans ?_,rem_mono wallet ?_,bright,forced,total⟩
  · have cost:=mul_nonneg (zero_le_one.trans (orbitCost_one_le ((C₀).labels.level d))) (by linarith : 0≤1+B₀ d f)
    exact (mul_le_of_le_one_right cost norm).trans (mul_le_mul_of_nonneg_left
      (add_le_add_right native.2.2 1) (zero_le_one.trans (orbitCost_one_le ((C₀).labels.level d))))
  · have one:1≤turnCost P.p.order P.p.power:=shift_pays (R:=P)
    rw [←mul_assoc]
    exact (mul_le_of_le_one_right (mul_nonneg (zero_le_one.trans one) pos) norm).trans (rot N p hf)

end YM.Integration.WilsonReflectedPublicMountedInvoice
end
