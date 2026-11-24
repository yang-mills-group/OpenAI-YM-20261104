import YM.Integration.WilsonOriginalIntrinsicInvoices

/-! Native activity invoices on a previously selected mixed roster, without reselecting its teachers or signed chronology. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledIntrinsicInvoices
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Push Marker RG05Readout Native Address Many Records Harvest Push.GridApprox Copper
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetSource WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open Push.Local WilsonThermometerOffsetResidue
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {k N p:ℕ}
local notation "B" => WilsonThermometerOffsetLedger.cash R

open WilsonOriginalIntrinsicInvoices

theorem received (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D t:ℕ) (posit:1 ≤ t) :
    ∀ᶠ k:ℕ in atTop, ∀{p N:ℕ} {I:Type} [Fintype I] [DecidableEq I] (hk:k ≤ N)
      (d:I→ℕ) (_:∀i,d i ≤ D) (z:I→Site (R.family.side N p))
      (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i)),
      (∀i,Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i)) →
      ∀(names:Census I) (y:(i:I)→Palette R.family (d i)), (∀i,size (y i) ≤ 1) →
      WilsonThermometerIntrinsicRoster.filed R d z y V r names hk t →
      Received R d z y V r names hk t := by
  have all:=Filter.eventually_all.mpr fun e:Fin (D+1)=>
    WilsonOriginalNectarRadius.original R simple shop e.val t posit
  filter_upwards [all] with k fees p N I fi di hk d bounded z V r roster names y small paper
  intro j hj hn
  let o:=WilsonThermometerOwnOffsetJoint.origins R z j
  have at_site (i:I):o i=site R hn (z i):=by
    dsimp only [o,WilsonThermometerOwnOffsetJoint.origins,WilsonThermometerOwnOffsetNectar.location];rw [dif_pos hn]
  choose Q form fare read using fun i:I=>(fees ⟨d i, by have:=bounded i;omega⟩) hj hn (z i) (roster i) (y i) (small i)
  refine ⟨Q,fun i=>by rw [show WilsonThermometerOwnOffsetJoint.origins R z j i=site R hn (z i) from at_site i];exact ⟨form i,fare i,read i⟩,?_⟩
  have smooth (i:I): (Q i).exponentialEntry (o i) (R.family.localSection (d i)) (R.family.path.rep N p j)=
      (state (k:=k) R (V i) (r i) (y i) (z i) j).2.1 :=by
    rw [at_site];exact congrArg (fun x:Three G (R.family.side j p)=>x.2.1) (read i)
  have forced (i:I):profile (R.family.path.rep N p j).activities (Q i).forced=
      profile (R.family.path.rep N p j).activities
        (state (k:=k) R (V i) (r i) (y i) (z i) j).2.2 :=
    congrArg (profile (R.family.path.rep N p j).activities)
      (congrArg (fun x:Three G (R.family.side j p)=>x.2.2) (read i))
  rw [show (fun i=>(Q i).exponentialEntry (WilsonThermometerOwnOffsetJoint.origins R z j i)
      (R.family.localSection (d i)) (R.family.path.rep N p j))=_ from funext smooth,
    show (fun i=>profile (R.family.path.rep N p j).activities (Q i).forced)=_ from funext forced]
  exact (paper j hj hn).2.2

end YM.Integration.WilsonOriginalFiledIntrinsicInvoices
end
