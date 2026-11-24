import YM.Integration.WilsonOriginalNectarRadius
import YM.Integration.WilsonThermometerIntrinsicRoster

/-! The true common marked posterior at every age, on the same deposited
single-source invoices including the individual old forced addresses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalIntrinsicInvoices
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open Push Marker RG05Readout Native Address Many Records Harvest Push.GridApprox Copper
open PhysicalNext.Repeat.Legato MergeProof Accent Motion Bandage
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetSource WilsonThermometerOwnOffsetField
open WilsonThermometerOwnOffsetTale WilsonThermometerOwnOffsetNectar WilsonThermometerOwnOffsetRadii
open Push.Local WilsonThermometerOffsetResidue
open scoped Classical BigOperators Topology
variable {G:Gauge} (R:Run G) {k N p:ℕ}
local notation "B" => WilsonThermometerOffsetLedger.cash R

def Received {I:Type} [Fintype I] [DecidableEq I] (d:I→ℕ) (z:I→Site (R.family.side N p))
    (y:(i:I)→Palette R.family (d i)) (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i))
    (names:Census I) (hk:k ≤ N) (t:ℕ) : Prop :=
  ∀ j (_:k ≤ j) (hn:j ≤ N),
    let P:=R.family.path.rep N p j
    let o:=WilsonThermometerOwnOffsetJoint.origins R z j
    ∃Q:(i:I) → Coefficient (R.family.labels.level (d i)) (R.family.side j p),
      (∀i, (Q i).Format (o i) R.family.params P ∧
        (Q i).remBound (o i) P (kappa R.family.path j) (radius R t k j)⁻¹ ∧
        invoice (Q i) (o i) (R.family.localSection (d i)) P=state (k:=k) R (V i) (r i) (y i) (z i) j) ∧
      Served P (fun i=>(Q i).exponentialEntry (o i) (R.family.localSection (d i)) P)
        (fun i=>profile P.activities (Q i).forced)
        (WilsonThermometerIntrinsicRoster.density R d z y r names hk hn) o
        (fun _=>radius R t k j) (topPitch R.family.path N j) 1

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (D:ℕ) :
    ∃t ≥ D+3, ∀ᶠ k:ℕ in atTop, ∀ p N (hk:k ≤ N) (I:Type) [Fintype I] [DecidableEq I]
      (d:I→ℕ) (_:∀i,d i ≤ D) (z:I→Site (R.family.side N p)),
      (∀i i':I,i≠i' → (R.family.path.levels.budget k).B^2 <
        separation (WilsonThermometerOwnOffsetJoint.origins R z k i)
          (WilsonThermometerOwnOffsetJoint.origins R z k i')) →
      ∃ (V:(i:I)→Sight R.family (d i) p) (r:(i:I)→Emblems R.family (d i)),
        (∀i, Enrolled R.makes R.doors B k N p (d i) (digits R N p (z i)) (V i) (r i)) ∧
        ∀(names:Census I) (y:(i:I)→Palette R.family (d i)), (∀i,size (y i) ≤ 1) →
          WilsonThermometerIntrinsicRoster.filed R d z y V r names hk t ∧ Received R d z y V r names hk t := by
  obtain ⟨t,large,available⟩:=WilsonThermometerIntrinsicRoster.original R simple shop D
  have paid:=Filter.eventually_all.mpr fun e:Fin (D+1)=>
    WilsonOriginalNectarRadius.original R simple shop e.val t (by omega)
  refine ⟨t,large,?_⟩
  filter_upwards [available,paid] with k course fees p N hk I fi di d bounded z clear
  obtain ⟨V,r,roster,book⟩:=course p N hk I d bounded z clear
  refine ⟨V,r,roster,?_⟩
  intro names y small
  have paper:=book names y small
  refine ⟨paper,?_⟩
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

end YM.Integration.WilsonOriginalIntrinsicInvoices
end
