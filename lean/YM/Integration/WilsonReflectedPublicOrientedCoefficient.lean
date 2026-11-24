import YM.Integration.WilsonReflectedPublicOpticalJoint
import YM.MergeProof.Cashew
import YM.Integration.WilsonThermometerWeakReflectedRows
/-! The actual reflected/translated physical one-mark coefficient on a named
keyed gallery, with separate true regular and mandatory source incomes. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicOrientedCoefficient
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open scoped Topology BigOperators Classical
variable {G:Gauge}{d:ℕ}{n:Side}{F:Frame G d}{P:Rep G n}{S:SectionData F}{A:Hol G}

theorem posted (s:Motion) (t:Site n) (π:P.activities.Moves s.1 t) (Q:Coefficient F n)
    (hn:2≤n.val) (sound:S.Sound A) (format:Q.Format 0 A P) {κ cost:ℝ}
    (budget:Q.remBound 0 P κ cost) {Z:Three G n}
    (read:View.Signpost P s t (invoice Q 0 S P) Z) :
    let q:=audition (z:=s) π Q
    q.Format t A P ∧ q.x=Motion.patch F s Q.x ∧
    (∃a b, a+b≤cost ∧ Tab q t P κ (turnCost P.p.order P.p.power*a) b) ∧
    q.remBound t P κ (turnCost P.p.order P.p.power*cost) ∧
    Z.2.1=q.exponentialEntry t S P ∧ profile P.activities Z.2.2=profile P.activities q.forced ∧
    q.density t S P=Z.1 := by
  intro q
  obtain ⟨a,b,raw,cap⟩:=rem_tabs.mp budget
  have turned:=audition_turn s t π hn sound format raw
  have moved:affine s.1 t (0:Site n)=t:=by simp [affine]
  dsimp only at turned
  rw [moved] at turned
  have slope:1≤turnCost P.p.order P.p.power :=
    one_le_pow₀ (one_le_mul_of_one_le_of_one_le one_le_two (one_le_pow₀ one_le_two))
  have bill:turnCost P.p.order P.p.power*a+b ≤ turnCost P.p.order P.p.power*cost := by
    calc
      _ ≤ turnCost P.p.order P.p.power*a+turnCost P.p.order P.p.power*b :=
        add_le_add_right (le_mul_of_one_le_left raw.second slope) _
      _ = turnCost P.p.order P.p.power*(a+b) := (mul_add ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left cap (zero_le_one.trans slope)
  refine ⟨turned.1,?_,⟨a,b,cap,turned.2.1⟩,turned.2.1.bound bill,?_,?_,?_⟩
  · unfold q audition Motion.patch
    split <;> rfl
  · rw [read.gate]
    exact (moved ▸ bow (o:=0) s Q t sound π).symm
  · rw [read.lens]
    exact (foyer s t π Q).symm
  · exact turned.2.2.trans read.trade.symm

variable (R:Run G) {N p k:ℕ}
local notation "Z₀" => R.family.path.rep N p k
local notation "B₀" => WilsonThermometerOffsetLedger.cash R

theorem original {V:Sight R.family d p}{r:Emblems R.family d}
    (z:Site (R.family.side N p)) (s:Motion) (c:Site (R.family.side k p)) (hk:k≤N)
    (y:Palette R.family d) (enrolled:Enrolled R.makes R.doors B₀ k N p d (digits R N p z) V r):
    let o:=point R z s c k
    let Z:=marked R z s c V r y k
    let κ:=kappa R.family.path k
    let τ:=turnCost (Z₀).p.order (Z₀).p.power
    ∃ q : Coefficient (R.family.labels.level d) (R.family.side k p),
      q.Format o R.family.params (Z₀) ∧
      (∃a b:ℝ,a+b≤B₀ d k*size y ∧ Tab q o (Z₀) κ (τ*a) b) ∧
      q.remBound o (Z₀) κ (τ*(B₀ d k*size y)) ∧ Z.2.1=q.exponentialEntry o (R.family.localSection d) (Z₀) ∧
      profile (Z₀).activities Z.2.2=profile (Z₀).activities q.forced ∧
      q.density o (R.family.localSection d) (Z₀)=Z.1 := by
  intro o Z κ τ
  obtain ⟨X,fmt,fee,_,_,read⟩:=WilsonThermometerWeakReflectedRows.master R z hk y enrolled
  let π:=Classical.choice ((R.makes.wilson.represents N p k hk).good.labels.moves s.1 o)
  have hn:2≤(R.family.side k p).val := (by decide : 2≤4).trans (Next.Foundations.actual_side_ge R.family.S k p)
  have paid:=posted s o π X hn (R.makes.sections d) fmt fee (read s c)
  exact ⟨_,paid.1,paid.2.2⟩

end YM.Integration.WilsonReflectedPublicOrientedCoefficient
end
