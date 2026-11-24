import YM.Integration.WilsonThermometerOffsetPhysical
import YM.Push.RELAY_DIFFERENCE.Stencils

/-! Collapse the actual original pulls at all ages to one cutoff position.
The test follows the same digits and each engineering factor is retained. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerOffsetCylinder
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source RG12 Extra.Histories
open RG05Readout Native Address Many Records Harvest Push.GridApprox
open PhysicalNext.Repeat.Legato MergeProof Accent
open WilsonPositionSeparatedProfileCenteredBranch WilsonThermometerOffsetPhysical
open scoped Classical BigOperators
variable {G : Gauge} (R : Run G) (N p m : ℕ)
def address (sites : ∀ i,Bud R.family p i) :
    (q : ℕ) → m+q≤N → Site (R.family.side N p)
  | 0,_ => 0
  | q+1,live => address sites q (by omega) + anchor R.family.S p live (child R.family p (m+q) (sites _))

def test (sites : ∀ i,Bud R.family p i) : ℕ → Body → Body
  | 0,φ => φ
  | q+1,φ => headFee R.family p (m+q) (sites _) (test sites q φ)

def units (d : ℕ) : ℕ → ℂ
  | 0 => 1
  | q+1 => units d q*((R.family.S.block (m+q)).val:ℂ)^d

theorem single {d q : ℕ} (sites : ∀ i,Bud R.family p i) (live : m+q≤N)
    (F : Bin G (R.family.side N p)) (φ : Body) (U : Config G (R.family.side N p)) :
    route R N p m d sites q live F φ U = units R m d q *
      F (test R p m sites q φ) (Lattice.pull 1 (address R N p m sites q live) U) := by
  induction q generalizing F with
  | zero => simp only [WilsonThermometerOffsetPhysical.route,units,test,address,pull_id,one_mul]
  | succ q ih =>
    rw [WilsonThermometerOffsetPhysical.route,ih (by omega) _,units,test,address]
    unfold shift arrangement
    simp only [Pi.smul_apply,Function.comp_apply,smul_eq_mul,Lattice.pull_pull,
      mul_one,Lattice.affine,Signed.act_one]
    rw [add_comm (anchor R.family.S p live (child R.family p (m+q) (sites _)))
      (address R N p m sites q (by omega))]; exact (mul_assoc ..).symm

theorem bare {d q : ℕ} (sites : ∀ i,Bud R.family p i) (live : m+q≤N)
    (t : Letter d) (x : R.family.label (kept t)) (φ : Body) :
    route R N p m d sites q live (WilsonReportingUVReturn.raw R N p t x) φ =
      (units R m d q * (readJ t 0 (test R p m sites q φ)*(R.family.S.a N:ℂ)^(kept t))) •
        R.family.O N p x (address R N p m sites q live) := by
  let a := address R N p m sites q live
  funext U
  rw [single]
  change units R m d q * ((readJ t 0 (test R p m sites q φ) *
      (R.family.S.a N:ℂ)^(kept t)) * R.family.O N p x 0 (Lattice.pull 1 a U)) = _
  rw [Lattice.pull_one,R.family.translation]
  have shift0 : (0:Site (R.family.side N p))+a=a := zero_add a
  rw [shift0]
  exact (mul_assoc ..).symm

end YM.Integration.WilsonThermometerOffsetCylinder
end
