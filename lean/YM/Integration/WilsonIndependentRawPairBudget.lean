import YM.Integration.WilsonIndependentRawNamedProduct
import YM.Integration.WilsonIndependentRawWordGeometry

/-! The total rooted moment of the submitted two-slot tensor has two
placement factors and finite, regulator-independent stencil expenses. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonIndependentRawPairBudget
open Lattice RG Source Labels PertExtension Orb XSpace XSpace.Rose XSpace.Cirrus
open RegulatorIR RegulatorIR.Halo RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Gain
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Cluster.Collapsed
open WilsonIndependentRawNamedProduct WilsonIndependentRawNamedStencil WilsonIndependentRawWordGeometry
open scoped Classical ENNReal BigOperators

variable {G:Gauge}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
variable (a c:Bool)(d e:ℕ)(b:(R.family.labels.level d).Index)(b':(R.family.labels.level e).Index)

def price (u i r:ℕ) : ℝ≥0∞ :=
  ∑j ∈ (_root_.Finset.HasAntidiagonal.antidiagonal i : Finset (ℕ×ℕ)),
    ∑ v ∈ (_root_.Finset.HasAntidiagonal.antidiagonal r : Finset (ℕ×ℕ)),
    markQ (root 0 (u+u)) (tensor R W a d b j.1 v.1) *
    markQ (root 0 (u+u)) (tensor R W c e b' j.2 v.2)

theorem paid (u i r:ℕ) : price R W a c d e b b' u i r≠⊤ := by
  unfold price
  apply ENNReal.sum_ne_top.mpr
  intro j _
  apply ENNReal.sum_ne_top.mpr
  intro v _
  apply ENNReal.mul_ne_top
  · exact WilsonIndependentRawWordGeometry.finite _ _
      ((stamp_symbol (authentic R W a d b)).choose_spec.1.canopy _ _)
  · exact WilsonIndependentRawWordGeometry.finite _ _
      ((stamp_symbol (authentic R W c e b')).choose_spec.1.canopy _ _)

def reach (x:Room)(o z:Cover)(u:ℕ) :=
  displacement x o (u+u)*displacement x z (u+u)

theorem original (u i r:ℕ)(o z:Cover)(x:Room) :
    markQ (root x u) (ranks R W a c d e b b' o z i r) ≤
      price R W a c d e b b' u i r * reach x o z u := by
  apply (joined_root x u _).trans
  unfold ranks accord price
  apply (quota_sum ..).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  unfold crisp
  apply (quota_sum ..).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro v hv
  have eqn:=_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hv
  rw [←eqn,pie,dif_pos rfl]
  apply (packet_pair zero_lt_one (u+u) {x} (localL (G:=G) 1) _ _).trans
  apply (mul_le_mul' (recenter x _ (tensor R W a d b j.1 v.1) o)
    (recenter x _ (tensor R W c e b' j.2 v.2) z)).trans_eq
  unfold reach
  ring

end YM.Integration.WilsonIndependentRawPairBudget
