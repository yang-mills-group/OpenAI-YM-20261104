import YM.Integration.WilsonIndependentRawRosterWord
import YM.Integration.WilsonIndependentRawWordGeometry

/-! The unamplified marked tensor has a rooted spatial salary on the actual
addresses of the whole finite roster. Each occurrence contributes one
displacement, including on the joint thermal and angular convolutions. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentRawRosterBudget
open Lattice RG Source Labels PertExtension XSpace XSpace.Rose
open RegulatorIR RegulatorIR.Halo RegulatorIR.Prim RegulatorIR.Geometry RegulatorIR.Gain
open RegulatorIR.Budget RegulatorIR.Budget.Packet RegulatorIR.Diagram
open RegulatorIR.Profiles RegulatorIR.Cluster RegulatorIR.Cluster.Collapsed
open RegulatorIR.Motion
open WilsonIndependentRawNamedStencil WilsonIndependentRawWordGeometry WilsonIndependentRawRosterWord
open scoped Classical ENNReal BigOperators

variable {G:Gauge}{I:Type}(R:PhysicalNext.Repeat.Legato.Run G)(W:Initialize G)
    (σ:I → Bool)(d:I → ℕ)(key:∀i,(R.family.labels.level (d i)).Index)
def charge : Composite I → ℕ → ℕ → ℕ → ℝ≥0∞
  | .atom i,u,j,r => markQ (root 0 u) (tensor R W (σ i) (d i) (key i) j r)
  | .pair l a,u,j,r =>
    ∑ b ∈ (_root_.Finset.HasAntidiagonal.antidiagonal j : Finset (ℕ×ℕ)),
      ∑ c ∈ (_root_.Finset.HasAntidiagonal.antidiagonal r : Finset (ℕ×ℕ)),
        charge l u b.1 c.1 * charge a u b.2 c.2

def travel (J:Composite I)(x:Room)(o:I → Cover)(u:ℕ):ℝ≥0∞:=
  fold (fun i=>displacement x (o i) u) J

def span (x:Room)(o:I → Cover):Composite I → ℝ
  | .atom i=>dist x (slide 1 (o i))
  | .pair l a=>span x o l + span x o a

theorem extent (x:Room)(o:I → Cover)(J:Composite I):0 ≤ span x o J:=by
  induction J with
  | atom _ => exact dist_nonneg
  | pair _ _ h h' => exact add_nonneg h h'

theorem housing (J:Composite I)(x:Room)(o:I → Cover)(u:ℕ):
    travel J x o u ≤ (ENNReal.ofReal (1+span x o J))^(J.accounts fun _=>u):=by
  induction J with
  | atom i => simp only [travel,fold,span,Composite.accounts,displacement,Tariff.amount,div_one,le_refl]
  | pair l a hl ha =>
    change travel l x o u*travel a x o u ≤ _^(_+_)
    apply (mul_le_mul' hl ha).trans
    rw [pow_add]
    apply mul_le_mul' <;> apply pow_le_pow_left' <;> apply ENNReal.ofReal_le_ofReal
    · change 1+span x o l ≤ 1+(span x o l+span x o a)
      linarith [extent x o a]
    · change 1+span x o a ≤ 1+(span x o l+span x o a)
      linarith [extent x o l]

local notation "salary" => charge R W σ d key
theorem finite (J:Composite I):∀u j r,salary J u j r ≠ ⊤:=by
  induction J with
  | atom i =>
    intro u j r
    exact WilsonIndependentRawWordGeometry.finite _ _
      ((stamp_symbol (authentic R W (σ i) (d i) (key i))).choose_spec.1.canopy j r)
  | pair l a hl ha =>
    intro u j r
    unfold charge
    apply ENNReal.sum_ne_top.mpr
    intro b _
    apply ENNReal.sum_ne_top.mpr
    intro c _
    exact ENNReal.mul_ne_top (hl u b.1 c.1) (ha u b.2 c.2)

theorem district_bound (J:Composite I)(x:Room)(o:I → Cover)(u:ℕ):∀j r,
    markQ (district x u) (bank R W σ d key J o j r) ≤ salary J u j r*travel J x o u:=by
  induction J with
  | atom i =>
    intro j r
    exact recenter x u (tensor R W (σ i) (d i) (key i) j r) (o i)
  | pair l a hl ha =>
    intro j r
    change markQ (district x u) (accord (bank R W σ d key l o) (bank R W σ d key a o) j r) ≤
      salary (.pair l a) u j r*(travel l x o u*travel a x o u)
    unfold accord charge
    apply (quota_sum ..).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro b _
    unfold crisp
    apply (quota_sum ..).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c hc
    rw [←_root_.Finset.HasAntidiagonal.mem_antidiagonal.mp hc,pie,dif_pos rfl]
    apply (packet_pair zero_lt_one u {x} (localL (G:=G) 1) _ _).trans
    apply (mul_le_mul' (hl b.1 c.1) (ha b.2 c.2)).trans_eq
    ring

theorem original (J:Composite I)(x:Room)(o:I → Cover)(u j r:ℕ):
    markQ (root x u) (bank R W σ d key J o j r) ≤
      salary J (u+u) j r*(ENNReal.ofReal (1+span x o J))^(J.accounts fun _=>u+u):=by
  exact (joined_root x u _).trans ((district_bound R W σ d key J x o (u+u) j r).trans
    (mul_le_mul_right (housing J x o (u+u)) _))

end YM.Integration.WilsonIndependentRawRosterBudget
