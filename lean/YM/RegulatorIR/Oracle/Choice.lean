import YM.RegulatorIR.Oracle.Life

/-! Length purchase in advance. obtain from ordinary budgets *before* reading
calendar. No silently altering actual Family. -/
noncomputable section
set_option autoImplicit false
namespace YM.RegulatorIR.Oracle
open Function Finset Lattice Laurent Bloch Set Filter Budget Spatial Budget.Packet Budget.Tuple Budget.Layer Quadratic Quarry Sources Tree Tree.Forest PertExtension Geometry Geometry.Field
open Exterior RG Wilson Matrix Halo Profiles Push Precision Prim Clocks Series Series.Radial Series.Tested Diagram Diagram.Formal PowerSeries YM.RegulatorIR.Step YM.RegulatorIR.Ledger YM.RegulatorIR.Ledger.Sky Taping Uniform
open scoped Topology ENNReal NNReal BigOperators Classical Matrix Matrix.Norms.Frobenius PowerSeries
variable {X:Type} {M:X→ℕ} {n:Page M→Side} {K:KernelChoices} {k p:ℕ}{γ:ℝ}

lemma waits (G:Gauge) (Y:Program K) (k j:ℕ) (_h:0<γ)(hp:γ<1):∃ s:ℕ, ∀ L: Side, s ≤ L.val → pack_c G k (Y.receipt.α j) (Y.receipt.Ω j)*ENNReal.ofReal (((L.val:ℝ))⁻¹) ≤ ENNReal.ofReal ((((L.val:ℝ)^γ))⁻¹):=by
 let q:= pack_c G k (Y.receipt.α j) (Y.receipt.Ω j)
 let R:=q.toReal
 have hv : Tendsto (fun t:ℕ=> (t:ℝ)^(1-γ)) atTop atTop:= (tendsto_rpow_atTop (sub_pos.mpr hp)).comp tendsto_natCast_atTop_atTop
 obtain ⟨s,he⟩:= eventually_atTop.1 (hv.eventually (eventually_ge_atTop R)); refine ⟨s,fun L hk=>?_⟩
 let r:ℝ:=L.val;have hr:0<r:=by unfold r; positivity
 have hc: R*r⁻¹≤ (r^γ)⁻¹:=by rw [← div_eq_mul_inv, div_le_iff₀ hr, mul_comm, ← div_eq_mul_inv, ← Real.rpow_one r]; nth_rw 2 [Real.rpow_one]; exact (he L.val hk).trans_eq (Real.rpow_sub hr 1 γ)
 exact (ENNReal.ofReal_le_ofReal hc).trans_eq rfl|>.trans' (le_of_eq <| by rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (show q≠⊤ from pack_c_f _ _ _ _)])

namespace Program
variable (Y:Program K)(G:Gauge)(p:ℕ)(γ:ℝ)(h:0<γ)(hp:γ<1)

def floor_q (j:ℕ) := (waits G Y p j h hp).choose
variable (S:Circuit M n)(ht:∀ i:Flap M, Y.floor_q G p γ h hp (S.J i.prev)≤(S.sizeL i).val)
include ht
lemma insists (i:Flap M) : Circuit.leadA S Y G p i ≤ ENNReal.ofReal ((((S.sizeL i).val:ℝ)^γ)⁻¹):= (waits G Y p _ h hp).choose_spec (S.sizeL i) (ht i)
lemma min_one (i:Flap M) : Circuit.leadA S Y G p i ≤1:=by
 have hz:= Y.insists G p γ h hp S ht i; apply hz.trans; rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal; apply inv_le_one_of_one_le₀; apply Real.one_le_rpow; exact_mod_cast (S.sizeL i).property;exact h.le
end Program
end YM.RegulatorIR.Oracle
