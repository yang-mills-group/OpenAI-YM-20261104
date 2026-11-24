import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShieldedKineticBill
import YM.Integration.FVA1Physical.Exchange.CovarianceExpansionShieldedAtomBank

/-! The entire geometric/action part of the original beforeSign-minus-
independent compensation on a locally cold physical bond. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
namespace YM.Integration.FVA1Physical.Exchange.ShieldedAction
open Finset Lattice RG Wilson Precision Push.Local WilsonStartup UVNext.PricedKernels
open scoped Classical BigOperators
variable {G:Gauge}{n:Side}
local notation "Fld" => Config G n

/-- Signed action in the original and independent conventions, without
the separately filed passenger/plan action. This is the full path action. -/
def pathMask (P:PathData G)(c:Clip)(p:BudgetPoint)(β:ℝ)(U:Fld):ℝ:=
  P.inChannels c p β U-(β*mainTerm c P U+Precision.loop P U)

def pathCash (σ C Λ β:ℝ)(D:ℕ):ℝ:=
  |β| * (8*C^2*(Fintype.card PlaqAxes:ℝ)*Real.exp (-(σ/2)*(D:ℝ))*basin (σ/2)+
    atomCash 3 σ C D+atomCash 4 σ C D)+atomCash 2 σ Λ D

private def oneChannel (P:PathData G)(c:Clip)(p:BudgetPoint)(β:ℝ)(U:Fld):ℝ:=
  β*(quadraticMask P c p U+atomMask P.cubic p U+atomMask P.quartic p U)+atomMask P.loop p U

private theorem all_channels (P:PathData G)(c:Clip)(p:BudgetPoint)(β:ℝ)(U:Fld):
    pathMask P c p β U=(Fintype.card Signed:ℝ)⁻¹*∑s:Signed,oneChannel P c p β (pull s 0 U):=by
  have algebra(W:Fld):oneChannel P c p β W=P.principal c p β W-
      β*(quadratic c P W+uncut P.cubic W+uncut P.quartic W)-uncut P.loop W:=by
    simp only [oneChannel,quadraticMask,atomMask,PathData.principal,Finset.sum_add_distrib]
    ring
  simp only [pathMask,mainTerm,Precision.loop,Patch.average,PathData.inChannels,algebra,
    Finset.sum_sub_distrib,←Finset.mul_sum]
  ring

/-- Original masked action versus the same independent numerical Wilson
geometry. True physical beta, arbitrarily many distant failures, every
path and orientation and an all-center sum independent of the volume. -/
theorem original_path_mask_price (p:BudgetPoint)(c:Clip)(P:PathData G){σ C Λ:ℝ}
    (pay:P.Bounds c σ C Λ)(licensed:Decent c p)(β:ℝ)(e:Edge (Site n))(D:ℕ)(U V:Fld)
    (same:∀b:Edge (Site n),b≠e → U b=V b)
    (cold:Healthy p.threshold (halo (D+p.B) {e.1}) U)(after:e.1∉flags p.threshold V):
    |pathMask P c p β U-pathMask P c p β V|≤pathCash σ C Λ β D:=by
  have bank:Healthy p.threshold (halo D {e.1}) U:=by
    apply disjoint_left.mpr;intro x hx hot
    obtain ⟨y,hy,near⟩:=halo_spec.mp hx
    exact disjoint_left.mp cold (halo_spec.mpr ⟨y,hy,near.trans (Nat.le_add_right ..)⟩) hot
  have one(s:Signed):|oneChannel P c p β (pull s 0 U)-oneChannel P c p β (pull s 0 V)|≤pathCash σ C Λ β D:=by
    let U':=pull s 0 U;let V':=pull s 0 V
    let Q:=quadraticMask P c p U'-quadraticMask P c p V'
    let X:=atomMask P.cubic p U'-atomMask P.cubic p V'
    let Y:=atomMask P.quartic p U'-atomMask P.quartic p V'
    let Z:=atomMask P.loop p U'-atomMask P.loop p V'
    have q:=original_quadratic_mask_price p c P pay licensed e D U V same cold after s
    have x:=original_atom_mask_price P.cubic pay.width pay.three p e D U V same bank after s
    have y:=original_atom_mask_price P.quartic pay.width pay.four p e D U V same bank after s
    have z:=original_atom_mask_price P.loop pay.width pay.two p e D U V same bank after s
    have eq:oneChannel P c p β U'-oneChannel P c p β V'=β*(Q+X+Y)+Z:=by dsimp only [oneChannel,Q,X,Y,Z];ring
    rw [eq]
    exact (abs_add_le ..).trans (add_le_add
      ((abs_mul ..).le.trans (mul_le_mul_of_nonneg_left
        ((abs_add_le ..).trans (add_le_add ((abs_add_le ..).trans (add_le_add q x)) y)) (abs_nonneg _))) z)
  let K:=Fintype.card Signed
  have pos:(0:ℝ)<K:=Nat.cast_pos.mpr Fintype.card_pos
  rw [all_channels,all_channels,←mul_sub,←Finset.sum_sub_distrib,abs_mul,abs_of_nonneg (inv_nonneg.mpr pos.le)]
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs ..) (inv_nonneg.mpr pos.le)).trans
  have costs:=Finset.sum_le_sum (s:=Finset.univ) (fun s _=>one s)
  simp only [sum_const,card_univ,nsmul_eq_mul] at costs
  exact (mul_le_mul_of_nonneg_left costs (inv_nonneg.mpr pos.le)).trans_eq (inv_mul_cancel_left₀ pos.ne' _)

end YM.Integration.FVA1Physical.Exchange.ShieldedAction
