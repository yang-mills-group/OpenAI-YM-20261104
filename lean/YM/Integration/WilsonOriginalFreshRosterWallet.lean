import YM.Integration.WilsonThermometerRaisedRoster
import YM.Integration.WilsonOriginalThreeCompactWallet

/-! Complete finite-census marked logs, with their actual nonempty modes
and one original unmasking expenditure at the submission date. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFreshRosterWallet
open Finset Lattice Laurent RG Wilson Marker
open Push Push.AbsoluteSums QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Mentor ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge} {n:Side} {V I X:Type} [Fintype V] [DecidableEq V]
    {o:Passport n V} (M:I→Row o (Stock.census V) G X) (base:V→ℝ) (d:V→ℕ)

theorem original (B:BudgetPoint) {g U σ ξ C Ω:ℝ} {order seats shelf:ℕ}
    (stock:Scene.Armada M base d σ C order seats shelf) (cp:0 ≤ C) (op:0 < Ω)
    (fund:Invoice.Supports B U (B.supportExponent+1) g σ ξ) :
    let D:=(∑v:V,d v)+1
    let fee:=WilsonOriginalThreeCompactWallet.fee G B U g ξ order seats shelf D
    let size:=max 1 C
    let raw:=Stoop.radius base size
    let shrink:=max 1 Ω + |fee|/Willow.haloSlack B.B
    let w:=Stoop.radius raw shrink
    let b:=shrink⁻¹*(size⁻¹*C)
    (∀v,0 < raw v) ∧ 1 ≤ shrink ∧ b ≤ 1 ∧ b ≤ Ω⁻¹ ∧
      Scene.Armada M w d σ b order seats shelf ∧
      WilsonRootedKioskOccupiedSlip.Gross (rendered M B g) raw B.B (B.supportExponent+1)
        (fee*(size⁻¹*C)) ∧ shrink⁻¹*(fee*(size⁻¹*C)) ≤ Willow.haloSlack B.B ∧
      ∀v,(w v)⁻¹=(base v)⁻¹*size*(max 1 Ω + |fee|/Willow.haloSlack B.B) := by
  intro D fee size raw shrink w b
  have sp:0 < size:=zero_lt_one.trans_le (le_max_left ..)
  have hp:0 < Willow.haloSlack B.B:=Willow.spare_pos _
  have rp:1 ≤ shrink:=(le_max_left 1 Ω).trans (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hp.le))
  have r0:0 < shrink:=zero_lt_one.trans_le rp
  have cap:size⁻¹*C ≤ 1:=by
    rw [←div_eq_inv_mul]
    exact (div_le_one sp).mpr (le_max_right ..)
  have b0:b ≤ shrink⁻¹:=by simpa only [mul_one] using mul_le_mul_of_nonneg_left cap (inv_nonneg.mpr r0.le)
  have scene:=WilsonThermometerRaisedRoster.salary M stock (le_refl order) (le_max_left 1 C)
  have hard:=WilsonMarkedFixedPoleGross.landed M raw d B scene fund D (fun s=>Nat.succ_le_succ
    (sum_le_sum_of_subset_of_nonneg (f:=d) (subset_univ _) (fun _ _ _=>Nat.zero_le _)))
  have rr:=WilsonThermometerRaisedRoster.salary M scene (le_refl order) rp
  have budget:fee*(size⁻¹*C) ≤ |fee|:=by
    exact (mul_le_mul_of_nonneg_right (le_abs_self fee) (mul_nonneg (inv_nonneg.mpr sp.le) cp)).trans
      (by simpa using mul_le_mul_of_nonneg_left cap (abs_nonneg fee))
  have halo:|fee| ≤ shrink*Willow.haloSlack B.B:=by
    apply (div_le_iff₀ hp).mp
    exact le_add_of_nonneg_left (zero_le_one.trans (le_max_left ..))
  refine ⟨scene.positive,rp,b0.trans (inv_le_one_of_one_le₀ rp),b0.trans
    (inv_anti₀ op ((le_max_right 1 Ω).trans (le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hp.le)))),
    rr,?_,?_,?_⟩
  · simpa only [fee,WilsonOriginalThreeCompactWallet.fee,mul_assoc] using hard
  · rw [←div_eq_inv_mul]
    exact (div_le_iff₀ r0).mpr ((budget.trans halo).trans_eq (mul_comm ..))
  · intro v
    change ((base v/size)/shrink)⁻¹=_
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring

end YM.Integration.WilsonOriginalFreshRosterWallet
end
