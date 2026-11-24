import YM.Integration.WilsonReceivedWholeFieldMask
import YM.Corona.Fit

/-! A failed regular lamp is charged at one of its own registered roots.
Remote compatible ordinary factors never enter this geometric price. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedMask
open Function Finset Filter MeasureTheory Lattice Wilson RG Ac Marker QuadraticLocal
open IterationFour PhysicalNext.Repeat.Legato Push.AbsoluteSums
open Push.AbsoluteSums.Animals OPE.Therm WilsonRootedKioskOccupiedSlip
open scoped Classical BigOperators Topology
variable {G:Gauge}{n:Side}{p:BudgetPoint}{V I T:Type}[DecidableEq V]
  {Γ:Census V}{o:V→Site n}(L:Lamps T I G p o Γ){w:V→ℝ}{a D:ℝ}(hw:∀v,0<w v)
  (ha:0≤a)(gross:Gross L w p.B a D)

def reach (B k:ℕ):ℕ:=k*(4*B+2)+2*B

include gross hw ha in
theorem original (k:ℕ)(t:T)(U:Config G n)(s:Γ.Mode)(v:V)(hv:v∈s.val)
    (clear:Healthy p.threshold (halo (reach p.B k) {o v}) U):
    (Real.exp (a*k)*Poly.toll w s)*‖(L.log t U).part s-(bare L t U).part s‖≤D:=by
  obtain ⟨f,pos,values,hit⟩:=gross.before
  let rate:=Real.exp (a*k)*Poly.toll w s
  let z (j:I):ℂ:=(rate:ℂ)*(Poly.send (L.mode j) (gap L t j U)).part s
  have wallet:=hit (o v)
  have rp:0≤rate:=mul_nonneg (Real.exp_nonneg _) (Poly.worth hw s).le
  have row (j:I):‖z j‖ ≤ if o v∈L.ground j then
      Poly.toll w (L.mode j)*f j*Real.exp (a*coverNumber p.B (L.ground j)) else 0:=by
    by_cases hm:s=L.mode j
    · have root:o v∈L.ground j:=L.roots j v (hm ▸ hv)
      rw [if_pos root,←hm]
      simp only [z,Poly.part_send,if_pos hm,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg rp]
      by_cases hs:coverNumber p.B (L.ground j)≤k
      · have sub:L.ground j⊆halo (reach p.B k) {o v}:=by
          intro y hy
          apply halo_spec.mpr
          refine ⟨o v,by simp,?_⟩
          exact (Corona.extent _ p.B root hy).trans
            (Nat.add_le_add_right (Nat.mul_le_mul_right _ hs) _)
        have good:Healthy p.threshold (L.ground j) U:=clear.mono_left sub
        rw [healthy L t j U good,norm_zero,mul_zero]
        exact mul_nonneg (mul_nonneg (Poly.worth hw s).le (pos j)) (Real.exp_nonneg _)
      · have bigger:Real.exp (a*k)≤Real.exp (a*(coverNumber p.B (L.ground j):ℝ)):=by
          apply Real.exp_le_exp.mpr
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.le_of_not_ge hs)) ha
        calc _≤rate*f j:=mul_le_mul_of_nonneg_left ((WilsonRootedKioskOccupiedSlip.size L t j U).trans (values j t U)) rp
             _=Poly.toll w s*f j*Real.exp (a*k):=by dsimp only [rate];ring
             _≤_:=mul_le_mul_of_nonneg_left bigger (mul_nonneg (Poly.worth hw s).le (pos j))
    · simp only [z,Poly.part_send,if_neg hm,mul_zero,norm_zero]
      split <;> first | exact mul_nonneg (mul_nonneg (Poly.worth hw _).le (pos _)) (Real.exp_nonneg _) | rfl
  have sums:=wallet.2.1.of_nonneg_of_le (fun j=>norm_nonneg (z j)) row
  have he:(rate:ℂ)*((L.log t U).part s-(bare L t U).part s)=∑'j,z j:=by
    rw [WilsonRootedKioskCompleteFiling.split L hw ha gross]
    change (rate:ℂ)*((bare L t U).part s+((sheet L).log t U).part s-(bare L t U).part s)=_
    rw [add_sub_cancel_left]
    change (rate:ℂ)*(∑'j,(sheet L).soap t j U).part s=_
    rw [Poly.share (WilsonRootedKioskCompleteFiling.sums L hw ha gross t U).2,tsum_mul_left]
    rfl
  have estimate:=(norm_tsum_le_tsum_norm sums).trans ((sums.tsum_le_tsum row wallet.2.1).trans wallet.2.2)
  rw [←he,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg rp] at estimate
  exact estimate

end YM.Integration.WilsonOriginalSeparatedMask
end
