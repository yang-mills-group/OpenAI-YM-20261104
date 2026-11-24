import YM.Integration.WilsonPositionScaleLawWhole

/-! The lower pieces of the same original physical field contract geometrically
at a half step, once the true measured transition lies on its selected branch. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPositionScaleLawContract
open Function Filter Set Finset Spec Table Extraction OPE Climb PhysMS Trace.Pilot
open Maxwell Maxwell.Free XSpace XSpace.Normalize PhysicalNext.Repeat.Legato
open FVA2 FVA2.Register FVA2.Scale
open WilsonPositionScaleLawHome (Ratio sweep)
open WilsonPositionScaleLawNative (exactOp)
open WilsonPositionScaleLawGrade (grade half)
open WilsonPositionScaleLawFixed (top)
open WilsonPositionScaleLawWhole (low fee full)
open scoped Topology Classical BigOperators
variable {G:Gauge}{R:Run G}{f:Extraction.Order}{S:Table R.family.book}(F:Final R.family f S)(J:ℝ→tower S)(Z:WilsonPrescription G)
set_option quotPrecheck false
local notation "E"=>(Bel R.family.book).Field

theorem lower {d:ℕ}(r:ℝ)(t:Ratio)(O:S.Field d):
    let y:=full F J Z d (t.val*r) O
    let x:=full F J Z d r O
    let U:=exactOp F J Z.store d (r,t)
    low R.family y ≤t.val*low R.family x+fee R.family d*‖U-ContinuousLinearMap.id ℂ (E d)‖*‖y‖:=by
  intro y x U
  let I:=ContinuousLinearMap.id ℂ (E d)
  have ht:=WilsonPositionScaleLawNative.positive t
  have share (i:Fin (d+1))(outside:i∈Finset.univ.erase (top d)):t.val^(d-i.val)≤t.val:=by
    have h : i≠top d:=Finset.ne_of_mem_erase outside
    have hlt:i.val<d:=lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt) (fun e=>h (Fin.ext e))
    obtain ⟨n,hh⟩:=Nat.exists_eq_succ_of_ne_zero (show d-i.val≠0 by omega)
    rw [hh,pow_succ];simpa using mul_le_mul_of_nonneg_right (pow_le_one₀ ht.le t.property.2) ht.le
  change low R.family y≤t.val*low R.family x+fee R.family d*‖U-I‖*‖y‖
  simp only [low,fee,Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  let P:=grade R.family i
  have eq:P y=P (U y)+P ((I-U) y):=by
    rw [_root_.sub_apply,show I y=y from rfl,P.map_sub];abel
  have point:P (U y)=(t.val:ℂ)^(d-i.val) • P x:=WilsonPositionScaleLawWhole.step F J Z r t i O
  calc
    ‖P y‖=‖P (U y)+P ((I-U) y)‖:=congrArg _ eq
    _≤‖P (U y)‖+‖P ((I-U) y)‖:=norm_add_le ..
    _≤t.val*‖P x‖+‖P‖*(‖I-U‖*‖y‖):=by
      rw [point,norm_smul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
      exact add_le_add (mul_le_mul_of_nonneg_right (share i hi) (norm_nonneg _))
        ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((I-U).le_opNorm _) (norm_nonneg _)))
    _=_:=by rw [norm_sub_rev I U,mul_assoc]

private theorem receipt {X I:Type*}[NormedAddCommGroup X][NormedSpace ℂ X]{l:Filter I}
    (U:I→X→L[ℂ]X)(K:ℝ)(near:Tendsto U l (𝓝 (ContinuousLinearMap.id ℂ X))):
    ∀ᶠz in l,K*‖U z-ContinuousLinearMap.id ℂ X‖≤1/4:=by
  have bill: Tendsto (fun z=>K*‖U z-ContinuousLinearMap.id ℂ X‖) l (𝓝 0):=by
    simpa only [mul_zero] using (tendsto_const_nhds (x:=K)).mul (tendsto_iff_norm_sub_tendsto_zero.mp near)
  exact ((tendsto_order.mp bill).2 _ (by norm_num : (0:ℝ)<1/4)).mono fun _ h=>h.le

theorem original (lead:Leading F J)(d:ℕ)(raw:WilsonPositionScaleLawBranch.Raw J d):
    ∀ᶠr in trail,∀t:Ratio,∀O:S.Field d,
    let y:=full F J Z d (t.val*r) O
    let x:=full F J Z d r O
    3*low R.family y≤4*t.val*low R.family x+‖grade R.family (top d) y‖:=by
  let I:=ContinuousLinearMap.id ℂ (E d)
  let U:=exactOp F J Z.store d
  have near:Tendsto U sweep (𝓝 I):=WilsonPositionScaleLawBranch.transferred F J Z.store lead d raw
  have paid:=receipt U (fee R.family d) near
  obtain ⟨p,hp,q,hq,all⟩:=Filter.eventually_prod_iff.mp paid
  filter_upwards [hp] with r hr t O
  dsimp only
  let y:=full F J Z d (t.val*r) O
  let x:=full F J Z d r O
  have h:=all hr (Filter.eventually_top.mp hq t)
  have actual:=lower F J Z r t O
  have k:=mul_le_mul_of_nonneg_right h (norm_nonneg y)
  have split:=WilsonPositionScaleLawWhole.split R.family y
  change low R.family y≤t.val*low R.family x+fee R.family d*‖U (r,t)-I‖*‖y‖ at actual
  change fee R.family d*‖U (r,t)-I‖*‖y‖≤(1/4)*‖y‖ at k
  change 3*low R.family y≤4*t.val*low R.family x+‖grade R.family (top d) y‖
  linarith

end YM.Integration.WilsonPositionScaleLawContract
end
