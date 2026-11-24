import YM.Integration.WilsonIndependentFittedExteriorRuler
import YM.Integration.WilsonOriginalPublicPlantedStableCredit

/-! The available coarse part of the purchased period admits every fixed
polynomial aperture in the exact reporting mesh. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonIndependentFittedExteriorRoom
open Filter Lattice RG XSpace RegulatorIR RegulatorIR.Ledger
open WilsonCoeffUV
open WilsonIndependentEvenPassport (old)
open WilsonIndependentExactPlate (Requests)
open private tape from YM.Integration.WilsonOriginalPublicPlantedStableCredit
open private speed scale from YM.Integration.WilsonOriginalPublicPlantedPeriod
open scoped Topology Classical

theorem room (V:XSpace.Run)(a:ℕ)(ha:0<a)(κ:ℝ):
    ∀ᶠ i:ℕ in atTop,∀(S:Schedule)(s:ℕ),
      (V.step i).spacing^(-κ) ≤ S.a s/S.a (s+old V a i):=by
  let K:=⌈κ*Real.log V.ratio/Real.log 3⌉₊
  have three:0<Real.log 3:=Real.log_pos (by norm_num)
  have rate:κ*Real.log V.ratio ≤ (K:ℝ)*Real.log 3:= (div_le_iff₀ three).1 (Nat.le_ceil _)
  filter_upwards [eventually_ge_atTop (K*a)] with i late S s
  have enough:K*i ≤ old V a i:=by
    apply (Nat.le_div_iff_mul_le ha).2
    calc K*i*a=(K*a)*i:=by ring
         _ ≤ i*i:=Nat.mul_le_mul_right i late
         _ ≤ V.reserve*i*i:=Nat.mul_le_mul_right i (Nat.le_mul_of_pos_left _ V.spare)
  have budget:=mul_le_mul_of_nonneg_right (show (K:ℝ)*(i:ℝ) ≤ (old V a i:ℝ) by exact_mod_cast enough) three.le
  have dollar:=mul_le_mul_of_nonneg_left rate (Nat.cast_nonneg i)
  have available:=tape S s (old V a i)
  calc (V.step i).spacing^(-κ) = Real.exp ((i:ℝ)*(κ*Real.log V.ratio)):=by
          rw [Real.rpow_def_of_pos (V.step i).positive,scale]
          unfold speed
          congr 1
          ring
       _ ≤ Real.exp (S.scale (s+old V a i)-S.scale s):=Real.exp_le_exp.mpr (by nlinarith only [budget,dollar,available])
       _ = S.a s/S.a (s+old V a i):=by
           rw [←Real.exp_log (div_pos (S.a_pos s) (S.a_pos (s+old V a i)))]
           congr 1
           unfold Schedule.scale
           rw [Real.log_div (S.a_pos _).ne' (S.a_pos _).ne',Real.log_inv,Real.log_inv]
           ring

theorem original {G:Gauge}(V:XSpace.Run)(a j:ℕ)(ha:0<a)(hj:4 ≤ j)(κ:ℝ):
    ∀ᶠ n:ℕ in atTop,∀(i:Requests a),i.val=n → ∀(A:Levels G)(s:ℕ),
      (∀f:Flap (WilsonIndependentExactPlate.M V a),f.volW=i→
        (A.clock.op (s+(WilsonIndependentExactPlate.M V a i-(f.offset+1))) 0).patch=
          (WilsonIndependentExactPlate.S V a ha j hj).pactP f) →
      ∀reach,1 ≤ reach → reach ≤ (V.step i.val).spacing^(-κ) →
      let m:=s+old V a i.val
      ∃t,s ≤ t ∧ t ≤ m ∧ 1 ≤ reach/(A.S.a t/A.S.a m) ∧ reach/(A.S.a t/A.S.a m) ≤ (V.ratio:ℝ)^(2*a):=by
  filter_upwards [room V a ha κ] with n paid i same A s ops reach near upper m
  apply WilsonIndependentFittedExteriorRuler.original V a j ha hj i A s m (Nat.le_add_right ..) _ ops reach near
  · apply upper.trans
    simpa only [m,same] using paid A.S s
  · change s+old V a i.val ≤ s+(old V a i.val+_)
    omega

end YM.Integration.WilsonIndependentFittedExteriorRoom
