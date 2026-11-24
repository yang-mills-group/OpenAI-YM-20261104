import YM.Integration.WilsonEmittedDictionary
import YM.Integration.WilsonEmittedOriginalRoom
import YM.WilsonCoeffUV.Emit.ReportingClocks

/-! The moving derivative order and every selected school fare consume a single subpower on the original date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonEmittedStageFinance
open Finset Filter RG Wilson Lattice RG.Supply PhysicalNext PhysicalNext.Repeat.Legato
open WilsonLimitConstruction FundedDictionaryPatchPrices WilsonEmittedDictionary
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Physical WilsonCoeffUV.Bank.Mosaic
open Comparison.Density Comparison.Density.Transport
open scoped Classical BigOperators
variable {G:Gauge} (tube:LinkTube G)

def orderBill (X:Patch) (B:Stage) (k:ℕ) :=
  13+max B.order k * capacity X k + 2*B.power*B.order

theorem parts (X:Patch) (K:KernelChoices) (B:Stage) (k:ℕ) :
    1≤program tube X K B k ∧ |groupPrice tube B.order|≤program tube X K B k ∧
    (4:ℝ)^(B.power*B.order)≤program tube X K B k ∧
    (orderBill X B k:ℝ)≤program tube X K B k ∧
    ((X.L.val:ℝ)+1)^k≤program tube X K B k ∧ (2:ℝ)^(capacity X k)≤program tube X K B k := by
  set n:=max B.order k
  let U:=roster (G:=G) (capacity X k) n
  have hU:0≤U:=by
    unfold U roster
    exact sum_nonneg fun _ _=>sum_nonneg fun _ _=>sum_nonneg fun _ _=>abs_nonneg _
  have hW:0≤|groupPrice tube B.order|:=abs_nonneg _
  have hF:0≤(4:ℝ)^(B.power*B.order):=by positivity
  have hJ:0≤(orderBill X B k:ℝ):=by positivity
  have hL:0≤((X.L.val:ℝ)+1)^k:=by positivity
  have hE:0≤(2:ℝ)^(capacity X k):=by positivity
  let P:=1+U+|groupPrice tube B.order|+(4:ℝ)^(B.power*B.order)+(orderBill X B k:ℝ)+
    ((X.L.val:ℝ)+1)^k+(2:ℝ)^(capacity X k)
  change 1≤P ∧ _≤P ∧ _≤P ∧ _≤P ∧ _≤P ∧ _≤P
  dsimp only [P];exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

private theorem bill {x z C:ℝ} {e:ℕ} (phase:1≤Real.log x) (hz:z=1+Real.log (Real.log x))
    (pos:1≤C) (price:C≤z) (degree:(e:ℝ)≤z) :
    C^3*(1+Real.log x)^e ≤ Real.exp (4*z^2) := by
  have h : 1≤z:=pos.trans price
  have y:1+Real.log x≤Real.exp z:=by
    rw [hz,Real.exp_add,Real.exp_log (zero_lt_one.trans_le phase)]
    have o:2≤Real.exp 1:=by linarith [Real.add_one_le_exp (1:ℝ)]
    have w:=mul_le_mul_of_nonneg_right o (zero_le_one.trans phase)
    linarith
  have c:C≤Real.exp z:=by linarith [Real.add_one_le_exp z]
  have p:=mul_le_mul (pow_le_pow_left₀ (zero_le_one.trans pos) c 3)
    (pow_le_pow_left₀ (by linarith :0≤1+Real.log x) y e)
    (pow_nonneg (by linarith) _) (pow_nonneg (Real.exp_pos _).le _)
  apply p.trans
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hz2:=mul_le_mul_of_nonneg_right degree (zero_le_one.trans h)
  have hzz:=mul_nonneg (sub_nonneg.mpr h) (zero_le_one.trans h)
  norm_num at *
  nlinarith only [hz2,hzz]

theorem funded (R:Run G) (simple:G.Simple) (bought:Covered (program tube) R) (k:ℕ) {η:ℝ} (pη:0<η) :
    let A:=R.family.path.levels
    ∀ᶠ m:ℕ in atTop,∀ per,∀β:ℝ,A.clock.hatBeta (m+1)/2≤β →
      let X:=(A.clock.op m per).patch
      let B:=A.params (m+1)
      (program tube X A.clock.kernel B k)^3*
          (1+Real.log (A.clock.hatBeta (m+1)))^(orderBill X B k) ≤
        ((Real.sqrt β)⁻¹)^(-η) := by
  let A:=R.family.path.levels
  let coin:Credit:=⟨2,4,by norm_num⟩
  have fast:=exp_at_band coin A simple η pη
  have rise:Tendsto (fun i=>Real.log (A.clock.hatBeta i)) atTop atTop:=YM.Multi.Wage.log_tend simple A
  have next:=tendsto_add_atTop_nat 1
  dsimp only
  filter_upwards [bought k,next.eventually fast,next.eventually (rise.eventually_ge_atTop 1)] with m hq paid warm
  intro per β band
  let X:=(A.clock.op m per).patch
  let B:=A.params (m+1)
  have P:=parts tube X A.clock.kernel B k
  have priced:program tube X A.clock.kernel B k≤zz A m:=(le_abs_self _).trans (hq per).1
  have move:zz A m≤zz A (m+1):=by
    unfold zz
    gcongr
    · exact Real.log_pos (A.fits.delayed _)
    · exact zero_lt_one.trans (A.fits.delayed _)
    · exact WilsonCoeffUV.Layout.betaR A simple (Nat.le_succ _)
  exact (bill warm rfl P.1 (priced.trans move) (P.2.2.2.1.trans (priced.trans move))).trans (paid β band)

end YM.Integration.WilsonEmittedStageFinance
end
