import YM.Integration.WilsonIndependentConditionedActualCredit
import YM.Integration.WilsonThermometerMixedThermal

/-! Clock prices relative to a genuine earlier home and the same optical cutoff. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedEarlierCredit
open Filter Real Function Lattice Wilson RG RG.Supply Precision PhysicalNext.Repeat.Legato
open Next.Rank WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Patrol Extra.Histories
open WilsonIndependentConditionedBankFittedFees (age)
open WilsonIndependentConditionedActualCredit (badge gramAge homes)
open WilsonInvariantActionPosition (berth)
open scoped Topology Classical
variable {G:Gauge}(R:Run G)
local notation "A" => R.family.path.levels
local notation "β" => R.family.path.levels.clock.hatBeta

def drift (T U:ℕ):Credit:=
  ⟨1,2+|zz A 0|+(T+U+1)*(2+(log 3)⁻¹),by
    have lp:0<log (3:ℝ):=log_pos (by norm_num)
    have nn:0≤((T:ℝ)+(U:ℝ)+1)*(2+(log 3)⁻¹):=by positivity
    linarith [abs_nonneg (zz A 0)]⟩

theorem original (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit)(T U:ℕ):
    ∀ᶠ f:ℕ in atTop,∀m:ℕ,m≤f → R.family.S.a m/R.family.S.a f≤(β f)^U →
      let K:=berth R T f
      let Z:=(drift R T U).buy (badge R f)
      1≤badge R f ∧ |age R m m|≤Z ∧ |age R m K|≤Z ∧ |gramAge R m K|≤Z:=by
  have leads:=Station.hat_rate A simple
  filter_upwards [WilsonAddressedCollarWindow.original R simple slow T (η:=1) zero_lt_one,
    (tendsto_log_atTop.comp leads).eventually_ge_atTop 1] with f edge warm
  intro m mf reach
  let K:=berth R T f
  let gap:=(A).S.scale K-(A).S.scale m
  have order:m≤K:=mf.trans edge.1.le
  have hb(i:ℕ):0<β i:=zero_lt_one.trans ((A).fits.delayed i)
  have lb(i:ℕ):0<badge R i:=log_pos ((A).fits.delayed i)
  have mono:Monotone (badge R):=fun i j ij=>log_le_log (hb i)
    (WilsonStartup.Timing.hat_mono A (Gauge.slopeConstant_pos simple).le ij)
  have hm:zz A 0 ≤ zz A m:=add_le_add le_rfl (log_le_log (lb 0) (mono (Nat.zero_le m)))
  have hf:zz A m ≤ 2*badge R f:=by
    change 1+log (badge R m) ≤ _
    linarith only [log_le_self (lb m).le,mono mf,show 1≤badge R f from warm]
  have hpos:0≤badge R f:=(lb f).le
  have fee:|zz A m| ≤ (2+|zz A 0|)*badge R f:=by
    have a:|zz A 0| ≤ |zz A 0| *badge R f:=le_mul_of_one_le_right (abs_nonneg _) warm
    have b:=neg_abs_le (zz A 0)
    rw [abs_le,add_mul]
    constructor <;> linarith only [a,b,hm,hf,abs_nonneg (zz A 0),hpos]
  have delta:gap≤((T:ℝ)+U+1)*badge R f:=by
    have v:=log_le_log (div_pos (R.family.S.a_pos f) (R.family.S.a_pos K)) edge.2.2
    have w:=log_le_log (div_pos (R.family.S.a_pos m) (R.family.S.a_pos f)) reach
    rw [rpow_one,log_mul (pow_pos (hb f) T).ne' (hb f).ne',log_pow] at v
    rw [log_pow] at w
    rw [log_div (R.family.S.a_pos f).ne' (R.family.S.a_pos K).ne'] at v
    rw [log_div (R.family.S.a_pos m).ne' (R.family.S.a_pos f).ne'] at w
    change R.family.S.scale K-R.family.S.scale m ≤ _
    rw [Schedule.scale,Schedule.scale,log_inv,log_inv]
    dsimp only [badge];linarith only [v,w]
  have lp:0<log (3:ℝ):=log_pos (by norm_num)
  have capture:((K-m:ℕ):ℝ)*log 3≤gap:=by
    simpa only [show m+(K-m)=K by omega] using AuxPlates.scaleTape (A).S m (K-m)
  have gpos:0≤gap:=(mul_nonneg (Nat.cast_nonneg _) lp.le).trans capture
  have day:((K-m:ℕ):ℝ)≤(((T:ℝ)+U+1)*badge R f)*(log 3)⁻¹:=by
    simpa only [div_eq_mul_inv] using (le_div_iff₀ lp).mpr (capture.trans delta)
  have base:0≤((T:ℝ)+U+1)*badge R f:=mul_nonneg (by positivity) hpos
  have extra:0≤(((T:ℝ)+U+1)*badge R f)*(log 3)⁻¹:=mul_nonneg base (inv_nonneg.mpr lp.le)
  have roof:(drift R T U).buy (badge R f) =
      (2+|zz A 0|)*badge R f+2*(((T:ℝ)+U+1)*badge R f)+
        (((T:ℝ)+U+1)*badge R f)*(log 3)⁻¹:=by simp only [drift,Credit.buy,pow_one];ring
  dsimp only
  rw [homes,roof]
  refine ⟨warm,by linarith only [fee,base,extra],?_,?_⟩
  · change |zz A m+gap+((K-m:ℕ):ℝ)|≤_
    have bound:|zz A m+gap+((K-m:ℕ):ℝ)|≤|zz A m|+gap+((K-m:ℕ):ℝ):=by
      calc _≤|zz A m+gap|+|((K-m:ℕ):ℝ)|:=abs_add_le .. 
           _≤(|zz A m|+|gap|)+|((K-m:ℕ):ℝ)|:=add_le_add (abs_add_le ..) le_rfl
           _=_:=by rw [abs_of_nonneg gpos,abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) (K-m))]
    linarith only [bound,fee,delta,day,base]
  · change |zz A m+2*gap|≤_
    have bound:=abs_add_le (zz A m) (2*gap)
    rw [abs_of_nonneg (mul_nonneg (by norm_num:0≤(2:ℝ)) gpos)] at bound
    linarith only [bound,fee,delta,extra]

end YM.Integration.WilsonIndependentConditionedEarlierCredit
