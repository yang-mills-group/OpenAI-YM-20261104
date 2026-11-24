import YM.Integration.WilsonThermometerSameWalkGerm
import YM.RG01.Slack
import YM.Trace.Physicalv2.GermPrices

/-! Gross one-source income on the fixed physical calendar. The upper cutoff
occurs only in the top bill. A positive charged child can make the gross
income large even though its transverse remainder contracts at every date. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkIncome
open Function Filter Lattice Wilson RG Source Labels Trace.Physical Trace.Physical.Germ
open Trace.Physical.GermGraph PhysicalNext Repeat Legato Graces Roost Org
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "β" =>R.family.path.levels.clock.hatBeta
local notation "s" =>R.family.S.scale
local notation "L" =>GermGraph.factor R.family

def fee (k b:ℕ) (ε M:ℝ) (i:ℕ):ℝ:=β (i+1)^b*(Real.exp (ε*(s i-s k))*M)

private theorem factors : Tendsto L atTop atTop:=by
  refine tendsto_atTop.mpr fun a=>?_
  let v:=max 1 a
  have hv:0<v:=zero_lt_one.trans_le (le_max_left _ _)
  filter_upwards [factor_large R.family v⁻¹ (inv_pos.mpr hv)] with i h
  have lower:v ≤ L i:=by simpa only [inv_inv] using h.1
  exact (le_max_right 1 a).trans lower

private theorem positive (i:ℕ) :0<β i:=by
  exact zero_lt_one.trans (R.family.path.levels.fits.delayed i)

theorem clocks (simple:G.Simple) (b:ℕ) {ε:ℝ} (small:ε<1/4):
    ∀ᶠ i:ℕ in atTop, ∀ k (M:ℝ), 0 ≤ M  → 
      L i^(-(1/4:ℝ))*fee R k b ε M (i+1) ≤ (1/2)*fee R k b ε M i:=by
  have low:=((tendsto_rpow_atTop (sub_pos.mpr small)).comp (factors R)).eventually_ge_atTop (2*(2:ℝ)^b)
  filter_upwards [low,(tendsto_add_atTop_nat 1).eventually (RG01.Physical.nextHat simple R.family.path.levels)]
    with i ample adj k M hM
  have hL:0<L i:=zero_lt_one.trans (factor_positive R.family i)
  change 2*(2:ℝ)^b ≤ L i^(1/4-ε) at ample
  have narrow:L i^(-(1/4:ℝ))*L i^ε*(2:ℝ)^b  ≤  1/2:=by
    rw [←Real.rpow_add hL,show -(1/4:ℝ)+ε= -(1/4-ε) by ring,Real.rpow_neg hL.le,
      inv_mul_eq_div,div_le_iff₀ (Real.rpow_pos_of_pos hL _)]
    linarith
  have ba:β ((i+1)+1)^b ≤ (2:ℝ)^b*(β (i+1))^b:=by
    rw [←mul_pow];exact pow_le_pow_left₀ (positive R _).le adj _
  have march:Real.exp (ε*(s (i+1)-s k))=L i^ε*Real.exp (ε*(s i-s k)):=by
    rw [Real.rpow_def_of_pos hL,←Real.exp_add,R.family.S.scale_succ]
    congr 1;ring
  unfold fee
  rw [march]
  calc
    _  ≤  L i^(-(1/4:ℝ))*((2^b*β (i+1)^b)*(L i^ε*Real.exp (ε*(s i-s k))*M)) := by
      gcongr
    _ = (L i^(-(1/4:ℝ))*L i^ε*2^b)*(β (i+1)^b*(Real.exp (ε*(s i-s k))*M)):=by ring
    _  ≤  _ :=mul_le_mul_of_nonneg_right narrow (by have:=positive R (i+1); positivity)

private theorem forecast (i : ℕ) :
    β i  ≤  (|R.family.path.levels.clock.bar|+|G.slopeConstant|+1)*Real.exp (s i) ∧
    L i  ≤  Real.exp (s (i+1)) := by
  let S:=R.family.S
  have nonneg (j : ℕ) : 0 ≤ S.scale j := by
    have h := (OPE.scale_mono S).monotone (Nat.zero_le j)
    simpa only [Schedule.scale_zero] using h
  have one := Real.one_le_exp (nonneg i)
  have ss : S.scale i  ≤  Real.exp (S.scale i) := by linarith only [Real.add_one_le_exp (S.scale i)]
  constructor
  · change R.family.path.levels.clock.bar + G.slopeConstant*S.scale i  ≤  _
    have base := le_mul_of_one_le_right (abs_nonneg R.family.path.levels.clock.bar) one
    have hb := (mul_le_mul_of_nonneg_right (le_abs_self G.slopeConstant) (nonneg i)).trans
      (mul_le_mul_of_nonneg_left ss (abs_nonneg G.slopeConstant))
    have hc := le_abs_self R.family.path.levels.clock.bar
    linarith only [base,hb,hc,one]
  · change ((S.block i).val:ℝ)  ≤  Real.exp (S.scale (i+1))
    rw [S.scale_succ,Real.exp_add,Real.exp_log (Nat.cast_pos.mpr (S.block i).pos)]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) one


theorem wrap (simple:G.Simple) (b:ℕ) (W:ℝ) (hW:0 ≤ W):
    ∀ᶠ i:ℕ in atTop, ∀ per, W*β (i+1)^b*wraps (R.family.path.levels.budget (i+1))
      (R.family.side (i+1) per)  ≤  (1/2)*L i^(-(1/4:ℝ)):=by
  let H:=|R.family.path.levels.clock.bar|+|G.slopeConstant|+1
  have hH:0<H:=by dsimp [H];positivity
  let δ:ℝ:= -((b:ℝ)+2)
  have late:= (Real.tendsto_exp_atTop.comp R.family.S.divergent).eventually_ge_atTop (2*(W*H^b))
  filter_upwards [(tendsto_add_atTop_nat 1).eventually late,
    (tendsto_add_atTop_nat 1).eventually (GermGraph.cut_flat R.family simple δ)] with i enough tail per
  change 2*(W*H^b) ≤ Real.exp (s (i+1)) at enough
  have hL:1<L i:=factor_positive R.family i
  have hp:=forecast R (i+1)
  have band:β (i+1)^b ≤ H^b*Real.exp ((b:ℝ)*s (i+1)):=by
    rw [Real.exp_nat_mul,←mul_pow]
    exact pow_le_pow_left₀ (positive R _).le hp.1 b
  have block:L i^(1/4:ℝ) ≤ Real.exp (s (i+1)):=by
    exact (Real.rpow_le_self_of_one_le hL.le (by norm_num)).trans (forecast R i).2
  have cut:wraps (R.family.path.levels.budget (i+1)) (R.family.side (i+1) per) ≤ Real.exp (δ*s (i+1)):=tail per
  have joint:W*β (i+1)^b*wraps (R.family.path.levels.budget (i+1)) (R.family.side (i+1) per)*L i^(1/4:ℝ) ≤ 1/2:=by
    calc
      _  ≤  W*(H^b*Real.exp ((b:ℝ)*s (i+1)))*Real.exp (δ*s (i+1))*Real.exp (s (i+1)) := by
        have wpos:0 ≤ wraps (R.family.path.levels.budget (i+1)) (R.family.side (i+1) per):=(Real.exp_pos _).le
        have bp:=positive R (i+1);gcongr
      _ = W*H^b*Real.exp (-s (i+1)) := by
        rw [show W*(H^b*Real.exp ((b:ℝ)*s (i+1)))*Real.exp (δ*s (i+1))*Real.exp (s (i+1))=
          W*H^b*(Real.exp ((b:ℝ)*s (i+1))*Real.exp (δ*s (i+1))*Real.exp (s (i+1))) from by ring,
          ←Real.exp_add,←Real.exp_add];dsimp [δ];ring_nf
      _  ≤  _ :=by rw [Real.exp_neg,←div_eq_mul_inv,div_le_iff₀ (Real.exp_pos _)];linarith
  rw [Real.rpow_neg (zero_lt_one.trans hL).le,←div_eq_mul_inv,le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans hL) _)]
  exact joint

theorem bounded {k N b per:ℕ} {ε M W:ℝ} 
    {X:Type*} [NormedAddCommGroup X] (p c:ℕ → X) (r A:ℕ → ℝ)
    (nonneg:∀i,k  ≤  i → i  ≤  N → 0 ≤ r i) (cost:∀i,k  ≤  i → i<N → 0 ≤ A i)
    (top:r N  ≤  2*fee R k b ε M N)
    (bill:∀i,k  ≤  i → i<N → r i ≤ L i^(-(2/5:ℝ))*r (i+1)+A i*‖c (i+1)‖)
    (probe:∀i,k  ≤  i → i<N → ‖c (i+1)-p (i+1)‖ ≤ W*wraps (R.family.path.levels.budget (i+1))
      (R.family.side (i+1) per)*r (i+1))
    (leaf:∀i,k  ≤  i → i<N → A i*‖p (i+1)‖  ≤  fee R k b ε M i)
    (wind:∀i,k  ≤  i → i<N → A i*W*wraps (R.family.path.levels.budget (i+1))
      (R.family.side (i+1) per) ≤ (1/2)*L i^(-(1/4:ℝ)))
    (shrink:∀i,k  ≤  i → i<N → L i^(-(2/5:ℝ)) ≤ (1/2)*L i^(-(1/4:ℝ)))
    (clock:∀i,k  ≤  i → i<N → L i^(-(1/4:ℝ))*fee R k b ε M (i+1) ≤ (1/2)*fee R k b ε M i) :
    ∀ i,k  ≤  i → i  ≤  N → r i ≤ 2*fee R k b ε M i:=by
  intro i low hi
  revert low
  induction hi using Nat.decreasingInduction with
  | self=>intro _;exact top
  | of_succ i hi ih=>
    intro low
    have after:=ih (Nat.le_succ_of_le low)
    have h1:‖c (i+1)‖ ≤ W*wraps (R.family.path.levels.budget (i+1)) (R.family.side (i+1) per)*r (i+1)+‖p (i+1)‖:=
      (calc ‖c (i+1)‖=‖(c (i+1)-p (i+1))+p (i+1)‖:=by rw [sub_add_cancel]
            _  ≤  ‖c (i+1)-p (i+1)‖+‖p (i+1)‖:=norm_add_le _ _).trans
        (add_le_add (probe i low hi) le_rfl)
    have h2:=mul_le_mul_of_nonneg_left h1 (cost i low hi)
    have h3:=mul_le_mul_of_nonneg_right (add_le_add (shrink i low hi) (wind i low hi))
      (nonneg _ (by omega) hi)
    have h4:=mul_le_mul_of_nonneg_left after (Real.rpow_nonneg (zero_lt_one.trans (factor_positive R.family i)).le (-(1/4:ℝ)))
    have h5:=clock i low hi
    nlinarith only [bill i low hi,h2,h3,h4,h5,leaf i low hi]

end YM.Integration.WilsonThermometerSameWalkIncome
end
