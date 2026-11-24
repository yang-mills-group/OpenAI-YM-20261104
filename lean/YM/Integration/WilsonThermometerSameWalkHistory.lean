import YM.Integration.WilsonThermometerSameWalkIncome
import YM.Integration.WilsonThermometerSameWalkTariff

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkHistory
open Function Filter Lattice Wilson RG Source Labels Trace.Physical Trace.Physical.Germ
open Trace.Physical.GermGraph PhysicalNext Repeat Legato Graces Roost Org
open scoped Classical Topology
variable {G:Gauge} (R:Run G)
local notation "β" =>R.family.path.levels.clock.hatBeta
local notation "s" =>R.family.S.scale
local notation "L" =>GermGraph.factor R.family

abbrev fee := WilsonThermometerSameWalkIncome.fee R

private theorem factors : Tendsto L atTop atTop:=by
  refine tendsto_atTop.mpr fun a=>?_
  let v:=max 1 a
  have hv:0<v:=zero_lt_one.trans_le (le_max_left _ _)
  filter_upwards [factor_large R.family v⁻¹ (inv_pos.mpr hv)] with i h
  have lower:v  ≤  L i:=by simpa only [inv_inv] using h.1
  exact (le_max_right 1 a).trans lower

private theorem positive (i:ℕ) :0<β i:=by
  exact zero_lt_one.trans (R.family.path.levels.fits.delayed i)

theorem clocks (simple:G.Simple) (b:ℕ) {ε:ℝ} (small:ε < 1/8):
    ∀ᶠ i:ℕ in atTop, ∀ k (M:ℝ), 0  ≤  M  → 
      L i^(-(1/8:ℝ))*fee R k b ε M (i+1)  ≤  (1/2)*fee R k b ε M i:=by
  have low:=((tendsto_rpow_atTop (sub_pos.mpr small)).comp (factors R)).eventually_ge_atTop (2*(2:ℝ)^b)
  filter_upwards [low,(tendsto_add_atTop_nat 1).eventually (RG01.Physical.nextHat simple R.family.path.levels)]
    with i ample adj k M hM
  have hL:0<L i:=zero_lt_one.trans (factor_positive R.family i)
  change 2*(2:ℝ)^b  ≤  L i^(1/8-ε) at ample
  have narrow:L i^(-(1/8:ℝ))*L i^ε*(2:ℝ)^b   ≤   1/2:=by
    rw [←Real.rpow_add hL,show -(1/8:ℝ)+ε= -(1/8-ε) by ring,Real.rpow_neg hL.le,
      inv_mul_eq_div,div_le_iff₀ (Real.rpow_pos_of_pos hL _)]
    linarith
  have ba:β ((i+1)+1)^b  ≤  (2:ℝ)^b*(β (i+1))^b:=by
    rw [←mul_pow];exact pow_le_pow_left₀ (positive R _).le adj _
  have march:Real.exp (ε*(s (i+1)-s k))=L i^ε*Real.exp (ε*(s i-s k)):=by
    rw [Real.rpow_def_of_pos hL,←Real.exp_add,R.family.S.scale_succ]
    congr 1;ring
  unfold fee WilsonThermometerSameWalkIncome.fee
  rw [march]
  calc
    _   ≤   L i^(-(1/8:ℝ))*((2^b*β (i+1)^b)*(L i^ε*Real.exp (ε*(s i-s k))*M)) := by
      gcongr
    _ = (L i^(-(1/8:ℝ))*L i^ε*2^b)*(β (i+1)^b*(Real.exp (ε*(s i-s k))*M)):=by ring
    _   ≤   _ :=mul_le_mul_of_nonneg_right narrow (by have:=positive R (i+1); positivity)

theorem original (simple:G.Simple) (shop:RG05Preconstruction.ReadoutPurchase R.b) (rank:ℕ)
    (menu:WilsonMeasuredRankedMenu.Menu R rank) {ε:ℝ} (small:ε < 1/8):
    let b:=rank+3
    let A:ℝ:=4^(rank+1)*(4*menu.cost+1)*menu.cost
    ∀ᶠ base:ℕ in atTop, ∀ (N:ℕ) (mass:ℝ),0 ≤ mass → ∀ (rent term:ℕ→ℝ),
      rent N ≤ 2*A*fee R base b ε mass N →
      (∀i,base  ≤  i → i < N → term (i+1) ≤ Real.exp (ε*(s (i+1)-s base))*mass) →
      (∀i,base  ≤  i → i < N → rent i ≤ L i^(-(1/8:ℝ))*rent (i+1)+WilsonThermometerSameWalkTariff.charge R rank menu i*term (i+1)) →
      ∀i,base  ≤  i → i  ≤  N → rent i ≤ 2*A*fee R base b ε mass i:=by
  intro b A
  obtain ⟨f,gate⟩:=eventually_atTop.mp (clocks R simple b small)
  filter_upwards [eventually_ge_atTop f] with base hf N mass hm rent term top source step i hi endi
  have Apos:0 ≤ A:=by dsimp [A];have:=menu.positive;positivity
  revert hi
  induction endi using Nat.decreasingInduction with
  | self=>intro _;exact top
  | of_succ j live later=>
   intro valid
   have Lp:0<L j:=zero_lt_one.trans (GermGraph.factor_positive R.family j)
   have net:=gate j (hf.trans valid) base mass hm
   have c0:0 ≤ WilsonThermometerSameWalkTariff.charge R rank menu j:=by
     unfold WilsonThermometerSameWalkTariff.charge
     have:=menu.positive;have:=positive R j;have:=positive R (j+1);positivity
   have cost:=WilsonThermometerSameWalkTariff.calendar R rank simple shop menu (show ε ≤ 1 by linarith only [small]) j
   have clock:Real.exp (ε*(s (j+1)-s base))=L j^ε*Real.exp (ε*(s j-s base)):=by
     rw [Real.rpow_def_of_pos Lp,←Real.exp_add,R.family.S.scale_succ]
     congr 1;ring
   have src:=source j valid live;rw [clock] at src
   have born:WilsonThermometerSameWalkTariff.charge R rank menu j*term (j+1) ≤ A*fee R base b ε mass j:=by
     calc _  ≤  WilsonThermometerSameWalkTariff.charge R rank menu j*(L j^ε*Real.exp (ε*(s j-s base))*mass):=mul_le_mul_of_nonneg_left src c0
         _ = (WilsonThermometerSameWalkTariff.charge R rank menu j*L j^ε)*(Real.exp (ε*(s j-s base))*mass):=by ring
         _  ≤  _ :=(mul_le_mul_of_nonneg_right cost (mul_nonneg (Real.exp_pos _).le hm)).trans_eq (by dsimp [A,b,fee,WilsonThermometerSameWalkIncome.fee];ring)
   have old:L j^(-(1/8:ℝ))*rent (j+1) ≤ A*fee R base b ε mass j:=by
     calc _  ≤  L j^(-(1/8:ℝ))*(2*A*fee R base b ε mass (j+1)):=
              mul_le_mul_of_nonneg_left (later (valid.trans j.le_succ)) (Real.rpow_nonneg Lp.le _)
         _ = 2*A*(L j^(-(1/8:ℝ))*fee R base b ε mass (j+1)):=by ring
         _  ≤  _ :=(mul_le_mul_of_nonneg_left net (by positivity : 0 ≤ 2*A)).trans_eq (by ring)
   linarith only [step j valid live,born,old]

end YM.Integration.WilsonThermometerSameWalkHistory
end
