import YM.Integration.WilsonTrueProjectedLocatedSeed
import YM.RG01.Slack

/-! Erasure of the actual one-date ultraviolet seed tariff at fixed landing,
uniformly over the side and the submitted null accounts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonTrueProjectedLocatedSeedTail
open Filter RG Wilson PhysicalNext.Repeat.Legato WilsonOriginalNullCorridor
open scoped Topology
variable {G:Gauge} (R:Run G)
local notation "A₀" => R.family.path.levels
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "s" => R.family.S.scale

theorem original (simple:G.Simple) (b power:ℕ) {C δ tol:ℝ}
    (cap:0≤C) (stable:δ<1/8) (positive:0<tol) :
    ∀ᶠ N:ℕ in atTop, ∀ B D:ℝ,
      B+D≤C*(1+H (N+1))^power*Real.exp (δ*(s N-s b)) →
      gain R.family b N*(B+D)≤tol := by
  have slope:=Gauge.slopeConstant_pos simple
  let e:ℝ:=(1/8-δ)/G.slopeConstant
  have ep:0<e:=div_pos (sub_pos.mpr stable) slope
  let t (N:ℕ):=e*(1+H N)
  have climb:Tendsto H atTop atTop:=tendsto_atTop_add_const_left _ _
    (R.family.S.divergent.const_mul_atTop slope)
  have ht:Tendsto t atTop atTop:=(tendsto_atTop_add_const_left _ (1:ℝ) climb).const_mul_atTop ep
  let K:=C*(2/e)^power*Real.exp (t b)
  have tail:=((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero power).comp ht).const_mul K
  simp only [mul_zero] at tail
  filter_upwards [tail.eventually_le_const positive,RG01.Physical.nextHat simple A₀,
    climb.eventually_ge_atTop 1] with N small adj funded
  intro B D stock
  have powerFee:(1+H (N+1))^power≤(2*(1+H N))^power:=
    pow_le_pow_left₀ (by have h:1≤H (N+1):=((A₀).fits.delayed (N+1)).le;linarith) (by linarith only [adj]) _
  have align:-(1/8:ℝ)*(s N-s b)+δ*(s N-s b)=t b-t N:=by
    change _=e*(1+((A₀).clock.bar+G.slopeConstant*s b))-e*(1+((A₀).clock.bar+G.slopeConstant*s N))
    dsimp only [e];field_simp [slope.ne'];ring
  have temps:gain R.family b N*Real.exp (δ*(s N-s b))=Real.exp (t b)*Real.exp (-(t N)):=by
    rw [gain,←Real.exp_add,align,sub_eq_add_neg,Real.exp_add]
  have units:(2*(1+H N))^power=(2/e)^power*(t N)^power:=by
    rw [←mul_pow];congr 1;dsimp only [t];field_simp [ep.ne']
  calc
    _ ≤ gain R.family b N*(C*(2*(1+H N))^power*Real.exp (δ*(s N-s b))) :=
      mul_le_mul_of_nonneg_left (stock.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left powerFee cap) (Real.exp_pos _).le)) (Real.exp_pos _).le
    _ = C*(2*(1+H N))^power*(gain R.family b N*Real.exp (δ*(s N-s b))) := by ring
    _ = K*((t N)^power*Real.exp (-(t N))) := by rw [units,temps];dsimp only [K];ring
    _ ≤ tol := small

end YM.Integration.WilsonTrueProjectedLocatedSeedTail
